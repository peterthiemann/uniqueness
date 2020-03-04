(* with splitting*)
type ident = string

type splitting = ident list * ident list

type loc = int
type borrow = Imm | Mut

type address = Address of borrow list * loc

let loc : loc -> address =
  fun ell -> Address ([], ell)

type result = RADDR of address | RCONST of int | RVOID

type venv = VEmpty | VUpd of venv * ident * result

type alpha = int                (* type variable *)

type 'a var = V of int

type kind = KVAR of kind var
          | KLIN of int option
          | KAFF of int option
          | KUNR of int option

type kappa = kind var           (* kind variable *)
type kappas = kappa list

type constr = (kind * kind) list

type ty = TYVAR of alpha
        | TYARR of kind * ty * ty
        | TYCON of ty list * ident
        | TYBOR of borrow * ty

type schm = SCHM of kappas * (alpha * kind) list * constr * ty

type exp = Const of int
         | Var of ident
         | Varinst of ident * kind list
         | Lam of kind * ident * exp
         | App of exp * exp * splitting
         | Let of ident * exp * exp * splitting
         | LetFun of ident * schm * kind * ident * exp * exp * splitting
         | Pair of kind * exp * exp * splitting
         | Match of ident * ident * exp * exp * splitting
         | Matchborrow of ident * ident * exp * exp * splitting
         | Region of exp * int * ident * borrow
         | Borrow of borrow * ident
         | Create (* of exp *)
         | Destroy of exp
         | Observe of exp
         | Update of exp * exp * splitting
         (* anf cases *)
         | VApp of ident * ident
         | VPair of kind * ident * ident
         | VMatch of ident * ident * ident * exp * splitting
         | VMatchborrow of ident * ident * ident * exp * splitting
         | VCreate of ident
         | VDestroy of ident
         | VObserve of ident
         | VUpdate of ident * ident

type storable
  = STPOLY of venv * kappas * constr * kind * ident * exp
  | STCLOS of venv * kind * ident * exp
  | STPAIR of kind * result * result
  | STRSRC of result
  | STRELEASED

(* hashtable and next free location *)
module Store = Map.Make(Int)
type store = Store of storable Store.t * loc

type perm = address list

let s_add : perm -> address -> perm =
  fun p a -> a :: p
let s_rem : perm -> address -> perm = assert false

let (<+>) = s_add
let (<->) = s_rem

let (<|=) = List.mem

let (!$) = loc

(* end of syntax *)

type 'a sem = Error of string | TimeOut | Ok of 'a

let sembind : 'a sem -> ('a -> 'b sem) -> 'b sem =
  fun sa fsb ->
  match sa with
    Error (s) -> Error (s)
  | TimeOut -> TimeOut
  | Ok (a) -> fsb a

let (let*) = sembind

let borrowed : address -> borrow -> address sem =
  fun (Address (bs, ell)) b ->
  match b with
    Imm ->
     Ok (Address (b :: bs, ell))
  | Mut ->
     match bs with
       [] ->
        Ok (Address ([b], ell))
     | (Mut :: bs) ->
        Ok (Address (b :: bs, ell))
     | (Imm :: bs) ->
        Error ("trying to take mutable borrow of immutable borrow")

let rborrowed : borrow -> address -> address sem =
  fun b a -> borrowed a b

let (<.>) = rborrowed

let checkborrowed : address -> borrow -> bool =
  fun (Address (bs, ell)) b ->
  match bs with
    [] ->
     false
  | (b' :: _) ->
     (b = b')

let (<?>) = checkborrowed

let rec vlookup : venv -> ident -> result sem =
  fun gamma x ->
  match gamma with
    VEmpty -> Error ("variable not found")
  | VUpd (gamma, y, r) ->
     if x = y then Ok r else vlookup gamma x

let (.!()) = vlookup

let rec vrestrict : venv -> ident list -> venv =
  fun gamma vs ->
  match gamma with
    VEmpty -> VEmpty
  | VUpd (gamma, x, r) ->
     let gamma' = vrestrict gamma vs in
     if List.mem x vs then VUpd (gamma', x, r) else gamma'

let vsplit : venv -> splitting -> venv * venv =
  fun gamma (vs1, vs2) ->
  vrestrict gamma vs1, vrestrict gamma vs2

let salloc : store -> storable -> (loc * store) =
  fun delta w ->
  match delta with
    Store (htable, nexta) ->
    (nexta, Store (Store.add nexta w htable, nexta+1))

let slookup : store -> loc -> storable sem =
  fun (Store (htable, _)) ell ->
  match Store.find_opt ell htable with
  | Some x -> Ok x
  | None -> Error "illegal store location"

let supdate : store -> loc -> storable -> store sem =
  fun (Store (htable, limit)) ell w ->
  let htable' = Store.add ell w htable in
  Ok (Store (htable', limit))

let (.*()) = slookup
let (.*()<-) = supdate

let getloc : result -> loc sem =
  fun r ->
  match r with
    RADDR (Address ([], rl)) -> Ok rl
  | _ -> Error ("raw location expected")

let getborrowed_loc : result -> (borrow * borrow list * loc) sem =
  fun r ->
  match r with
    RADDR (Address (b :: bs, ell)) -> Ok (b, bs, ell)
  | _ -> Error ("borrowed address expected")

let getaddress : result -> address sem =
  fun r ->
  match r with
    RADDR (rho) -> Ok rho
  | _ -> Error ("address expected")

let getstpoly : storable -> (venv * kappas * constr * kind * ident * exp) sem =
  fun w ->
  match w with
    STPOLY (gamma, kappas, cstr, k, x, e) ->
      Ok (gamma, kappas, cstr, k, x, e)
  | _ ->
     Error ("expected STPOLY")

let getstclos : storable -> (venv * kind * ident * exp) sem =
  fun w ->
  match w with
    STCLOS (gamma, k, x, e) ->
    Ok (gamma, k, x, e)
  | _ ->
     Error ("expected STCLOS")

let getstpair : storable -> (kind * result * result) sem =
  fun w ->
  match w with
    STPAIR (k, r1, r2) ->
    Ok (k, r1, r2)
  | _ ->
     Error ("expected STPAIR")

let getstrsrc : storable -> result sem =
  fun w ->
  match w with
    STRSRC (r) -> Ok r
  | _ -> Error ("expected STRSRC")

let (let*?) : bool -> (unit -> 'b sem) -> 'b sem =
  fun b f -> if b then f () else Error ("test failed")

let (-:>) : 'a -> 'b -> 'a * 'b =
  fun a b -> a, b
let (.+()) : venv -> ident * result -> venv =
  fun v (i, r) -> VUpd (v, i, r)

type subst
let (-->) : 'a list -> 'a var list -> subst = assert false
let (./{}) : 'a -> subst -> 'a = assert false

let (<=>) : constr -> constr -> bool = assert false
let (<<=) : kind -> kind -> kind * kind =
  fun k1 k2 -> k1, k2

  (* eval header *)
let rec eval
  (delta:store) (pi:perm) (gamma:venv) i e
  : (store * perm * result) sem =
  if i=0 then TimeOut else
  let i' = i - 1 in
  match e with
  (**)
  (* rule const *)
  | Const (c) ->
    Ok (delta, pi, RCONST c)
  (**)
  (* rule var *)
  | Var (x) ->
    let* r = gamma.!(x) in
    Ok (delta, pi, r)
  (**)
  (* rule varinst *)
  | Varinst (x, ks) ->
    let* rx = gamma.!(x) in
    let* ell = getloc rx in
    let*? () = !$ ell <|= pi in
    let* w = delta.*(ell) in
    let* (gamma', kappas', cstr', k', x', e') = getstpoly w in
    let pi' =
      if cstr'./{ks-->kappas'} <=> [(k' <<= KUNR None)]./{ks-->kappas'}
      then pi
      else pi <-> !$ ell
    in
    let w = STCLOS (gamma', k'./{ks-->kappas'}, x', e'./{ks-->kappas'}) in
    let (ell', delta') = salloc delta w in
    Ok (delta', pi' <+> !$ ell', RADDR !$ ell')
  (**)
  (* rule lam *)
  | Lam (k, x, e) ->
    let w = STCLOS (gamma, k, x, e) in
    let (ell', delta') = salloc delta w in
    let pi' = pi <+> !$ ell' in
    Ok (delta', pi', RADDR !$ ell')
  (**)
  (* rule sapp *)
  | App (e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* ell_1 = getloc r_1 in
    let*? () = !$ ell_1 <|= pi_1 in
    let* w = delta_1.*(ell_1) in
    let* (gamma', k', x', e') = getstclos w in
    let pi_1' = if k' <= KUNR None then pi_1 else pi_1 <-> !$ ell_1 in
    let* delta_1' = delta_1.*(ell_1) <- (if k' <= KUNR None then w else STRELEASED) in
    let* (delta_2, pi_2, r_2) = eval delta_1' pi_1' gamma_2 i' e_2 in
    let* (delta_3, pi_3, r_3) = eval delta_2 pi_2 gamma'.+(x'-:> r_2) i' e' in
    Ok (delta_3, pi_3, r_3)
  (**)
  (* rule sappanf *)
  | VApp (x_1, x_2) ->
    let* r_1 = gamma.!(x_1) in
    let* ell_1 = getloc r_1 in
    let*? () = !$ ell_1 <|= pi in
    let* w = delta.*(ell_1) in
    let* (gamma', k', x', e') = getstclos w in
    let pi' = (if k' <= KUNR None then pi else pi <-> !$ ell_1) in
    let* delta' = delta.*(ell_1) <- (if k' <= KUNR None then w else STRELEASED) in
    let* r_2 = gamma.!(x_2) in
    let* (delta_3, pi_3, r_3) = eval delta' pi' gamma'.+(x'-:> r_2) i' e' in
    Ok (delta_3, pi_3, r_3)
  (**)
  (* rule slet *)
  | Let (x, e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* (delta_2, pi_2, r_2) = eval delta_1 pi_1 gamma_2.+(x -:> r_1) i' e_2 in
    Ok (delta_2, pi_2, r_2)
  (**)
  (* rule sletfun *)
  | LetFun (f, sigma, k, x, e, e', sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let SCHM(kappas, _, cstr, ty) = sigma in
    let w = STPOLY (gamma_1, kappas, cstr, k, x, e') in
    let (ell', delta') = salloc delta w in
    let pi' = pi <+> !$ ell' in
    let* (delta_1, pi_1, r_1) = eval delta' pi' gamma_2.+(f -:> RADDR !$ ell') i' e' in
    Ok (delta_1, pi_1, r_1)
  (**)
  (* rule spair *)
  | Pair (k, e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* (delta_2, pi_2, r_2) =
      eval delta_1 pi_1 gamma_2 i' e_2
    in
    let w = STPAIR (k, r_1, r_2) in
    let (ell', delta') = salloc delta_2 w in
    Ok (delta', pi_2 <+> !$ ell', RADDR !$ ell')
  (**)
  (* rule spairanf *)
  | VPair (k, x_1, x_2) ->
    let* r_1 = gamma.!(x_1) in
    let* r_2 = gamma.!(x_2) in
    let w = STPAIR (k, r_1, r_2) in
    let (ell', delta') = salloc delta w in
    let pi' = pi <+> !$ ell' in
    Ok (delta', pi', RADDR !$ ell')
  (**)
  (* rule smatch *)
  | Match (x, y, e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* ell = getloc r_1 in
    let* w = delta_1.*(ell) in
    let* (k', r_1', r_2') = getstpair w in
    let pi_1' =
      if k' <= KUNR None then pi_1 else pi_1 <-> !$ ell
    in
    let* (delta_2, pi_2, r_2) = eval delta_1 pi_1' gamma_2.+(x -:> r_1').+(y -:> r_2') i' e_2 in
    Ok (delta_2, pi_2, r_2)
  (**)
  (* rule smatchanf *)
  | VMatch (x, x', z, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* r = gamma_1.!(z) in
    let* ell = getloc r in
    let* w = delta.*(ell) in
    let* (k, r_1, r_1') = getstpair w in
    let pi' = if k <= KUNR None then pi else pi <-> !$ ell in
    let* delta' = delta.*(ell) <- (if k <= KUNR None then w else STRELEASED) in
    let* (delta_2, pi_2, r_2) = eval delta' pi' gamma_2.+(x -:> r_1).+(x' -:> r_1') i' e_2 in
    Ok (delta_2, pi_2, r_2)
  (**)
  (* rule matchborrow *)
  | Matchborrow (x, y, e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* (b, _, ell) = getborrowed_loc r_1 in
    let* w = delta_1.*(ell) in
    let* (k', r_1', r_2') = getstpair w in
    let* rho_1 = getaddress r_1' in
    let* rho_2 = getaddress r_2' in
    let* rho_1' = b<.>rho_1 in
    let* rho_2' = b<.>rho_2 in
    let pi_1' = (((pi_1 <-> rho_1) <-> rho_2) <+> rho_1') <+> rho_2' in
    let r_1'' = RADDR rho_1' in
    let r_2'' = RADDR rho_2' in
    let* (delta_2, pi_2, r_2) = eval delta_1 pi_1' gamma_2.+(x -:> r_1'').+(y -:> r_2'') i' e_2 in
    Ok (delta_2, pi_2, r_2)
  (**)
  (* let pi_2' = (((pi_2 <-> rho_1') <-> rho_2') <+> rho_1) <+> rho_2 in *)
  (* rule matchborrowanf *)
  | VMatchborrow (x, x', z, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* r_1 = gamma_1.!(z) in
    let* (b, _, ell) = getborrowed_loc r_1 in
    let* w = delta.*(ell) in
    let* (k', r_1', r_2') = getstpair w in
    let* rho = getaddress r_1 in
    let pi' = if k' <= KUNR None then pi else pi <-> rho in
    let delta'' = delta in
    let* rho_1 = getaddress r_1' in
    let* rho_2 = getaddress r_2' in
    let* rho_1' = b<.>rho_1 in
    let* rho_2' = b<.>rho_2 in
    let pi'' = (((pi' <-> rho_1) <-> rho_2) <+> rho_1') <+> rho_2' in
    let r_1'' = RADDR rho_1' in
    let r_2'' = RADDR rho_2' in
    let gamma_2'' = gamma_2.+(x -:> r_1'').+(x' -:> r_2'') in
    let* (delta_2, pi_2, r_2) = eval delta'' pi'' gamma_2'' i' e_2 in
    Ok (delta_2, pi_2, r_2)
  (**)
  (* rule sregion *)
  | Region (e, n, x, b) ->
    let* RADDR rho = gamma.!(x) in
    let* rho' = b<.>rho in
    let gamma' = gamma.+(x -:>RADDR rho') in
    let pi = (pi <+> rho') <-> rho in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma' i' e in
    let pi_1 = (pi_1 <-> rho') <+> rho in
    Ok (delta_1, pi_1, r_1)
  (**)
  (*(* previous *)
  | Region (e_1, n, x, b) ->
    let* rx = gamma.!(x) in
    let* rho = getaddress rx in
    let*? () = rho <|= pi in
    let* rho' = b<.>rho in
    let gamma' = gamma.+(x -:>RADDR rho') in
    let pi' = (pi <-> rho) <+> rho' in
    let* (delta_1, pi_1, r_1) = eval delta pi' gamma' i' e_1 in
    let pi_1' = (pi <-> rho') <+> rho in
    Ok (delta_1, pi_1', r_1)
   *)
  (* rule sborrow *)
  | Borrow (b, x) ->
    let* RADDR rho = gamma.!(x) in
    let*? () = rho <?> b && rho <|= pi in
    Ok (delta, pi, RADDR rho)
  (**)
  (*(* previous *)
  | Borrow (b, x) ->
    let* rx = gamma.!(x) in
    let* rho = getaddress rx in
    let* rho' = b<.>rho in
    let*? () = rho' <|= pi in
    Ok (delta, pi, RADDR rho')
   *)
  (* rule screate *)
  | Create ->
    let w = STRSRC (RCONST 0) in
    let (ell_1, delta_1) = salloc delta w in
    let pi_1 = pi <+> !$ ell_1 in
    Ok (delta_1, pi_1, RADDR !$ ell_1)
  (**)
  (* rule screateanf *)
  | VCreate (x) ->
    let* r = gamma.!(x) in
    let w = STRSRC (r) in
    let (ell_1, delta_1) = salloc delta w in
    let pi_1 = pi <+> !$ ell_1 in
    Ok (delta_1, pi_1, RADDR !$ ell_1)
  (**)
  (* rule sdestroy *)
  | Destroy (e_1) ->
    let* (delta_1, pi_1, r_1) = eval delta pi gamma i' e_1 in
    let* rho = getaddress r_1 in
    let* ell = getloc r_1 in
    let* w = delta_1.*(ell) in
    let* r = getstrsrc w in
    let*? () = rho <|= pi_1 in
    let* delta_1' = delta_1.*(ell) <- STRELEASED in
    let pi_1' = pi_1 <-> !$ ell in
    Ok (delta_1', pi_1', RVOID)
  (**)
  (* rule sdestroyanf *)
  | VDestroy (x) ->
    let* r = gamma.!(x) in
    let* rho = getaddress r in
    let* ell = getloc r in
    let* w = delta.*(ell) in
    let* r = getstrsrc w in
    let*? () = rho <|= pi in
    let* delta_1 = delta.*(ell) <- STRELEASED in
    let pi_1 = pi <-> !$ ell in
    Ok (delta_1, pi_1, RVOID)
  (**)
  (* rule sobserve *)
  | Observe (e_1) ->
    let* (delta_1, pi_1, r_1) = eval delta pi gamma i' e_1 in
    let* rho = getaddress r_1 in
    let*? () = rho <|= pi_1 in
    let* (b, _, ell) = getborrowed_loc r_1 in
    let*? () = (b = Imm) in
    let* w = delta_1.*(ell) in
    let* r = getstrsrc w in
    Ok (delta_1, pi_1, r)
  (**)
  (* rule sobserveanf *)
  | VObserve (x) ->
    let* r = gamma.!(x) in
    let* rho = getaddress r in
    let*? () = rho <|= pi in
    let* (b, _, ell) = getborrowed_loc r in
    let*? () = (b = Imm) in
    let* w = delta.*(ell) in
    let* r' = getstrsrc w in
    Ok (delta, pi, r')
  (**)
  (* rule supdate *)
  | Update (e_1, e_2, sp) ->
    let (gamma_1, gamma_2) = vsplit gamma sp in
    let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
    let* rho = getaddress r_1 in
    let* (b, _, ell) = getborrowed_loc r_1 in
    let*? () = (b = Mut) in
    let* (delta_2, pi_2, r_2) = eval delta_1 pi_1 gamma_2 i' e_2 in
    let* w = delta_2.*(ell) in
    let* r = getstrsrc w in
    let*? () = rho <|= pi_2 in
    let* delta_2' = delta_2.*(ell) <- STRSRC (r_2) in
    let pi_2' = pi_2 <-> rho in
    Ok (delta_2', pi_2', RVOID)
  (**)
  (* rule supdateanf *)
  | VUpdate (x_1, x_2) ->
    let* r_1 = gamma.!(x_1) in
    let* rho = getaddress r_1 in
    let* (b, _, ell) = getborrowed_loc r_1 in
    let*? () = (b = Mut) in
    let* r_2 = gamma.!(x_2) in
    let* w = delta.*(ell) in
    let* r = getstrsrc w in
    let*? () = rho <|= pi in
    let* delta' = delta.*(ell) <- STRSRC (r_2) in
    let pi' = pi <-> rho in
    Ok (delta', pi', RVOID)
(**)
