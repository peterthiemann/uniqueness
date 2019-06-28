(* with splitting*)
type ident = string

type splitting = ident list * ident list

type raw_loc = int
type borrow = Imm | Mut

type address = Address of borrow list * raw_loc

let loc : raw_loc -> address =
  fun ell -> Address ([], ell)

type result = RADDR of address | RCONST of int | RVOID

type venv = VEmpty | VUpd of venv * ident * result

type alpha = int                (* type variable *)

type 'a var = VAR of int

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

type exp = CONST of int
         | VAR of ident
         | VARINST of ident * kind list * ty list
         | POLYLAM of kappas * constr * kind * ident * exp
         | SAPP of exp * exp * splitting
         | SLET of ident * exp * exp * splitting
         | SPAIR of kind * exp * exp * splitting
         | SMATCH of ident * ident * exp * exp * splitting
         | MATCHBORROW of ident * ident * exp * exp * splitting
         | SREGION of exp * ident * int * borrow
         | SBORROW of borrow * ident
         | SCREATE of exp
         | SDESTROY of exp
         | SOBSERVE of exp
         | SUPDATE of exp * exp * splitting


type storable
  = STPOLY of venv * kappas * constr * kind * ident * exp
  | STCLOSURE of venv * kind * ident * exp
  | STPAIR of kind * result * result
  | STRESOURCE of result
  | STRELEASED

(* hashtable and next free location *)
module Store = Map.Make(Int)
type store = Store of storable Store.t * raw_loc

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

let salloc : store -> storable -> (raw_loc * store) sem =
  fun delta w ->
  match delta with
    Store (htable, nexta) ->
      Ok (nexta, Store (Store.add nexta w htable, nexta+1))

let slookup : store -> raw_loc -> storable sem =
  fun (Store (htable, _)) ell ->
  match Store.find_opt ell htable with
  | Some x -> Ok x
  | None -> Error "illegal store location"

let supdate : store -> raw_loc -> storable -> store sem =
  fun (Store (htable, limit)) ell w ->
  let htable' = Store.add ell w htable in
  Ok (Store (htable', limit))

let (.*()) = slookup
let (.*()<-) = supdate

let getraw_loc : result -> raw_loc sem =
  fun r ->
  match r with
    RADDR (Address ([], rl)) -> Ok rl
  | _ -> Error ("raw location expected")

let getborrowed_loc : result -> (borrow * borrow list * raw_loc) sem =
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

let getstclosure : storable -> (venv * kind * ident * exp) sem =
  fun w ->
  match w with
    STCLOSURE (gamma, k, x, e) ->
    Ok (gamma, k, x, e)
  | _ ->
     Error ("expected STCLOSURE")

let getstpair : storable -> (kind * result * result) sem =
  fun w ->
  match w with
    STPAIR (k, r1, r2) ->
    Ok (k, r1, r2)
  | _ ->
     Error ("expected STPAIR")

let getstresource : storable -> result sem =
  fun w ->
  match w with
    STRESOURCE (r) -> Ok r
  | _ -> Error ("expected STRESOURCE")

let (let*?) : bool -> (unit -> 'b sem) -> 'b sem =
  fun b f ->
  if b then f () else Error ("test failed")

let (-:>) : 'a -> 'b -> 'a * 'b =
  fun a b -> a, b
let (.+()) : venv -> ident * result -> venv =
  fun v (i, r) -> VUpd (v, i, r)

type subst 
let (-->) : 'a list -> 'a var list -> subst = assert false
let (./{}) : 'a -> subst -> 'a = assert false

let (<=>) : constr -> constr -> bool = assert false

let rec eval : store -> perm -> venv -> int -> exp -> (store * perm * result) sem =
  fun delta pi gamma i e ->
  if i=0 then TimeOut else
  match e with
  (* rule const *)
  | CONST (c) -> 
    Ok (delta, pi, RCONST (c))
  (**)
  (* rule var *)
  | VAR (x) ->
    let* r = gamma.!(x) in
    Ok (delta, pi, r)
  (**)
  (* rule varinst *)
  | VARINST (x, ks, tys) ->
    let* rx = gamma.!(x) in
    let* ell = getraw_loc rx in
    let*? () = !$ ell <|= pi in
    let* w = delta.*(ell) in
    let* (gamma', kappas', cstr', k', x', e') = getstpoly w in
    let pi' =
      if cstr'./{ks --> kappas'} <=> [(k', KUNR None)]./{ks --> kappas'}  
      then pi 
      else pi <-> !$ ell
    in
    let w = STCLOSURE (gamma', k'./{ks --> kappas'},
                       x', e'./{ks --> kappas'}) in
    let* (ell', delta') = salloc delta w in
    Ok (delta', pi' <+> !$ ell', RADDR !$ ell')
  (**)
  (* rule polylam *)
  | POLYLAM (kappas, cstr, k, x', e') ->
     let w = STPOLY (gamma, kappas, cstr, k, x', e') in
     let* (ell', delta') = salloc delta w in
     Ok (delta', pi <+> !$ ell', RADDR !$ ell')
  (**)
  (* rule sapp *)
  | SAPP (e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* ell_1 = getraw_loc r_1 in
     let* w = delta_1.*(ell_1) in
     let* (gamma', k', x', e') = getstclosure w in
     let pi_1' = (if k' <= KUNR None then pi_1 else pi_1 <-> !$ ell_1) in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1' gamma_2 i' e_2 in
     let* (delta_3, pi_3, r_3) = eval delta_2 pi_2 gamma'.+(x'-:> r_2) i' e' in
     Ok (delta_3, pi_3, r_3)
  (**)
  (* rule slet *)
  | SLET (x, e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1 gamma_2.+(x -:> r_1) i' e_2 in
     Ok (delta_2, pi_2, r_2)
  (**)
  (* rule spair *)
  | SPAIR (k, e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1 gamma_2 i' e_2 in
     let w = STPAIR (k, r_1, r_2) in
     let* (ell', delta') = salloc delta w in
     Ok (delta_2, pi_2 <+> !$ ell', RADDR !$ ell')
  (**)
  (* rule smatch *)
  | SMATCH (x, y, e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* ell = getraw_loc r_1 in
     let* w = delta_1.*(ell) in
     let* (k', r_1', r_2') = getstpair w in
     let pi_1' =
       if k' <= KUNR None then pi_1 else pi_1 <-> !$ ell
     in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1' gamma_2.+(x -:> r_1').+(y -:> r_2') i' e_2 in
     Ok (delta_2, pi_2, r_2)
  (**)
  (* rule matchborrow *)
  | MATCHBORROW (x, y, e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* (b, _, ell) = getborrowed_loc r_1 in
     let* w = delta_1.*(ell) in
     let* (k', r_1', r_2') = getstpair w in
     let* rho_1 = getaddress r_1' in
     let* rho_2 = getaddress r_2' in
     let* rho_1' = borrowed rho_1 b in
     let* rho_2' = borrowed rho_2 b in
     let pi_1' = (((pi_1 <-> rho_1) <-> rho_2) <+> rho_1') <+> rho_2' in
     let r_1'' = RADDR rho_1' in
     let r_2'' = RADDR rho_2' in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1' gamma_2.+(x -:> r_1'').+(y -:> r_2'') i' e_2 in
     let pi_2' = (((pi_2 <-> rho_1') <-> rho_2') <+> rho_1) <+> rho_2 in
     Ok (delta_2, pi_2', r_2)
  (**)
  (* rule sregion *)
  | SREGION (e_1, x, n, b) ->
     let i' = i - 1 in
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let*? () = rho <|= pi in
     let* rho' = borrowed rho b in
     let pi' = (pi <-> rho) <+> rho' in
     let* (delta_1, pi_1, r_1) = eval delta pi' gamma i' e_1 in
     let pi_1' = (pi <-> rho') <+> rho in
     Ok (delta_1, pi_1', r_1)
  (**)
  (* rule sborrow *)
  | SBORROW (b, x) ->
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let* rho' = borrowed rho b in
     let*? () = rho' <|= pi in
     Ok (delta, pi, RADDR rho')
  (**)
  (* rule screate *)
  | SCREATE (e_1) ->
     let i' = i - 1 in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma i' e_1 in
     let w = STRESOURCE (r_1) in
     let* (ell', delta') = salloc delta w in
     let pi_1' = pi <+> !$ ell' in
     Ok (delta_1, pi_1', RADDR !$ ell')
  (**)
  (* rule sdestroy *)
  | SDESTROY (e_1) ->
     let i' = i - 1 in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma i' e_1 in
     let* ell = getraw_loc r_1 in
     let* w = delta_1.*(ell) in
     let* r = getstresource w in
     let* delta_1' = delta_1.*(ell) <- STRELEASED in
     let pi_1' = pi_1 <-> !$ ell in
     Ok (delta_1', pi_1', RVOID)
  (**)
  (* rule sobserve *)
  | SOBSERVE (e_1) ->
     let i' = i - 1 in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma i' e_1 in
     let* (b, _, ell) = getborrowed_loc r_1 in
     let*? () = (b = Imm) in
     let* w = delta_1.*(ell) in
     let* r = getstresource w in
     Ok (delta_1, pi_1, r)
  (**)
  (* rule supdate *)
  | SUPDATE (e_1, e_2, sp) ->
     let i' = i - 1 in
     let (gamma_1, gamma_2) = vsplit gamma sp in
     let* (delta_1, pi_1, r_1) = eval delta pi gamma_1 i' e_1 in
     let* rho = getaddress r_1 in
     let* (b, _, ell) = getborrowed_loc r_1 in
     let*? () = (b = Mut) in
     let* (delta_2, pi_2, r_2) = eval delta_1 pi_1 gamma_2 i' e_2 in
     let* w = delta_2.*(ell) in
     let* r = getstresource w in
     let*? () = rho <|= pi_2 in
     let* delta_2' = delta_2.*(ell) <- STRESOURCE (r_2) in
     let pi_2' = pi_2 <-> rho in
     Ok (delta_2', pi_2', RVOID)
  (**)
