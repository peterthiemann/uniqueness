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

type constr = (kind * kind) list

type ty = TYVAR of alpha
        | TYARR of kind * ty * ty
        | TYCON of ty list * ident
        | TYBOR of borrow * ty

type schm = SCHM of kappa list * (alpha * kind) list * constr * ty

type exp = CONST of int
         | VAR of ident
         | VARINST of ident * kind list * ty list
         | POLYLAM of kappa list * constr * kind * ident * exp
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
  = STPOLY of venv * kappa list * constr * kind * ident * exp
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

(* end of syntax *)

type 'a sem = Error of string | TimeOut | Return of 'a

let sembind : 'a sem -> ('a -> 'b sem) -> 'b sem =
  fun sa fsb ->
  match sa with
    Error (s) -> Error (s)
  | TimeOut -> TimeOut
  | Return (a) -> fsb a

let (let*) = sembind

let borrowed : address -> borrow -> address sem =
  fun (Address (bs, ell)) b ->
  match b with
    Imm ->
     Return (Address (b :: bs, ell))
  | Mut ->
     match bs with
       [] -> 
        Return (Address ([b], ell))
     | (Mut :: bs) ->
        Return (Address (b :: bs, ell))
     | (Imm :: bs) ->
        Error ("trying to take mutable borrow of immutable borrow")


let rec vlookup : venv -> ident -> result sem =
  fun gamma x ->
  match gamma with
    VEmpty -> Error ("variable not found")
  | VUpd (gamma, y, r) ->
     if x = y then Return r else vlookup gamma x

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
      Return (nexta, Store (Store.add nexta w htable, nexta+1))

let slookup : store -> raw_loc -> storable sem =
  fun (Store (htable, _)) ell ->
  match Store.find_opt ell htable with
  | Some x -> Return x
  | None -> Error "illegal store location"

let supdate : store -> raw_loc -> storable -> store sem =
  fun (Store (htable, limit)) ell w ->
  let htable' = Store.add ell w htable in
  Return (Store (htable', limit))

let (.![]) = slookup
let (.![]<-) = supdate

let getraw_loc : result -> raw_loc sem =
  fun r ->
  match r with
    RADDR (Address ([], rl)) -> Return rl
  | _ -> Error ("raw location expected")

let getborrowed_loc : result -> (borrow * borrow list * raw_loc) sem =
  fun r ->
  match r with
    RADDR (Address (b :: bs, ell)) -> Return (b, bs, ell)
  | _ -> Error ("borrowed address expected")

let getaddress : result -> address sem =
  fun r ->
  match r with
    RADDR (rho) -> Return rho
  | _ -> Error ("address expected")

let getstpoly : storable -> (venv * kappa list * constr * kind * ident * exp) sem =
  fun w ->
  match w with
    STPOLY (gamma, kappas, cstr, knd, x, e) ->
      Return (gamma, kappas, cstr, knd, x, e)
  | _ ->
     Error ("expected STPOLY")

let getstclosure : storable -> (venv * kind * ident * exp) sem =
  fun w ->
  match w with
    STCLOSURE (gamma, knd, x, e) ->
    Return (gamma, knd, x, e)
  | _ ->
     Error ("expected STCLOSURE")

let getstpair : storable -> (kind * result * result) sem =
  fun w ->
  match w with
    STPAIR (knd, r1, r2) ->
    Return (knd, r1, r2)
  | _ ->
     Error ("expected STPAIR")

let getstresource : storable -> result sem =
  fun w ->
  match w with
    STRESOURCE (r) -> Return r
  | _ -> Error ("expected STRESOURCE")

let (let*?) : bool -> (unit -> 'b sem) -> 'b sem =
  fun b f ->
  if b then f () else Error ("test failed")

type subst 
let (-->) : 'a list -> 'a var list -> subst = assert false
let (./{}) : 'a -> subst -> 'a = assert false

let (<=>) : constr -> constr -> bool = assert false

let rec eval : store -> perm -> venv -> int -> exp -> (store * perm * result) sem =
  fun delta pi gamma i e ->
  if i=0 then TimeOut else
  match e with
    CONST (c) -> 
    Return (delta, pi, RCONST (c))
  | VAR (x) ->
    let* r = gamma.!(x) in
    Return (delta, pi, r)
  | VARINST (x, kinds, tys) ->
    let* rx = gamma.!(x) in
    let* ell = getraw_loc rx in (* ℓ ← γ (x) *)
    let*? () = List.mem (loc ell) pi in
    let* w = delta.![ell] in
    let* (gamma', kappas', cstr', knd', x', e') = getstpoly w in
    let pi' =
      if cstr'./{kinds --> kappas'} <=> [(knd', KUNR None)]./{kinds --> kappas'}  
      then pi 
      else s_rem pi (loc ell)
    in
    let w = STCLOSURE (gamma', knd'./{kinds --> kappas'},
                       x', e'./{kinds --> kappas'}) in
    let* (ell', delta') = salloc delta w in
    Return (delta', s_add pi' (loc ell'), RADDR (loc ell'))
  | POLYLAM (kappas, cstr, knd, x', e') ->
     let w = STPOLY (gamma, kappas, cstr, knd, x', e') in
     let* (ell', delta') = salloc delta w in
     Return (delta', s_add pi (loc ell'), RADDR (loc ell'))
  | SAPP (e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* (gamma', knd', x', e') = getstclosure w in
     let pi1' =
       if knd' <= KUNR None then pi1 else s_rem pi1 (loc ell)
     in
     let* (delta2, pi2, r2) = eval delta1 pi1' gamma2 i' e2 in
     let* (delta3, pi3, r3) = eval delta2 pi2 (VUpd (gamma', x', r2)) i' e' in
     Return (delta3, pi3, r3)
  | SLET (x, e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* (delta2, pi2, r2) = eval delta1 pi1 (VUpd (gamma2, x, r1)) i' e2 in
     Return (delta2, pi2, r2)
  | SPAIR (knd, e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* (delta2, pi2, r2) = eval delta1 pi1 gamma2 i' e2 in
     let w = STPAIR (knd, r1, r2) in
     let* (ell', delta') = salloc delta w in
     Return (delta2, s_add pi2 (loc ell'), RADDR (loc ell'))
  | SMATCH (x, y, e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* (knd', r1', r2') = getstpair w in
     let pi1' =
       if knd' <= KUNR None then pi1 else s_rem pi1 (loc ell)
     in
     let* (delta2, pi2, r2) = eval delta1 pi1' (VUpd (VUpd (gamma2, x, r1'), y, r2')) i' e2 in
     Return (delta2, pi2, r2)
  | MATCHBORROW (x, y, e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* (b, _, ell) = getborrowed_loc r1 in
     let* w = delta1.![ell] in
     let* (knd', r1', r2') = getstpair w in
     let* rho1 = getaddress r1' in
     let* rho2 = getaddress r2' in
     let* rho1' = borrowed rho1 b in
     let* rho2' = borrowed rho2 b in
     let pi1' = s_add (s_add (s_rem (s_rem pi1 rho1) rho2) rho1') rho2' in
     let r1'' = RADDR rho1' in
     let r2'' = RADDR rho2' in
     let* (delta2, pi2, r2) = eval delta1 pi1' (VUpd (VUpd (gamma2, x, r1''), y, r2'')) i' e2 in
     let pi2' = s_add (s_add (s_rem (s_rem pi2 rho1') rho2') rho1) rho2 in
     Return (delta2, pi2', r2)
  | SREGION (e1, x, n, b) ->
     let i' = i - 1 in
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let*? () = List.mem rho pi in
     let* rho' = borrowed rho b in
     let pi' = s_add (s_rem pi rho) rho' in
     let* (delta1, pi1, r1) = eval delta pi' gamma i' e1 in
     let pi1' = s_add (s_rem pi rho') rho in
     Return (delta1, pi1', r1)
  | SBORROW (b, x) ->
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let* rho' = borrowed rho b in
     let*? () = List.mem rho' pi in
     Return (delta, pi, RADDR rho')
  | SCREATE (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let w = STRESOURCE (r1) in
     let* (ell', delta') = salloc delta w in
     let pi1' = s_add pi (loc ell') in
     Return (delta1, pi1', RADDR (loc ell'))
  | SDESTROY (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* r = getstresource w in
     let* delta1' = delta1.![ell] <- STRELEASED in
     let pi1' = s_rem pi1 (loc ell) in
     Return (delta1', pi1', RVOID)
  | SOBSERVE (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* (b, _, ell) = getborrowed_loc r1 in
     let*? () = (b = Imm) in
     let* w = delta1.![ell] in
     let* r = getstresource w in
     Return (delta1, pi1, r)
  | SUPDATE (e1, e2, split) ->
     let i' = i - 1 in
     let (gamma1, gamma2) = vsplit gamma split in
     let* (delta1, pi1, r1) = eval delta pi gamma1 i' e1 in
     let* rho = getaddress r1 in
     let* (b, _, ell) = getborrowed_loc r1 in
     let*? () = (b = Mut) in
     let* (delta2, pi2, r2) = eval delta1 pi1 gamma2 i' e2 in
     let* w = delta2.![ell] in
     let* r = getstresource w in
     let*? () = List.mem rho pi2 in
     let* delta2' = delta2.![ell] <- STRESOURCE (r2) in
     let pi2' = s_rem pi2 rho in
     Return (delta2', pi2', RVOID)

