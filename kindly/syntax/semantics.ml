type ident = string

type raw_loc = int
type borrow = Imm | Mut

type address = Loc of raw_loc | Borrowed of address * borrow

type result = RADDR of address | RCONST of int | RVOID

type venv = VEmpty | VUpd of venv * ident * result

type kappa = int                (* kind variable *)
type alpha = int                (* type variable *)

type kind = KVAR of kappa
          | KLIN of int option
          | KAFF of int option
          | KUNR of int option

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
         | SAPP of exp * exp
         | SLET of ident * exp * exp
         | SPAIR of kind * exp * exp
         | SMATCH of ident * ident * exp * exp
         | MATCHBORROW of ident * ident * exp * exp
         | SREGION of exp * ident * int * borrow
         | SBORROW of borrow * ident
         | SCREATE of exp
         | SDESTROY of exp
         | SOBSERVE of exp
         | SUPDATE of exp * exp


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


(* end of syntax *)

type 'a sem = Error of string | TimeOut | Return of 'a

let sembind : 'a sem -> ('a -> 'b sem) -> 'b sem =
  fun sa fsb ->
  match sa with
    Error (s) -> Error (s)
  | TimeOut -> TimeOut
  | Return (a) -> fsb a

let (let*) = sembind

let rec vlookup : venv -> ident -> result sem =
  fun gamma x ->
  match gamma with
    VEmpty -> Error ("variable not found")
  | VUpd (gamma, y, r) ->
     if x = y then Return r else vlookup gamma x

let (.!()) = vlookup


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

let (.![]) = slookup

let getraw_loc : result -> raw_loc sem =
  fun r ->
  match r with
    RADDR (Loc rl) -> Return rl
  | _ -> Error ("raw location expected")

let getborrowed_loc : result -> (address * borrow) sem =
  fun r ->
  match r with
    RADDR (Borrowed (a, b)) -> Return (a, b)
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
let (-->) : 'a -> 'a -> subst = assert false
let (./{}) : constr -> subst -> constr = assert false

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
    let*? () = List.mem (Loc ell) pi in
    let* w = delta.![ell] in
    let* (gamma', kappas', cstr', knd', x', e') = getstpoly w in
    let pi' =
      if cstr'./{kinds --> kappas'} <=> (knd', KUNR None)./{kinds --> kappas'}  
      then pi 
      else Set.remove pi ell
    in
    let w = STCLOSURE (gamma', knd'./{kinds --> kappas'},
                       x', e'./{kinds --> kappas'}) in
    let* (ell', delta') = salloc delta w in
    Return (delta', Set.add pi' (Loc ell'), RADDR (Loc ell'))
  | POLYLAM (kappas, cstr, knd, x', e') ->
     let w = STPOLY (gamma, kappas, cstr, knd, x', e') in
     let* (ell', delta') = salloc delta w in
     Return (delta', Set.add pi (Loc ell'), RADDR (Loc ell'))
  | SAPP (e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* (gamma', knd', x', e') = getstclosure w in
     let pi1' =
       if knd' <= KUNR None then pi1 else Set.remove pi1 ell 
     in
     let* (delta2, pi2, r2) = eval delta1 pi1' gamma i' e2 in
     let* (delta3, pi3, r3) = eval delta2 pi2 (VUpd (gamma', x', r2)) i' e' in
     Return (delta3, pi3, r3)
  | SLET (x, e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* (delta2, pi2, r2) = eval delta1 pi1 (VUpd (gamma, x, r1)) i' e2 in
     Return (delta2, pi2, r2)
  | SPAIR (knd, e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* (delta2, pi2, r2) = eval delta1 pi1 gamma i' e2 in
     let w = STPAIR (knd, r1, r2) in
     let* (ell', delta') = salloc delta w in
     Return (delta2, Set.add pi2 (Loc ell'), RADDR (Loc ell'))
  | SMATCH (x, y, e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* (knd', r1', r2') = getstpair w in
     let pi1' =
       if knd' <= KUNR None then pi1 else Set.remove pi1 ell 
     in
     let* (delta2, pi2, r2) = eval delta1 pi1' (VUpd (VUpd (gamma, x, r1'), y, r2')) i' e2 in
     Return (delta2, pi2, r2)
  | MATCHBORROW (x, y, e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* (rho, b) = getborrowed_loc r1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* (knd', r1', r2') = getstpair w in
     let* rho1 = getaddress r1' in
     let* rho2 = getaddress r2' in
     let rho1' = Borrowed (rho1, b) in
     let rho2' = Borrowed (rho2, b) in
     let pi1' = Set.add (Set.add (Set.remove (Set.remove pi1 rho1) rho2) rho1') rho2' in
     let r1'' = RADDR rho1' in
     let r2'' = RADDR rho2' in
     let* (delta2, pi2, r2) = eval delta1 pi1' (VUpd (VUpd (gamma, x, r1''), y, r2'')) i' e2 in
     let pi2' = Set.add (Set.add (Set.remove (Set.remove pi2 rho1') rho2') rho1) rho2 in
     Return (delta2, pi2', r2)
  | SREGION (e1, x, n, b) ->
     let i' = i - 1 in
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let*? () = List.mem rho pi in
     let rho' = Borrowed (rho, b) in
     let pi' = Set.add (Set.remove pi rho) rho' in
     let* (delta1, pi1, r1) = eval delta pi' gamma i' e1 in
     let pi1' = Set.add (Set.remove pi rho') rho in
     Return (delta1, pi1', r1)
  | SBORROW (b, x) ->
     let* rx = gamma.!(x) in
     let* rho = getaddress rx in
     let rho' = Borrowed (rho, b) in
     let*? () = List.mem rho' pi in
     Return (delta, pi, RADDR rho')
  | SCREATE (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let w = STRESOURCE (r1) in
     let* (ell', delta') = salloc delta w in
     let pi1' = Set.add pi (Loc ell') in
     Return (delta1, pi1', RADDR (Loc ell'))
  | SDESTROY (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* r = getstresource w in
     let delta1' = delta1.![ell] <- STRELEASED in
     let pi1' = Set.remove pi1 (Loc ell) in
     Return (delta1', pi1', RVOID)
  | SOBSERVE (e1) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* (rho, b) = getborrowed_loc r1 in
     let*? () = (b = Imm) in
     let* ell = getraw_loc r1 in
     let* w = delta1.![ell] in
     let* r = getstresource w in
     Return (delta1, pi1, r)
  | SUPDATE (e1, e2) ->
     let i' = i - 1 in
     let* (delta1, pi1, r1) = eval delta pi gamma i' e1 in
     let* rho = getaddress r1 in
     let* (_, b) = getborrowed_loc r1 in
     let*? () = (b = Mut) in
     let* (delta2, pi2, r2) = eval delta1 pi1 gamma i' e2 in
     let* ell = getraw_loc r1 in
     let* w = delta2.![ell] in
     let* r = getstresource w in
     let*? () = List.mem rho pi2 in
     let delta2' = delta2.![ell] <- STRESOURCE (r2) in
     let pi2' = Set.remove pi2 rho in
     Return (delta2', pi2', RVOID)

