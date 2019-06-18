type ident = string

type raw_loc = int
type borrow = Imm | Mut

type address = Loc of raw_loc | Borrowed of borrow * address

type result = RADDR of address | RCONST of int

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
         | SREGION of exp * ident * int
         | SBORROW of borrow * ident
         | SCREATE of exp
         | SDESTROY of exp
         | SOBSERVE of exp
         | SUPDATE of exp * exp


type storable
  = STPOLY of venv * kappa list * alpha list * constr * kind * ident * exp
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

let (.![]) = vlookup


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
  | _ -> Error ("type mismatch")

let getstpoly : storable -> (venv * kappa list * alpha list * constr * kind * ident * exp) sem =
  fun w ->
  match w with
    STPOLY (gamma, kappas, alphas, cstr, knd, x, e) ->
      Return (gamma, kappas, alphas, cstr, knd, x, e)
  | _ ->
      Error ("expected STPOLY")

let (let*?) : bool -> (unit -> 'b sem) -> 'b sem =
  fun b f ->
  if b then f () else Error ("test failed")

type subst 
let (-->) : 'a -> 'a -> subst = assert false
let (./{}) : constr -> subst -> constr = assert false

let eval : store -> perm -> venv -> int -> exp -> (store * perm * result) sem =
  fun delta pi gamma i e ->
  match e with
    CONST (c) -> 
    Return (delta, pi, RCONST (c))
  | VAR (x) ->
    let* r = gamma.![x] in
    Return (delta, pi, r)
  | VARINST (x, kinds, tys) ->
    let* rx = gamma.![x] in
    let* ell = getraw_loc rx in (* ℓ ← γ (x) *)
    let*? () = List.mem (Loc ell) pi in
    let* w = delta.![ell] in
    let* (gamma', kappas', alphas', cstr', knd', x', e') = getstpoly w in
    let pi' =
      if cstr'./{kinds --> kappas'} <=> (knd' <= KUNR)./{kinds --> kappas'}  
      then pi 
      else Set.remove pi ell
    in
    let w = STCLOSURE (gamma', ksubst kinds kappas' knd', x',
                       tsubst tys alphas' (ksubst kinds kappas' e')) in
    let* (ell', delta') = salloc delta w
        Return (delta', Set.add pi' (Loc ell'), ell') in
    (??)
  | _ ->
    Error "not implemented"

