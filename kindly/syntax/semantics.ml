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

type store = SEmpty | SUpd of store * int * storable

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

let getraw_loc : result -> raw_loc sem =
  fun r ->
  match r with
    RADDR (Loc rl) -> Return rl
  | _ -> Error ("type mismatch")

let getstpoly : storable -> (venv * kappa list * alpha list * constr * kind * ident * exp) sem =
  

let (let*?) : bool -> (unit -> 'b sem) -> 'b sem =
  fun b f ->
  if b then f () else Error ("test failed")

let eval : store -> perm -> venv -> int -> exp -> (store * perm * result) sem =
  fun delta pi gamma i e ->
  match e with
    CONST (c) -> 
     Return (delta, pi, RCONST (c))
  | VAR (x) ->
     let* r = gamma.![x] in
     Return (delta, pi, r)
  | VARINST (x, kappas, tys) ->
     let* rx = gamma.![x] in
     let* rl = getraw_loc rx in (* ℓ ← γ (x) *)
     let*? () = List.mem (Loc rl) pi in
     Error "finished"
  | _ ->
     Error "not implemented"

