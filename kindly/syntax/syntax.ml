type ident = string

type raw_loc = int
type borrow = Imm | Mut

type address = Loc of raw_loc | Borrowed of borrow * address

type result = Addr of address | Const of int

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
  = Poly of venv * kappa list * alpha list * constr * kind * ident * exp
  | Closure of venv * kind * ident * exp
  | Pair of kind * result * result
  | Resource of result
  | Released

type store = SEmpty | SUpd of store * int * storable

type perm = raw_loc list

