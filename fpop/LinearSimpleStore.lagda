Untyped definitional interpreter with soundness proof for untyped linear lambda calculus
\begin{code}
module LinearSimpleStore where

open import Data.Fin hiding (_≤_; lift; _+_)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.All
open import Data.Maybe hiding (All)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec hiding (drop; [_]; _>>=_; _∈_)
open import Function

open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

data Kind : Set where
  One Many : Kind

data _⊑_ : Kind → Kind → Set where
  ⊑-refl : ∀ {k} → k ⊑ k
  ⊑-step : Many ⊑ One

-- simple linear types
data Type : Set where
  Num : Type
  Fun : (k : Kind) (t₁ : Type) (t₂ : Type) → Type

TEnv = List Type

data Wf-type (k : Kind) : (t : Type) → Set where
  wft-num : Wf-type k Num
  wft-fun : ∀ {k' t₁ t₂} → k' ⊑ k →  Wf-type k (Fun k' t₁ t₂)

data Wf-env (k : Kind) : (Φ : TEnv) → Set where
  wfe-[] : Wf-env k []
  wfe-:: : ∀ {t Φ} → Wf-type k t → Wf-env k Φ → Wf-env k (t ∷ Φ)

Unr : (t : Type) → Set
Unr = Wf-type Many

-- context splitting, respecting linearity
data Split : TEnv → TEnv → TEnv → Set where
  [] : Split [] [] []
  dupl : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  drop : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ Φ₂
  left : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  rght : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

data Exp : TEnv → Type → Set where
  Cst : (n : ℕ) → Exp [] Num
  Var : ∀ {t} → Exp [ t ] t
  Lam : ∀ {Φ t₂} → (k : Kind) (w : Wf-env k Φ) (t₁ : Type) (e : Exp (t₁ ∷ Φ) t₂) → Exp Φ (Fun k t₁ t₂)
  App : ∀ {k t₁ t₂ Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (e₁ : Exp Φ₁ (Fun k t₁ t₂)) (e₂ : Exp Φ₂ t₁) → Exp Φ t₂
  Weaken : ∀ {t Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (un-Φ : All Unr Φ₁) (e : Exp Φ₂ t) → Exp Φ t
\end{code}

the Maybe monad redefined; just too annoying to use from the stdlib
\begin{code}
∅ : {A : Set} → Maybe A
∅ = nothing
return : {A : Set} → A → Maybe A
return = just
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just x >>= fb = fb x
nothing >>= fb = nothing
\end{code}

\begin{code}

mutual

  UStore : ℕ → Set
  UStore n = Vec (UStorable n) n

  data UVal (n : ℕ) : Set where
    UNum  : (i : ℕ) → UVal n
    UAddr : (a : Fin n) → UVal n

  UEnv : ℕ → Set
  UEnv n = List (UVal n)

  data UStorable n : Set where
    UFun : ∀ {Φ t₁ t₂} → (ϱ : UEnv n) → (e : Exp (t₁ ∷ Φ) t₂) → UStorable n

uhead : ∀ {A : Set} → List A → Maybe A
uhead [] = nothing
uhead (x ∷ ϱ) = just x

utail : ∀ {A : Set} → List A → Maybe (List A)
utail [] = nothing
utail (x ∷ ϱ) = just ϱ


usplit-env : ∀ {σ Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (ϱ : UEnv σ) → Maybe (UEnv σ × UEnv σ)
usplit-env [] [] = return ([] , [])
usplit-env (dupl x ts) [] = nothing
usplit-env (drop x ts) [] = usplit-env ts []
usplit-env (left ts) [] = nothing
usplit-env (rght ts) [] = nothing
usplit-env [] (x ∷ ϱ) = nothing
usplit-env (dupl x₁ ts) (x ∷ ϱ) = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → return ((x ∷ ϱ₁) , (x ∷ ϱ₂)) }
usplit-env (drop x₁ ts) (x ∷ ϱ) = usplit-env ts ϱ
usplit-env (left ts) (x ∷ ϱ) = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → return ((x ∷ ϱ₁) , ϱ₂) }
usplit-env (rght ts) (x ∷ ϱ) = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → return (ϱ₁ , (x ∷ ϱ₂)) }
\end{code}

TODO: we need two levels of Maybe.
One for indicating lack of gas and the other for indicating type errors.
\begin{code}
Lifting : (P : ℕ → Set) → Set
Lifting P = ∀ {n} → (k : ℕ) → P n → P (n + k)

liftUVal : Lifting UVal
liftUVal k = λ { (UNum j) → UNum j
               ; (UAddr a) → UAddr (inject+ k a) } 

liftUEnv : Lifting UEnv
liftUEnv k = Data.List.map (liftUVal k)

liftUStorable : Lifting UStorable
liftUStorable k = λ{ (UFun ϱ e) → UFun (liftUEnv k ϱ) e }

getDifference : ∀ {m n} → m ≤′ n → ∃ λ k → n ≡ k + m
getDifference ≤′-refl = 0 , refl
getDifference (≤′-step p) 
  with getDifference p
... | k , p≡
  = (suc k) , (cong suc p≡)
\end{code}
Inversion of fins
\begin{code}
invert : (n : ℕ) (i : Fin n) → Fin n
invert (suc n) zero = fromℕ n
invert (suc n) (suc i) 
  = inject₁ (invert n i)

to-from-id : ∀ n → toℕ (fromℕ n) ≡ n
to-from-id zero = refl
to-from-id (suc n) = cong suc (to-from-id n)

{-
invert-p : ∀ n → (i : Fin n) → suc (toℕ i + toℕ (invert n i)) ≡ n
invert-p zero ()
invert-p (suc n) zero rewrite to-from-id n = refl
invert-p (suc n) (suc i) = cong suc {!!}
-}

get : ∀ {A : Set} {n} → Vec A n → Fin n → A
get (x ∷ v) zero = x
get (x ∷ v) (suc i) = get v i
\end{code}

\begin{code}
Gas = ℕ

ppp : ∀ {n} → n + 1 ≡ suc n
ppp {zero} = refl
ppp {suc n} = cong suc ppp

eval : ∀ {Φ t n} → Exp Φ t → Gas → (σ : UStore n) → UEnv n 
  → Maybe (∃ λ n' → n ≤′ n' × UStore n' × UVal n')
eval e zero σ ϱ = ∅
eval (Cst j) i σ ϱ
  = return ( , (≤′-refl , σ , UNum j))
eval Var i σ ϱ
  = uhead ϱ >>= λ v → return ( , (≤′-refl , σ , v))
eval{n = n} (Lam k w t₁ e) i σ ϱ
  with UFun (liftUEnv 1 ϱ) e
... | v 
  with Data.Vec.map (liftUStorable 1) σ
... | σ'
  rewrite (ppp{n})
  = return (suc n , ≤′-step ≤′-refl , v ∷ σ' , UAddr (fromℕ n))
eval (App ts e₁ e₂) (suc i) σ ϱ
  = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) →
    eval e₁ i σ ϱ₁ >>= λ{ (n₁ , n≤n₁ , σ₁ , v₁) →
      case v₁ of λ{ (UNum j) → ∅
                  ; (UAddr a) →
    let idx = invert n₁ a in
    case get σ₁ idx of λ{ (UFun ϱ' e') →
    let k,p≡ = getDifference n≤n₁ in
    eval e₂ i σ₁ (liftUEnv {!!} {!ϱ₂!}) >>= λ{ (n₂ , n₁≤n₂ , σ₂ , v₂) →
    eval {!!} {!!} {!!} {!!} }}}}}
eval (Weaken ts un-Φ e) i σ ϱ
  = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → eval e i σ ϱ₂ }
\end{code}









