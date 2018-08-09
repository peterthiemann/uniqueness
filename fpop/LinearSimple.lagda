Untyped definitional interpreter with soundness proof for untyped linear lambda calculus
\begin{code}
module LinearSimple where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.All
open import Data.Maybe hiding (All)
open import Data.Nat
open import Data.Product

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
UEnv : Set
data UVal : Set where
  UNum : (n : ℕ) → UVal
  UFun : ∀ {Φ t₁ t₂} → (ϱ : UEnv) → (e : Exp (t₁ ∷ Φ) t₂) → UVal

UEnv = List UVal

ulookup : ∀ {Φ} {t : Type} → UEnv → (x : t ∈ Φ) → Maybe UVal
ulookup [] (here px) = ∅
ulookup (x ∷ ϱ) (here px) = return x
ulookup [] (there x) = ∅
ulookup (x₁ ∷ ϱ) (there x) = ulookup ϱ x

uhead : UEnv → Maybe UVal
uhead [] = nothing
uhead (x ∷ ϱ) = just x

usplit-env : ∀ {Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (ϱ : UEnv) → Maybe (UEnv × UEnv)
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
eval : ∀ {Φ t} → Exp Φ t → ℕ → UEnv → Maybe UVal
eval (Cst n) i ϱ = return (UNum n)
eval Var i ϱ = uhead ϱ
eval (Lam k w t₁ e) i ϱ = return (UFun ϱ e)
eval (App ts e₁ e₂) zero ϱ = ∅
eval (App ts e₁ e₂) (suc i) ϱ 
  = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → eval e₁ i ϱ₁ >>= λ{
    (UNum n) → ∅ ;
    (UFun ϱ' e') → eval e₂ i ϱ₂ >>= λ v → eval e' i (v ∷ ϱ') } }
eval (Weaken ts un-Φ e) i ϱ
  = usplit-env ts ϱ >>= λ{ (ϱ₁ , ϱ₂) → eval e i ϱ₂ }
\end{code}

Soundness
\begin{code}
mutual
  data _∈∈_ : UVal → Type → Set where
    in-num : ∀ {n} → UNum n ∈∈ Num
    in-fun : ∀ {ϱ' k t₁ t₂} {Φ'} {e' : Exp (t₁ ∷ Φ') t₂} → 
      (p' : ϱ' ⊧ Φ') → UFun ϱ' e' ∈∈ Fun k t₁ t₂

  data _⊧_ : UEnv → TEnv → Set where
    empty : [] ⊧ []
    elem  : ∀ {v t ϱ Φ} → (v∈t : v ∈∈ t) → (p : ϱ ⊧ Φ) → (v ∷ ϱ) ⊧ (t ∷ Φ)

data _∈∈'_ : Maybe UVal → Type → Set where
  in-nothing : ∀ {t} → nothing ∈∈' t
  in-just : ∀ {v t} → v ∈∈ t → just v ∈∈' t

sound-lookup :  ∀ {Φ} {t : Type} → (x : t ∈ Φ) (ϱ : UEnv) → ϱ ⊧ Φ → ulookup ϱ x ∈∈' t
sound-lookup (here px) (x ∷ ϱ) (elem x₂ p) rewrite px = in-just x₂
sound-lookup (there x) (x₁ ∷ ϱ) (elem x₃ p) = sound-lookup x ϱ p

sound-split : ∀ {Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (ϱ : UEnv) (p : ϱ ⊧ Φ) 
  → ∃ λ ϱ₁ → ∃ λ ϱ₂ → (usplit-env ts ϱ ≡ just (ϱ₁ , ϱ₂)) × (ϱ₁ ⊧ Φ₁) × (ϱ₂ ⊧ Φ₂)
sound-split [] [] empty = , , refl , empty , empty
sound-split (dupl x₁ ts) (v ∷ ϱ) (elem v∈t p)
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = v ∷ ϱ₁ , (v ∷ ϱ₂) , refl , ((elem v∈t p₁) , (elem v∈t p₂))
sound-split (drop x₁ ts) (_ ∷ ϱ) (elem v∈t p)
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = ϱ₁ , (ϱ₂ , (refl , (p₁ , p₂)))
sound-split (left ts) (v ∷ ϱ) (elem v∈t p)
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = v ∷ ϱ₁ , ϱ₂ , refl , elem v∈t p₁ , p₂
sound-split (rght ts) (v ∷ ϱ) (elem v∈t p)
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = ϱ₁ , v ∷ ϱ₂ , refl , p₁ , elem v∈t p₂

sound : ∀ {Φ t} → (e : Exp Φ t) (ϱ : UEnv) (p : ϱ ⊧ Φ) → ∀ i →  eval e i ϱ ∈∈' t
sound (Cst n) ϱ p i = in-just in-num
sound Var .(_ ∷ _) (elem x p) i = in-just x
sound (Lam k w t₁ e) ϱ p i = in-just (in-fun p)
sound (App ts e e₁) ϱ p zero = in-nothing
sound (App ts e₁ e₂) ϱ p (suc i)
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  with eval e₁ i ϱ₁ | inspect (eval e₁ i) ϱ₁
... | nothing | _ = in-nothing
... | just v₁ | [[ eq₁ ]]
  with sound e₁ ϱ₁ p₁ i
... | se
  rewrite eq₁
  with se
... | in-just (in-fun{ϱ'}{e' = e'} pp)
  with eval e₂ i ϱ₂ | inspect (eval e₂ i) ϱ₂
... | nothing | _ = in-nothing
... | just v₂ | [[ eq₂ ]]
  with sound e₂ ϱ₂ p₂ i
... | se2
  rewrite eq₂
  with se2
... | in-just se2'
  = sound e' (v₂ ∷ ϱ') (elem se2' pp) i
sound (Weaken ts un-Φ e) ϱ p i
  with sound-split ts ϱ p
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = sound e ϱ₂ p₂ i
\end{code}
