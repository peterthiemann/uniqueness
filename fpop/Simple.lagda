Untyped definitional interpreter with soundness proof for untyped lambda calculus
\begin{code}
module Simple where

open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.All
open import Data.Maybe
open import Data.Nat

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

-- simple types
data Type : Set where
  Num : Type
  Fun : (t₁ : Type) (t₂ : Type) → Type

TEnv = List Type

data Exp Φ : Type → Set where
  Cst : (n : ℕ) → Exp Φ Num
  Var : ∀ {t} → (x : t ∈ Φ) → Exp Φ t
  Lam : ∀ {t₂} → (t₁ : Type) (e : Exp (t₁ ∷ Φ) t₂) → Exp Φ (Fun t₁ t₂)
  App : ∀ {t₁ t₂} → (e₁ : Exp Φ (Fun t₁ t₂)) (e₂ : Exp Φ t₁) → Exp Φ t₂
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

eval : ∀ {Φ t} → Exp Φ t → ℕ → UEnv → Maybe UVal
eval (Cst n) i ϱ = return (UNum n)
eval (Var x) i ϱ = ulookup ϱ x
eval (Lam t₁ e) i ϱ = return (UFun ϱ e)
eval (App  e₁ e₂) zero ϱ = ∅
eval (App e₁ e₂) (suc i) ϱ =
  eval e₁ i ϱ >>= λ{
    (UNum n) → ∅ ;
    (UFun ϱ' e') → eval e₂ i ϱ >>= λ v → eval e' i (v ∷ ϱ') }
\end{code}

\begin{code}
mutual
  data _∈∈_ : UVal → Type → Set where
    in-num : ∀ {n} → UNum n ∈∈ Num
    in-fun : ∀ {ϱ' t₁ t₂} {Φ'} {e' : Exp (t₁ ∷ Φ') t₂} → 
      (p' : ϱ' ⊧ Φ') → UFun ϱ' e' ∈∈ Fun t₁ t₂

  data _⊧_ : UEnv → TEnv → Set where
    empty : [] ⊧ []
    elem  : ∀ {v t ϱ Φ} → v ∈∈ t → ϱ ⊧ Φ → (v ∷ ϱ) ⊧ (t ∷ Φ)

data _∈∈'_ : Maybe UVal → Type → Set where
  in-nothing : ∀ {t} → nothing ∈∈' t
  in-just : ∀ {v t} → v ∈∈ t → just v ∈∈' t

sound-lookup :  ∀ {Φ} {t : Type} → (x : t ∈ Φ) (ϱ : UEnv) → ϱ ⊧ Φ → ulookup ϱ x ∈∈' t
sound-lookup (here px) (x ∷ ϱ) (elem x₂ p) rewrite px = in-just x₂
sound-lookup (there x) (x₁ ∷ ϱ) (elem x₃ p) = sound-lookup x ϱ p

sound : ∀ {Φ t} → (e : Exp Φ t) (ϱ : UEnv) (p : ϱ ⊧ Φ) → ∀ i →  eval e i ϱ ∈∈' t
sound (Cst n) ϱ p i = in-just in-num
sound (Var x) ϱ p i = sound-lookup x ϱ p
sound (Lam t₁ e) ϱ p i = in-just (in-fun p)
sound (App e e₁) ϱ p zero = in-nothing
sound (App e e₁) ϱ p (suc i) 
  with sound e ϱ p i
... | serp
  with eval e i ϱ
... | nothing = in-nothing
... | just v
  with serp
... | in-just (in-fun{ϱ'}{e' = e'} p')
  with sound e₁ ϱ p i
... | se1
  with eval e₁ i ϱ
... | nothing = in-nothing
... | just v₁
  with se1
... | in-just pv1
  =  sound e' (v₁ ∷ ϱ') (elem pv1 p') i
\end{code}
