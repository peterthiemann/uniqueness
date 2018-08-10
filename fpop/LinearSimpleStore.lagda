Untyped definitional interpreter with soundness proof for untyped linear lambda calculus with store-based semantics that checks linearity.
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
MM : Set → Set
MM A = Maybe (Maybe A)

∅ : {A : Set} → Maybe A
∅ = nothing
return : {A : Set} → A → MM A
return x = just (just x)
_>>=_ : {A B : Set} → MM A → (A → MM B) → MM B
just (just x) >>= fb = fb x
just nothing >>= fb = just nothing
nothing >>= fb = nothing
_>>=M_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just x >>=M fb = fb x
nothing >>=M fb = nothing
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
    Used : UStorable n
    UFun : ∀ {Φ t₁ t₂} → (k : Kind) (ϱ : UEnv n) → (e : Exp (t₁ ∷ Φ) t₂) → UStorable n

uhead : ∀ {A : Set} → List A → MM A
uhead [] = nothing
uhead (x ∷ ϱ) = return x

utail : ∀ {A : Set} → List A → Maybe (List A)
utail [] = nothing
utail (x ∷ ϱ) = just ϱ


usplit-env : ∀ {σ Φ Φ₁ Φ₂} → (ts : Split Φ Φ₁ Φ₂) (ϱ : UEnv σ) → Maybe (UEnv σ × UEnv σ)
usplit-env [] [] = just ([] , [])
usplit-env (dupl x ts) [] = nothing
usplit-env (drop x ts) [] = usplit-env ts []
usplit-env (left ts) [] = nothing
usplit-env (rght ts) [] = nothing
usplit-env [] (x ∷ ϱ) = nothing
usplit-env (dupl x₁ ts) (x ∷ ϱ) = usplit-env ts ϱ >>=M λ{ (ϱ₁ , ϱ₂) → just ((x ∷ ϱ₁) , (x ∷ ϱ₂)) }
usplit-env (drop x₁ ts) (x ∷ ϱ) = usplit-env ts ϱ
usplit-env (left ts) (x ∷ ϱ) = usplit-env ts ϱ >>=M λ{ (ϱ₁ , ϱ₂) → just ((x ∷ ϱ₁) , ϱ₂) }
usplit-env (rght ts) (x ∷ ϱ) = usplit-env ts ϱ >>=M λ{ (ϱ₁ , ϱ₂) → just (ϱ₁ , (x ∷ ϱ₂)) }
\end{code}
Some Fin lemmas
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

inject≤′ :  ∀ {m n} → Fin m → m ≤′ n → Fin n
inject≤′ i ≤′-refl = i
inject≤′ i (≤′-step p) = inject₁ (inject≤′ i p) 

≤′-trans : ∀ {l m n} → l ≤′ m → m ≤′ n → l ≤′ n
≤′-trans ≤′-refl ≤′-refl = ≤′-refl
≤′-trans ≤′-refl (≤′-step m≤n) = ≤′-step m≤n
≤′-trans (≤′-step l≤m) ≤′-refl = ≤′-step l≤m
≤′-trans (≤′-step l≤m) (≤′-step m≤n) = ≤′-step (≤′-trans (≤′-step l≤m) m≤n)

\end{code}

\begin{code}
Lifting' : (P : ℕ → Set) → Set
Lifting' P = ∀ {m n} → (m ≤′ n) → P m → P (n)

liftUVal' : Lifting' UVal
liftUVal' p = λ{ (UNum j) → UNum j
               ; (UAddr a) → UAddr (inject≤′ a p) }
               
liftUEnv' : Lifting' UEnv
liftUEnv' p = Data.List.map (liftUVal' p)

liftUStorable' : Lifting' UStorable
liftUStorable' p = λ{ Used → Used ; (UFun k ϱ e) → UFun k (liftUEnv' p ϱ) e }
\end{code}

We have two layers of Maybe.
An outer layer of nothing indicates lack of gas. 
The inner layer indicates type errors.
just nothing is a type error, whereas just (just x) yields value x.
\begin{code}
Gas = ℕ

n+1=suc-n : ∀ {n} → n + 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc n+1=suc-n

nuke-if-lin : ∀ {n} → (k : Kind) → UStore n → Fin n → UStore n
nuke-if-lin One σ i = σ [ i ]≔ Used
nuke-if-lin Many σ i = σ

eval : ∀ {Φ t n} → Exp Φ t → Gas → (σ : UStore n) → UEnv n 
  → MM (∃ λ n' → n ≤′ n' × UStore n' × UVal n')
eval e zero σ ϱ = ∅
eval (Cst j) i σ ϱ
  = return ( , (≤′-refl , σ , UNum j))
eval Var i σ ϱ
  = uhead ϱ >>= λ v → return ( , (≤′-refl , σ , v))
eval{n = n} (Lam k w t₁ e) i σ ϱ
  with UFun k (liftUEnv' (≤′-step ≤′-refl) ϱ) e
... | v 
  with Data.Vec.map (liftUStorable' (≤′-step ≤′-refl)) σ
... | σ'
  rewrite (n+1=suc-n{n})
  = return (suc n , ≤′-step ≤′-refl , v ∷ σ' , UAddr (fromℕ n))
eval (App ts e₁ e₂) (suc i) σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) →
    eval e₁ i σ ϱ₁ >>= λ{ (n₁ , n≤n₁ , σ₁ , v₁) →
      case v₁ of λ{ (UNum j) → just ∅
                  ; (UAddr a) →
    let idx = invert n₁ a in
    case get σ₁ idx of λ{ Used → just ∅ 
                        ; (UFun k ϱ' e') →
    let σ₁' = nuke-if-lin k σ₁ idx in
    eval e₂ i σ₁' (liftUEnv' n≤n₁ ϱ₂) >>= λ{ (n₂ , n₁≤n₂ , σ₂ , v₂) →
    eval e' i σ₂ (v₂ ∷ liftUEnv' n₁≤n₂ ϱ') >>= λ{ (n' , n₂≤n' , σ' , v') →
    return (n' , (≤′-trans n≤n₁ (≤′-trans n₁≤n₂ n₂≤n') , σ' , v')) }}}}}}
eval (Weaken ts un-Φ e) i σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) → eval e i σ ϱ₂ }
\end{code}

Soundness relations
\begin{code}
mutual
  data [_]_∈∈_ {n} (σ : UStore n) : UVal n → Type → Set where
    in-num : ∀ {j} → [ σ ] UNum j ∈∈ Num
    in-fun : ∀ {a k t₁ t₂} → [ σ ] get σ a ∈∈' Fun k t₁ t₂ → [ σ ] UAddr a ∈∈ Fun k t₁ t₂

  data [_]_∈∈'_ {n} (σ : UStore n) : UStorable n → Type → Set where
    st-fun : ∀ {k t₁ Φ' t₂ ϱ'} {e' : Exp (t₁ ∷ Φ') t₂} (p' : [ σ ] ϱ' ⊧ Φ')
      → [ σ ] UFun k ϱ' e' ∈∈' Fun k t₁ t₂

  data [_]_⊧_ {n} (σ : UStore n) : UEnv n → TEnv → Set where
    empty : [ σ ] [] ⊧ []
    elem  : ∀ {v t ϱ Φ} → (v∈t : [ σ ] v ∈∈ t) → (p : [ σ ] ϱ ⊧ Φ) → [ σ ] (v ∷ ϱ) ⊧ (t ∷ Φ)

  data [_]_⊧'_ {n} (σ : UStore n) : ∀ {m} → Vec (UStorable n) m → TEnv → Set where
    empty : [ σ ] [] ⊧' []
    elem  : ∀ {m t Φ}{s : UStorable n}{σ' : Vec (UStorable n) m}
      → [ σ ] s ∈∈' t → [ σ ] σ' ⊧' Φ → [ σ ] (s ∷ σ') ⊧' (t ∷ Φ)

  data _:∈:_ {n} : MM (∃ λ n' → n ≤′ n' × UStore n' × UVal n') → Type → Set where
    in-nogas : ∀{t} → nothing :∈: t
    in-acceptable : ∀ {n' n≤n' σ' v' t Ψ'}
      → (ps : [ σ' ] σ' ⊧' Ψ')
      → (pv : [ σ' ] v' ∈∈ t) 
      → just (just (n' , n≤n' , σ' , v')) :∈: t
\end{code}

Soundness proof
\begin{code}
sound-split : ∀ {n Φ₁ Φ₂} 
  (σ : UStore n) (Ψ : TEnv) (σ⊧Ψ : [ σ ] σ ⊧' Ψ)
  (ϱ : UEnv n) (Φ : TEnv) (ϱ⊧Φ : [ σ ] ϱ ⊧ Φ)
  (ts : Split Φ Φ₁ Φ₂) →
  ∃ λ ϱ₁ → ∃ λ ϱ₂ → usplit-env ts ϱ ≡ just (ϱ₁ , ϱ₂) × ([ σ ] ϱ₁ ⊧ Φ₁) × ([ σ ] ϱ₂ ⊧ Φ₂)
sound-split σ Ψ σ⊧Ψ .[] [] empty [] = [] , [] , refl , empty , empty
sound-split σ Ψ σ⊧Ψ (v ∷ _) .(_ ∷ _) (elem v∈t ϱ⊧Φ) (dupl x ts)
  with sound-split σ Ψ σ⊧Ψ _ _ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = (v ∷ ϱ₁) , ((v ∷ ϱ₂) , (refl , (elem v∈t p₁) , (elem v∈t p₂)))
sound-split σ Ψ σ⊧Ψ .(_ ∷ _) .(_ ∷ _) (elem v∈t ϱ⊧Φ) (drop x ts)
  with sound-split σ Ψ σ⊧Ψ _ _ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = ϱ₁ , (ϱ₂ , (refl , (p₁ , p₂)))
sound-split σ Ψ σ⊧Ψ (v ∷ _) .(_ ∷ _) (elem v∈t ϱ⊧Φ) (left ts)
  with sound-split σ Ψ σ⊧Ψ _ _ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = (v ∷ ϱ₁) , (ϱ₂ , refl , ((elem v∈t p₁) , p₂))
sound-split σ Ψ σ⊧Ψ (v ∷ _) .(_ ∷ _) (elem v∈t ϱ⊧Φ) (rght ts)
  with sound-split σ Ψ σ⊧Ψ _ _ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , p₁ , p₂
  rewrite usp≡
  = ϱ₁ , ((v ∷ ϱ₂) , (refl , (p₁ , (elem v∈t p₂))))

sound : ∀ {n t}
  (σ : UStore n) (Ψ : TEnv) (σ⊧Ψ : [ σ ] σ ⊧' Ψ)
  (ϱ : UEnv n) (Φ : TEnv) (ϱ⊧Φ : [ σ ] ϱ ⊧ Φ)
  (e : Exp Φ t)
  → ∀ i → eval e i σ ϱ :∈: t
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ e zero = in-nogas
sound σ Ψ σ⊧Ψ ϱ [] ϱ⊧Φ (Cst n) (suc i) = in-acceptable σ⊧Ψ in-num
sound σ Ψ σ⊧Ψ .(_ ∷ _) (t ∷ []) (elem v∈t ϱ⊧Φ) Var (suc i) = in-acceptable σ⊧Ψ v∈t
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Lam k w t₁ e) (suc i)
  = {!!}
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App ts e e₁) (suc i) = {!!}
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Weaken ts un-Φ e) (suc i)
  with sound-split σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , ups≡ , p₁ , p₂
  rewrite ups≡
  = sound σ Ψ σ⊧Ψ ϱ₂ _ p₂ e (suc i)
\end{code}
