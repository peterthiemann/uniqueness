Untyped definitional interpreter with soundness proof for untyped linear lambda calculus with store-based semantics that checks linearity.
\begin{code}
module LinearStoreNoInvert where

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

open import FinLemmas

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

Some lemmas about vectors and alternative less than or equal
\begin{code}
get : ∀ {A : Set} {n} → Vec A n → Fin n → A
get (x ∷ v) zero = x
get (x ∷ v) (suc i) = get v i

≤′-trans : ∀ {l m n} → l ≤′ m → m ≤′ n → l ≤′ n
≤′-trans ≤′-refl ≤′-refl = ≤′-refl
≤′-trans ≤′-refl (≤′-step m≤n) = ≤′-step m≤n
≤′-trans (≤′-step l≤m) ≤′-refl = ≤′-step l≤m
≤′-trans (≤′-step l≤m) (≤′-step m≤n) = ≤′-step (≤′-trans (≤′-step l≤m) m≤n)
\end{code}

\begin{code}
Lifting : (P : ℕ → Set) → Set
Lifting P = ∀ {m n} → (m ≤′ n) → P m → P n

liftAddr : Lifting Fin
liftAddr ≤′-refl a = a
liftAddr (≤′-step p) a = suc (liftAddr p a)

liftUVal : Lifting UVal
liftUVal p = λ{ (UNum j) → UNum j
               ; (UAddr a) → UAddr (liftAddr p a) }
               
liftUEnv : Lifting UEnv
liftUEnv p = Data.List.map (liftUVal p)

liftUStorable : Lifting UStorable
liftUStorable p = λ{ Used → Used ; (UFun k ϱ e) → UFun k (liftUEnv p ϱ) e }

liftUPreStore : ∀ {m} → Lifting (λ n → (Vec (UStorable n) m))
liftUPreStore p = Data.Vec.map (liftUStorable p)

get-lift : ∀ {n m}
  (σ' : Vec (UStorable n) m) →
  (i : Fin m) →
  get (liftUPreStore (≤′-step ≤′-refl) σ') i ≡ liftUStorable (≤′-step ≤′-refl) (get σ' i)
get-lift (x ∷ σ') zero = refl
get-lift (x ∷ σ') (suc i) = get-lift σ' i
\end{code}

There are two layers of Maybe.
An outer layer of nothing indicates lack of gas. 
The inner layer indicates type errors.
just nothing is a type error, whereas just (just x) yields value x.
\begin{code}
Gas = ℕ

n+1=suc-n : ∀ {n} → n + 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc n+1=suc-n

up1 : ∀ {n} → n ≤′ suc n
up1 = ≤′-step ≤′-refl

nuke-if-lin : ∀ {n} → (k : Kind) → UStore n → Fin n → UStore n
nuke-if-lin One σ i = σ [ i ]≔ Used
nuke-if-lin Many σ i = σ

eval : ∀ {Φ t n} → Exp Φ t → Gas → (σ : UStore n) → UEnv n 
  → MM (∃ λ n' → n ≤′ n' × UStore n' × UVal n')
eval e zero σ ϱ = ∅
eval (Cst j) (suc i) σ ϱ
  = return ( , (≤′-refl , σ , UNum j))
eval Var (suc i) σ ϱ
  = uhead ϱ >>= λ v → return ( , (≤′-refl , σ , v))
eval{n = n} (Lam k w t₁ e) (suc i) σ ϱ
  with UFun k (liftUEnv up1 ϱ) e
... | v 
  with Data.Vec.map (liftUStorable up1) σ
... | σ'
  rewrite (n+1=suc-n{n})
  = return (suc n , up1 , v ∷ σ' , UAddr zero)
eval (App ts e₁ e₂) (suc i) σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) →
    eval e₁ i σ ϱ₁ >>= λ{ (n₁ , n≤n₁ , σ₁ , v₁) →
      case v₁ of λ{ (UNum j) → just ∅
                  ; (UAddr a) →
      case get σ₁ a of λ{ Used → just ∅ 
                        ; (UFun k ϱ' e') →
      let σ₁' = nuke-if-lin k σ₁ a in
      eval e₂ i σ₁' (liftUEnv n≤n₁ ϱ₂) >>= λ{ (n₂ , n₁≤n₂ , σ₂ , v₂) →
      eval e' i σ₂ (v₂ ∷ liftUEnv n₁≤n₂ ϱ') >>= λ{ (n' , n₂≤n' , σ' , v') →
      return (n' , (≤′-trans n≤n₁ (≤′-trans n₁≤n₂ n₂≤n') , σ' , v')) }}}}}}
eval (Weaken ts un-Φ e) (suc i) σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) → eval e i σ ϱ₂ }
\end{code}


Soundness relations
\begin{code}
mutual
  data [_]_∈∈_ {n} (σ : UStore n) : UVal n → Type → Set where
    in-num : ∀ {j} → [ σ ] UNum j ∈∈ Num
    in-fun : ∀ {a k t₁ t₂} → [ σ ] get σ a ∈∈' Fun k t₁ t₂ → [ σ ] UAddr a ∈∈ Fun k t₁ t₂

  data [_]_∈∈'_ {n} (σ : UStore n) : UStorable n → Type → Set where
    st-fun : ∀ {k t₁ Ψ' t₂ ϱ'} 
      {e' : Exp (t₁ ∷ Ψ') t₂}
      (p' : [ σ ] ϱ' ⊧ Ψ')
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

Lifting the soundness relations
\begin{code}
mutual
  lift-∈∈' :
    ∀ {n k t₁ t₂}
    (σ' : UStore n)
    (vs' : UStorable (suc n))
    (us : UStorable n)
    → [ σ' ] us ∈∈' Fun k t₁ t₂
    →
    [ vs' ∷ liftUPreStore up1 σ' ] 
    liftUStorable up1 us ∈∈' Fun k t₁ t₂
  lift-∈∈' σ' vs' Used ()
  lift-∈∈' σ' vs' (UFun k ϱ e) (st-fun p') = st-fun (lift-⊧ vs' p')

  lift-∈∈ : ∀ {n}{σ' : UStore n}{v}{t}
    (vs' : UStorable (suc n)) →
    (v∈t : [ σ' ] v ∈∈ t)
    → 
    [ vs' ∷ liftUPreStore up1 σ' ] liftUVal up1 v ∈∈ t
  lift-∈∈ vs' in-num = in-num
  lift-∈∈{n}{σ'} vs' (in-fun{a} x∈∈') 
    with get (liftUPreStore up1 σ') a
  ... | glsa
    rewrite (get-lift σ' a)
{-
    with get σ' a | inspect (get σ') a
  lift-∈∈ {n} {σ'} vs' (in-fun {a} ()) | Used | _
  lift-∈∈ {n} {σ'} vs' (in-fun {a} (st-fun p')) | UFun k ϱ e | [[ eq ]]
-}
    = in-fun {!!}
{-
  lift-∈∈ {zero} vs' in-num = in-num
  lift-∈∈ {zero} vs' (in-fun{a} x) 
    with invert zero a
  lift-∈∈ {zero} vs' (in-fun {a} x) | ()
  lift-∈∈ {suc n} vs' in-num = in-num
  lift-∈∈ {suc n}{σ'} vs' (in-fun{a = a} x) 
    = in-fun {!!}
-}

  lift-⊧ : ∀ {n}{σ' : UStore n}{ϱ' : UEnv n}{Φ'}
    (vs' : UStorable (suc n)) →
    [ σ' ] ϱ' ⊧ Φ'
    → 
    let up = (≤′-step ≤′-refl) in
    [ vs' ∷ liftUPreStore up σ' ] liftUEnv up ϱ' ⊧ Φ'
  lift-⊧ v' empty = empty
  lift-⊧ v' (elem v∈t srf) = elem (lift-∈∈ v' v∈t) (lift-⊧ v' srf)

  lift-⊧' : ∀ {n}{σ₀ : UStore n}{Ψ'}{Φ'}{ϱ' : UEnv n}
    {m}(σ : Vec (UStorable n) m)             -- the prestore
    (k : Kind) (t₁ t₂ : Type) 
    (e' : Exp (t₁ ∷ Φ') t₂) (p : [ σ₀ ] ϱ' ⊧ Φ')
    → [ σ₀ ] σ ⊧' Ψ' → 
    let sv = UFun k ϱ' e' in
    let up = (≤′-step ≤′-refl) in
    let σ₀' = (liftUStorable up sv ∷ liftUPreStore up σ₀) in
    ( [ σ₀' ] (liftUPreStore up σ) ⊧' (Fun k t₁ t₂ ∷ Ψ'))
  lift-⊧' {n} {σ₀} {.[]} {Φ'} {ϱ'} .[] k t₁ t₂ e' p empty = {!elem!}
  lift-⊧' {n} {σ₀} {.(_ ∷ _)} {Φ'} {ϱ'} .(_ ∷ _) k t₁ t₂ e' p (elem x smp) = {!!}
  {-
    = let ee = st-fun{n}{k = k}{ϱ' = ϱ'}{e' = e'} p in
      let sv = UFun k ϱ' e' in
      let up = (≤′-step{n} ≤′-refl) in
      let sv' = liftUStorable up sv in
      let σ₀' = (sv' ∷ liftUPreStore up σ₀) in
      elem (st-fun (lift-⊧ sv' p)) {!lift-⊧' !}
  -}
\end{code}


Soundness proof
%%\begin{code}
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
sound{n} σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Lam{t₂ = t₂} k w t₁ e) (suc i)
  with UFun k (liftUEnv (≤′-step ≤′-refl) ϱ) e 
    | inspect (UFun k (liftUEnv (≤′-step ≤′-refl) ϱ)) e
... | v | [[ v≡ ]]
  with Data.Vec.map (liftUStorable (≤′-step ≤′-refl)) σ
... | σ'
  rewrite (n+1=suc-n{n}) -- (invert-0 n)
  = in-acceptable 
      (elem (lift-∈∈' {!σ!} v {!!} {!!}) {!lift-⊧'!}) 
      (in-fun (gen-xx (rev-xx (st-fun (lift-⊧ {!v!} {!ϱ⊧Φ!})))))
  where get-xx : get (v ∷ σ') (invert (suc n) (fromℕ n)) ≡ v
        get-xx rewrite invert-0 n = refl
        gen-xx : [ v ∷ σ' ] v ∈∈' Fun k t₁ t₂ → 
                 [ v ∷ σ' ] get (v ∷ σ') (invert (suc n) (fromℕ n)) ∈∈' Fun k t₁ t₂
        gen-xx r rewrite get-xx = r
        rev-xx : let v' = UFun k (liftUEnv (≤′-step ≤′-refl) ϱ) e in 
                 [ v' ∷ σ' ] v' ∈∈' Fun k t₁ t₂ → [ v ∷ σ' ] v ∈∈' Fun k t₁ t₂
        rev-xx r rewrite v≡ = r
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App{k}{t₁}{t₂} ts e e₁) (suc i) 
  with sound-split σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂
  rewrite usp≡
  with eval e i σ ϱ₁ | inspect (eval e i σ) ϱ₁
... | nothing | [[ _ ]] = in-nogas
... | just evalei | [[ eqei ]]
  with sound σ Ψ σ⊧Ψ ϱ₁ _ ϱ₁⊧Φ₁ e i
... | sei
  rewrite eqei
  with sei
... | in-acceptable ps (in-fun get-inv)
  with get-inv
... | gi
  = {!gi!}
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Weaken ts un-Φ e) (suc i)
  with sound-split σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , ups≡ , p₁ , p₂
  rewrite ups≡
  = sound σ Ψ σ⊧Ψ ϱ₂ _ p₂ e i
\end{code}
