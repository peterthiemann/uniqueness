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
open import Data.Vec.All hiding (All)
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
  Cst : (j : ℕ) → Exp [] Num
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
    UAddr : (a : Fin n) → UVal n

  UEnv : ℕ → Set
  UEnv n = List (UVal n)

  data UStorable n : Set where
    Used : UStorable n
    UNum : (i : ℕ) → UStorable n
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

vdrop : ∀ {A : Set} {n} → Vec A n → (i : Fin (suc n)) → Vec A (n ℕ-ℕ i)
vdrop xs zero = xs
vdrop [] (suc ())
vdrop (x ∷ xs) (suc i) = vdrop xs i

≤′-zero : ∀ n → zero ≤′ n
≤′-zero zero = ≤′-refl
≤′-zero (suc n) = ≤′-step (≤′-zero n)

≤′-suc : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
≤′-suc ≤′-refl = ≤′-refl
≤′-suc (≤′-step p) = ≤′-step (≤′-suc p)

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
liftUVal p = λ{ (UAddr a) → UAddr (liftAddr p a) }
               
liftUEnv : Lifting UEnv
liftUEnv p = Data.List.map (liftUVal p)

liftUStorable : Lifting UStorable
liftUStorable p = λ{ Used → Used ; (UNum j) → UNum j ; (UFun k ϱ e) → UFun k (liftUEnv p ϱ) e }

liftUPreStore : ∀ {m} → Lifting (λ n → (Vec (UStorable n) m))
liftUPreStore p = Data.Vec.map (liftUStorable p)
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

get-lift : ∀ {n m}
  (σ' : Vec (UStorable n) m) →
  (i : Fin m) →
  get (liftUPreStore up1 σ') i ≡ liftUStorable up1 (get σ' i)
get-lift (x ∷ σ') zero = refl
get-lift (x ∷ σ') (suc i) = get-lift σ' i

nuke-if-lin : ∀ {n m} → (k : Kind) → Vec (UStorable n) m → Fin m → Vec (UStorable n) m
nuke-if-lin One σ i = σ [ i ]≔ Used
nuke-if-lin Many σ i = σ

nuke-if-lin2 : ∀ {n m} → (k : Kind) 
  → Vec (UStorable n) m → Vec (Maybe Type) m → Fin m
  → (Vec (UStorable n) m × Vec (Maybe Type) m)
nuke-if-lin2 One σ Ψ i = (σ [ i ]≔ Used) , Ψ [ i ]≔ nothing
nuke-if-lin2 Many σ Ψ i = σ , Ψ


eval : ∀ {n Φ t} → Exp Φ t → Gas → (σ : UStore n) → UEnv n 
  → MM (∃ λ n' → n ≤′ n' × UStore n' × UVal n')
eval e zero σ ϱ = ∅
eval{n} (Cst j) (suc i) σ ϱ
  = return (suc n , up1 , UNum j ∷ Data.Vec.map (liftUStorable up1) σ , UAddr zero)
eval Var (suc i) σ ϱ
  = uhead ϱ >>= λ v → return ( , (≤′-refl , σ , v))
eval{n} (Lam k w t₁ e) (suc i) σ ϱ
  with UFun k (liftUEnv up1 ϱ) e
... | v 
  with Data.Vec.map (liftUStorable up1) σ
... | σ'
  rewrite (n+1=suc-n{n})
  = return (suc n , up1 , v ∷ σ' , UAddr zero)
eval (App ts e₁ e₂) (suc i) σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) →
    eval e₁ i σ ϱ₁ >>= λ{ (n₁ , n≤n₁ , σ₁ , v₁) →
      case v₁ of λ{ (UAddr a) →
      case get σ₁ a of λ{ Used → just ∅ 
                        ; (UNum j) → just ∅
                        ; (UFun k ϱ' e') →
      let σ₁' = nuke-if-lin k σ₁ a in
      eval e₂ i σ₁' (liftUEnv n≤n₁ ϱ₂) >>= λ{ (n₂ , n₁≤n₂ , σ₂ , v₂) →
      eval e' i σ₂ (v₂ ∷ liftUEnv n₁≤n₂ ϱ') >>= λ{ (n' , n₂≤n' , σ' , v') →
      return (n' , (≤′-trans n≤n₁ (≤′-trans n₁≤n₂ n₂≤n') , σ' , v')) }}}}}}
eval (Weaken ts un-Φ e) (suc i) σ ϱ
  = just (usplit-env ts ϱ) >>= λ{ (ϱ₁ , ϱ₂) → eval e i σ ϱ₂ }
\end{code}


Soundness relations
(We don't need cycles in the store)
\begin{code}
-- store type
-- all values live in the store
-- they start out as "just", but linear values degrade to "nothing" after first use
SType = λ n → Vec (Maybe Type) n

mutual
  data [_]_∈∈_ {n} (σ : UStore n) : UVal n → Type → Set where
    in-addr : ∀ {a t} → [ σ ] get σ a ∈∈' just t → [ σ ] UAddr a ∈∈ t

  data [_]_∈∈'_ {n} (σ : UStore n) : UStorable n → Maybe Type → Set where
    st-void : [ σ ] Used ∈∈' nothing
    st-num  : ∀ {k} → [ σ ] UNum k ∈∈' just Num
    st-fun  : ∀ {k t₁ t₂ Ψ' ϱ'} 
      {e' : Exp (t₁ ∷ Ψ') t₂}
      (p' : [ σ ] ϱ' ⊧ Ψ')
      → [ σ ] UFun k ϱ' e' ∈∈' just (Fun k t₁ t₂)

  data [_]_⊧_ {n} (σ : UStore n) : UEnv n → TEnv → Set where
    empty : [ σ ] [] ⊧ []
    elem  : ∀ {v t ϱ Φ} → (v∈t : [ σ ] v ∈∈ t) → (p : [ σ ] ϱ ⊧ Φ) → [ σ ] (v ∷ ϱ) ⊧ (t ∷ Φ)

  _⊧'_ : ∀ {n} → UStore n → SType n → Set
  σ ⊧' Ψ = All₂ ([_]_∈∈'_ σ) σ Ψ
  
--  data _⊧'_ : ∀ {n} → UStore n → SType n → Set where
--    empty : ∀ {n} → _⊧'_ {p = ≤′-zero n} [] []
--    elem  : ∀ {n m mt Ψ p}{s : UStorable (suc n)}{σ : Vec (UStorable (suc n)) m}
--      → [ σ ] s ∈∈' mt → _⊧'_ {p = p} σ Ψ → _⊧'_ {p = ≤′-suc {!!}} (s ∷ σ) (mt ∷ Ψ)

  data _:∈:_ {n} : MM (∃ λ n' → n ≤′ n' × UStore n' × UVal n') → Type → Set where
    in-nogas : ∀{t} → nothing :∈: t
    in-acceptable : ∀ {n' n≤n' σ' v' t Ψ'}
      → (ps : σ' ⊧' Ψ')
      → (pv : [ σ' ] v' ∈∈ t) 
      → just (just (n' , n≤n' , σ' , v')) :∈: t
\end{code}

%\begin{code}
access-ustorable' : ∀ {n}{σ : UStore n}{Ψ'}{m}{σ' : Vec (UStorable n) m}
  (ps : σ' ⊧' Ψ') (a : Fin m)
  → ∃ λ k → ∃ λ t₁ → ∃ λ t₂ → [ σ ] get σ' a ∈∈' just (Fun k t₁ t₂)
access-ustorable' ps a = {!!}

access-ustorable : ∀ {n}{σ' : UStore n}{Ψ'}
  (ps : σ' ⊧' Ψ') (a : Fin n)
  → ∃ λ k → ∃ λ t₁ → ∃ λ t₂ → [ σ' ] get σ' a ∈∈' just (Fun k t₁ t₂)
access-ustorable {σ' = σ'} ps a = access-ustorable' {σ = σ'}{σ' = σ'} ps a

get-ustorable' : ∀ {n}{σ : UStore n}{Ψ'}{m}{σ' : Vec (UStorable n) m}
  (ps : σ' ⊧' Ψ') (a : Fin m)
  → ∃ λ k → ∃ λ ϱ' → ∃ λ e' → get σ' a ≡ UFun k ϱ' e'
get-ustorable' ps a = {!!}

get-ustorable : ∀ {n}{σ' : UStore n}{Ψ'}
  (ps : σ' ⊧' Ψ') (a : Fin n)
  → ∃ λ k → ∃ λ ϱ' → ∃ λ e' → get σ' a ≡ UFun k ϱ' e'
get-ustorable {σ' = σ'} ps a = get-ustorable' {σ = σ'}{σ' = σ'} ps a
\end{code}

Lifting the soundness relations
%\begin{code}
mutual
  lift-∈∈' :
    ∀ {n k t₁ t₂}
    (σ' : UStore n)
    (vs' : UStorable (suc n))
    (us : UStorable n)
    → [ σ' ] us ∈∈' just (Fun k t₁ t₂)
    →
    [ vs' ∷ liftUPreStore up1 σ' ] 
    liftUStorable up1 us ∈∈' just (Fun k t₁ t₂)
  lift-∈∈' σ' vs' Used ()
  lift-∈∈' σ' vs' (UFun k ϱ e) (st-fun p') = st-fun (lift-⊧ vs' p')

  lift-∈∈ : ∀ {n}{σ' : UStore n}{v}{t}
    (vs' : UStorable (suc n)) →
    (v∈t : [ σ' ] v ∈∈ t)
    → 
    [ vs' ∷ liftUPreStore up1 σ' ] liftUVal up1 v ∈∈ t
  lift-∈∈ vs' v∈t = {!!}
{-
 in-num = in-num
  lift-∈∈{n}{σ'} vs' (in-fun{a} x∈∈') 
    with get (liftUPreStore up1 σ') a
  ... | glsa
    rewrite (get-lift σ' a)
    with get σ' a | inspect (get σ') a
  lift-∈∈ {n} {σ'} vs' (in-fun {a} ()) | Used | _
  lift-∈∈ {n} {σ'} vs' (in-fun {a} (st-fun p')) | UFun k ϱ e | [[ eq ]]
    = in-fun {!!}
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

  {-
  lift-⊧' : ∀ {n}{σ₀ : UStore n}{Ψ'}{Φ'}{ϱ' : UEnv n}
    {m}(σ : Vec (UStorable n) m)             -- the prestore
    (k : Kind) (t₁ t₂ : Type) 
    (e' : Exp (t₁ ∷ Φ') t₂) (p : [ σ₀ ] ϱ' ⊧ Φ')
    → σ ⊧' Ψ' → 
    let sv = UFun k ϱ' e' in
    let up = (≤′-step ≤′-refl) in
    let σ₀' = (liftUStorable up sv ∷ liftUPreStore up σ₀) in
    ( (liftUPreStore up σ) ⊧' (just (Fun k t₁ t₂) ∷ Ψ'))
  lift-⊧' {n} {σ₀} {.[]} {Φ'} {ϱ'} .[] k t₁ t₂ e' p empty = {!elem!}
  lift-⊧' {n} {σ₀} {.(_ ∷ _)} {Φ'} {ϱ'} .(_ ∷ _) k t₁ t₂ e' p (elem x smp) = {!!}
    = let ee = st-fun{n}{k = k}{ϱ' = ϱ'}{e' = e'} p in
      let sv = UFun k ϱ' e' in
      let up = (≤′-step{n} ≤′-refl) in
      let sv' = liftUStorable up sv in
      let σ₀' = (sv' ∷ liftUPreStore up σ₀) in
      elem (st-fun (lift-⊧ sv' p)) {!lift-⊧' !}
  -}
\end{code}

%\begin{code}
nuke-ok' : ∀ {n}{m}{σ : UStore n}{Ψ'}{σ' : Vec (UStorable n) m}
  (ps : σ' ⊧' Ψ') (a : Fin n) (a' : Fin m)
  → nuke-if-lin One σ' a' ⊧' Ψ'
nuke-ok' ps a a' = {!!}

nuke-ok : ∀ {n} {σ' : UStore n}{Ψ'}
  (ps : σ' ⊧' Ψ') (a : Fin n) (k' : Kind)
  → let σ'' = nuke-if-lin k' σ' a in
    σ'' ⊧' Ψ'
nuke-ok ps a One = nuke-ok' ps a a
nuke-ok ps a Many = ps
\end{code}

Lemmas
\begin{code}
lemma3 :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (u  : UVal n)
  (t  : Type)
  (v∈t : [ σ ] u ∈∈ t)
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ] liftUVal up1 u ∈∈ t

lemma5 :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (ϱ' : List (UVal n))
  (Φ' : List Type)
  (p'  : [ σ ] ϱ' ⊧ Φ')
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ] liftUEnv up1 ϱ' ⊧ Φ'
lemma5 σ [] [] empty = empty
lemma5 σ (v ∷ ϱ') (t ∷ Φ') (elem v∈t p') = elem (lemma3 σ v t v∈t) (lemma5 σ ϱ' Φ' p')

lemma4' :
  ∀ {n m}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (σ' : Vec (UStorable n) m)
  (t  : Type)
  (a'  : Fin m)
  (p  : [ σ ] get σ' a' ∈∈' just t)
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ]
      get (Data.Vec.map (liftUStorable up1) σ') a' ∈∈' just t
lemma4' σ (.(UNum _) ∷ σ') .Num zero st-num = st-num
lemma4' σ ((UFun{Φ'} k ϱ' _) ∷ σ') .(Fun _ _ _) zero (st-fun p') = st-fun (lemma5 σ ϱ' Φ' p')
lemma4' σ (x ∷ σ') t (suc a') p = lemma4' σ σ' t a' p

lemma4 :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (t  : Type)
  (a  : Fin n)
  (p  : [ σ ] get σ a ∈∈' just t)
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ]
      get (Data.Vec.map (liftUStorable up1) σ) a ∈∈' just t
lemma4 σ t a p = lemma4' σ σ t a p

lemma3 σ (UAddr a) t (in-addr x) = in-addr (lemma4 σ t a x)

lemma2 :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (ϱ  : List (UVal n))
  (Φ  : List Type)
  (p  : [ σ ] ϱ ⊧ Φ)
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ] liftUEnv up1 ϱ ⊧ Φ
lemma2 σ [] [] empty = empty
lemma2 σ (u ∷ ϱ) (t ∷ Φ) (elem v∈t p) = elem (lemma3 σ u t v∈t) (lemma2 σ ϱ Φ p)

lemma1 :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ  : UStore n)
  (s  : UStorable n)
  (mt : Maybe Type)
  (p  : [ σ ] s ∈∈' mt)
  →
  [ s' ∷ Data.Vec.map (liftUStorable up1) σ ] liftUStorable up1 s ∈∈' mt
lemma1 σ Used .nothing st-void = st-void
lemma1 σ (UNum i) .(just Num) st-num = st-num
lemma1 σ (UFun k ϱ e) .(just (Fun k _ _)) (st-fun p') = st-fun (lemma2 σ ϱ _ p')

lemma' : 
  ∀ {n m}
  {s' : UStorable (suc n)}
  (σ : UStore n)
  (σ' : Vec (UStorable n) m) (Ψ' : SType m)
  (σ⊧Ψ : All₂ ([_]_∈∈'_ σ) σ' Ψ')
  →
  All₂ ([_]_∈∈'_ (s' ∷ Data.Vec.map (liftUStorable up1) σ))
      (Data.Vec.map (liftUStorable up1) σ') Ψ'
lemma' σ [] [] [] = []
lemma' σ (s ∷ σ') (mt ∷ Ψ') (x₂ ∷ σ⊧Ψ) = lemma1 σ s mt x₂ ∷ lemma' σ σ' Ψ' σ⊧Ψ

lemma :
  ∀ {n}
  {s' : UStorable (suc n)}
  (σ : UStore n) (Ψ : SType n)
  (σ⊧Ψ : All₂ ([_]_∈∈'_ σ) σ Ψ)
  →
  All₂ ([_]_∈∈'_ (s' ∷ Data.Vec.map (liftUStorable up1) σ))
      (Data.Vec.map (liftUStorable up1) σ) Ψ
lemma σ Ψ σ⊧Ψ = lemma' σ σ Ψ σ⊧Ψ
\end{code}

\begin{code}
nuke-if-lin-aux2 : ∀ {n m}
  → (σ₀ : UStore n) (j : Fin n)
  → (σ : Vec (UStorable n) m) → (Ψ : Vec (Maybe Type) m)
  → All₂ ([_]_∈∈'_ σ₀) σ Ψ → (i : Fin m)
  → m ≤′ n → toℕ i ≤′ toℕ j
  → n ∸ m ≡ toℕ j ∸ toℕ i
  → All₂ ([_]_∈∈'_ (σ₀ [ j ]≔ Used)) (σ [ i ]≔ Used) (Ψ [ i ]≔ nothing)
nuke-if-lin-aux2 {n} {suc m} σ₀ j .(_ ∷ _) .(_ ∷ _) (x₁ ∷ allin-σ-Ψ) zero m<n i<j p
  = st-void ∷ {!!}
nuke-if-lin-aux2 {n} {suc m} σ₀ j (_ ∷ σ) (_ ∷ Ψ) (x₁ ∷ allin-σ-Ψ) (suc i) m<n i<j p
  = let c = congruence-lemma m<n i<j p
    in (case x₁ of λ{ st-void → st-void
                    ; st-num → st-num
                    ; (st-fun p') → st-fun {!!}})
       ∷ nuke-if-lin-aux2 σ₀ j σ Ψ allin-σ-Ψ i (si<n->i<n m<n) (si<n->i<n i<j) c

nuke-if-lin-aux : ∀ {n}
  → (σ : UStore n) → (Ψ : Vec (Maybe Type) n) → σ ⊧' Ψ → (i : Fin n)
  → (σ [ i ]≔ Used) ⊧' (Ψ [ i ]≔ nothing)
nuke-if-lin-aux{n} σ Ψ σ⊧'Ψ i 
  = nuke-if-lin-aux2 σ i σ Ψ σ⊧'Ψ i ≤′-refl ≤′-refl n-n=i-i
  where
    n-n=i-i : n ∸ n ≡ toℕ i ∸ toℕ i
    n-n=i-i rewrite n-n=0 n | n-n=0 (toℕ i) = refl
  

nuke-if-lin3 : ∀ {n} → (k : Kind) 
  → (σ : UStore n) → (Ψ : Vec (Maybe Type) n) → σ ⊧' Ψ → Fin n
  → Σ (UStore n) λ σ' → Σ (Vec (Maybe Type) n) λ Ψ' → σ' ⊧' Ψ'
nuke-if-lin3 One σ Ψ σ⊧'Ψ i = (σ [ i ]≔ Used) , Ψ [ i ]≔ nothing , nuke-if-lin-aux σ Ψ σ⊧'Ψ i
nuke-if-lin3 Many σ Ψ σ⊧'Ψ i = σ , Ψ , σ⊧'Ψ
\end{code}


Soundness proof
\begin{code}
sound-split : ∀ {n Φ₁ Φ₂} 
  (σ : UStore n) (Ψ : SType n) (σ⊧Ψ : σ ⊧' Ψ)
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
  (σ : UStore n) (Ψ : SType n) (σ⊧Ψ : σ ⊧' Ψ)
  (ϱ : UEnv n) (Φ : TEnv) (ϱ⊧Φ : [ σ ] ϱ ⊧ Φ)
  (e : Exp Φ t)
  → ∀ i → eval e i σ ϱ :∈: t
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ e zero = in-nogas
sound σ Ψ σ⊧Ψ .[] [] empty (Cst j) (suc i) = in-acceptable (st-num ∷ lemma σ Ψ σ⊧Ψ) (in-addr st-num)
sound σ Ψ σ⊧Ψ .(_ ∷ _) (t ∷ []) (elem v∈t ϱ⊧Φ) Var (suc i) = in-acceptable σ⊧Ψ v∈t
sound{n} σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Lam{t₂ = t₂} k w t₁ e) (suc i)
  rewrite (n+1=suc-n{n})
  = let σ' = Data.Vec.map (liftUStorable up1) σ in
    let ϱ' = (liftUEnv up1 ϱ) in
    let s' = UFun k ϱ' e in
    let la5 = lemma5{s' = s'} σ ϱ Φ ϱ⊧Φ in
    let la = lemma{s' = s'} σ Ψ σ⊧Ψ in
  in-acceptable (st-fun la5 ∷ la) (in-addr (st-fun la5))

sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App{k}{t₁}{t₂} ts e₁ e₂) (suc i) 
  with sound-split σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂
  rewrite usp≡
  with sound σ Ψ σ⊧Ψ ϱ₁ _ ϱ₁⊧Φ₁ e₁ i
... | sound-e with eval e₁ i σ ϱ₁
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App {k} {t₁} {t₂} ts e₁ e₂) (suc i) | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂ | in-nogas | nothing = in-nogas
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App {k} {t₁} {t₂} ts e₁ e₂) (suc i) | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂ | in-acceptable ps pv | just (just (n' , n≤n' , σ' , UAddr a))
  with pv | get σ' a | inspect (get σ') a
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App {k} {t₁} {t₂} ts e₁ e₂) (suc i) | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂ | in-acceptable ps pv | just (just (n' , n≤n' , σ' , UAddr a)) | in-addr gsa-in | UNum _ | [[ gsa-eq ]]
  rewrite gsa-eq
  with gsa-in
... | ()
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App {k} {t₁} {t₂} ts e₁ e₂) (suc i) | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂ | in-acceptable ps pv | just (just (n' , n≤n' , σ' , UAddr a)) | in-addr gsa-in | Used | [[ gsa-eq ]] 
  rewrite gsa-eq 
  with gsa-in
... | ()
sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (App {k} {t₁} {t₂} ts e₁ e₂) (suc i) | ϱ₁ , ϱ₂ , usp≡ , ϱ₁⊧Φ₁ , ϱ₂⊧Φ₂ | in-acceptable ps pv | just (just (n' , n≤n' , σ' , UAddr a)) | in-addr gsa-in | UFun k' r' e' | [[ gsa-eq ]]
  rewrite gsa-eq
  with gsa-in
... | st-fun p'
  = {!!}

{-
  with eval e₁ i σ ϱ₁ | inspect (eval e₁ i σ) ϱ₁
... | nothing | [[ _ ]] = in-nogas
... | just evalei | [[ eqei ]]
  with sound σ Ψ σ⊧Ψ ϱ₁ _ ϱ₁⊧Φ₁ e₁ i
... | sei
  rewrite eqei
  with sei
... | in-acceptable ps pv
  with evalei
... | nothing = {!!}
... | just xxx
  = {!!}
-}


sound σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ (Weaken ts un-Φ e) (suc i)
  with sound-split σ Ψ σ⊧Ψ ϱ Φ ϱ⊧Φ ts
... | ϱ₁ , ϱ₂ , ups≡ , p₁ , p₂
  rewrite ups≡
  = sound σ Ψ σ⊧Ψ ϱ₂ _ p₂ e i
\end{code}
