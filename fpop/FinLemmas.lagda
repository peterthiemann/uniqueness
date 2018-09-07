\begin{code}
module FinLemmas where
open import Data.Nat
open import Data.Fin hiding (_≤_; lift; _+_)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])

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

invert-0 : ∀ n → invert (suc n) (fromℕ n) ≡ zero
invert-0 zero = refl
invert-0 (suc n) rewrite invert-0 n = refl

invert-s : ∀ n a → invert (suc (suc n)) (inject₁ a) ≡ suc (invert (suc n) a)
invert-s zero zero = refl
invert-s zero (suc a) with invert 0 a
invert-s zero (suc a) | ()
invert-s (suc n) zero = refl
invert-s (suc n) (suc a) rewrite invert-s n a = refl

inject≤′ :  ∀ {m n} → Fin m → m ≤′ n → Fin n
inject≤′ i ≤′-refl = i
inject≤′ i (≤′-step p) = inject₁ (inject≤′ i p) 

n-n=0 : ∀ n → n ∸ n ≡ 0
n-n=0 zero = refl
n-n=0 (suc n) = n-n=0 n

sn-n=1 : ∀ n → suc n ∸ n ≡ 1
sn-n=1 zero = refl
sn-n=1 (suc n) = sn-n=1 n

sn-i=0->n-i=0 : ∀ n {i} → suc n ∸ i ≡ 0 → n ∸ i ≡ 0
sn-i=0->n-i=0 zero {zero} sni=0 = refl
sn-i=0->n-i=0 zero {suc i} sni=0 = refl
sn-i=0->n-i=0 (suc n) {zero} ()
sn-i=0->n-i=0 (suc n) {suc i} sni=0 = sn-i=0->n-i=0 n {i} sni=0

m<n->sm<sn : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
m<n->sm<sn ≤′-refl = ≤′-refl
m<n->sm<sn (≤′-step m<n) = ≤′-step (m<n->sm<sn m<n)

sm<sn->m<n : ∀ {m n} → suc m ≤′ suc n → m ≤′ n
sm<sn->m<n ≤′-refl = ≤′-refl
sm<sn->m<n {n = zero} (≤′-step ())
sm<sn->m<n {n = suc n} (≤′-step sm<sn) = ≤′-step (sm<sn->m<n sm<sn)

ssi<n->s1<n : ∀ {i n} → suc i ≤′ n → i ≤′ n
ssi<n->s1<n {n = zero} ()
ssi<n->s1<n {n = suc n} sin = ≤′-step (sm<sn->m<n sin)

n-i-not-null : ∀ {i} n → suc i ≤′ n → (n ∸ i) ≢ 0
n-i-not-null zero () n-i=0
n-i-not-null (suc n) ≤′-refl n-i=0 rewrite sn-n=1 n with n-i=0
... | ()
n-i-not-null {i} (suc n) (≤′-step si<n) n-i=0 
  = n-i-not-null n si<n (sn-i=0->n-i=0 n {i} n-i=0)

suc-n-i : ∀ i n → suc i ≤′ n → suc n ∸ i ≡ suc (n ∸ i)
suc-n-i zero n si<n = refl
suc-n-i (suc i) .(suc (suc i)) ≤′-refl = suc-n-i i (suc i) ≤′-refl
suc-n-i (suc i) (suc n) (≤′-step si<n) = suc-n-i i n (ssi<n->s1<n si<n)

congruence-lemma : ∀ {n m j i}
  → suc m ≤′ n
  → suc i ≤′ j
  → n ∸ suc m ≡ j ∸ suc i
  → n ∸ m ≡ j ∸ i
congruence-lemma {m = m}{i = i} ≤′-refl ≤′-refl sm=ji rewrite sn-n=1 m | sn-n=1 i = refl
congruence-lemma {n} {m}{j}{ i} ≤′-refl (≤′-step si<j) sm=ji rewrite sn-n=1 m | n-n=0 m
  = contradiction (sym sm=ji) (n-i-not-null _ si<j)
congruence-lemma {.(suc _)} {m} {.(suc i)} {i} (≤′-step sm<n) ≤′-refl sm=ji rewrite sn-n=1 i | n-n=0 i = contradiction sm=ji (n-i-not-null _ sm<n)
congruence-lemma {.(suc _)} {m} {.(suc _)} {i} (≤′-step sm<n) (≤′-step si<j) sm=ji
  rewrite suc-n-i _ _ si<j | suc-n-i _ _ sm<n = cong suc sm=ji
\end{code}
