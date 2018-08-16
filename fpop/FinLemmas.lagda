\begin{code}
module FinLemmas where
open import Data.Nat
open import Data.Fin hiding (_≤_; lift; _+_)

open import Relation.Nullary
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

\end{code}
