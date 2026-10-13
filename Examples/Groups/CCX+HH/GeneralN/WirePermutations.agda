------------------------------------------------------------------------
-- Presentations of groups
--
-- Fixed-width routing of one, two, or three designated wires.  The
-- permutation is extended on the remaining wires, and the existing
-- symmetric-group synthesis expands it into adjacent SWAPs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.WirePermutations where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Permutation as P
  using (Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; transpose ; inverseˡ ; inverseʳ)
import Data.Fin.Permutation.Components as PC
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong)
open import Relation.Nullary.Decidable using (yes ; no)
open import Data.Empty using (⊥-elim)
import Examples.Groups.Symmetric.Surjectivity as S
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.Syntactics as HH

private variable n : ℕ

injective : ∀ (p : Permutation′ n) {i j} → p ⟨$⟩ʳ i ≡ p ⟨$⟩ʳ j → i ≡ j
injective p {i} {j} eq = trans (sym (inverseˡ p))
  (trans (cong (p ⟨$⟩ˡ_) eq) (inverseˡ p))

transpose-other : ∀ {a b i : Fin n} → i ≢ a → i ≢ b →
  transpose a b ⟨$⟩ʳ i ≡ i
transpose-other {a = a} {b} {i} ia ib with i ≟ a
... | yes eq = ⊥-elim (ia eq)
... | no _ with i ≟ b
...   | yes eq = ⊥-elim (ib eq)
...   | no _ = refl

-- Modify a permutation so that one new input has the requested image.
pin : Permutation′ n → Fin n → Fin n → Permutation′ n
pin p i a = p ∘ₚ transpose (p ⟨$⟩ʳ i) a

pin-correct : ∀ (p : Permutation′ n) i a → pin p i a ⟨$⟩ʳ i ≡ a
pin-correct p i a = PC.transpose[i,j,i]≡j (p ⟨$⟩ʳ i) a

pin-preserves : ∀ (p : Permutation′ n) i a j → j ≢ i → (p ⟨$⟩ʳ j) ≢ a →
  pin p i a ⟨$⟩ʳ j ≡ p ⟨$⟩ʳ j
pin-preserves p i a j ji ja = transpose-other (λ eq → ji (injective p eq)) ja

one : Fin (suc n) → Permutation′ (suc n)
one t = transpose zero t

one-zero : ∀ (t : Fin (suc n)) → one t ⟨$⟩ʳ zero ≡ t
one-zero t = PC.transpose[i,j,i]≡j zero t

two : Fin (suc (suc n)) → Fin (suc (suc n)) → Permutation′ (suc (suc n))
two t c = pin (one t) (suc zero) c

two-zero : ∀ (t c : Fin (suc (suc n))) → t ≢ c → two t c ⟨$⟩ʳ zero ≡ t
two-zero t c tc = trans
  (pin-preserves (one t) (suc zero) c zero (λ ())
    (λ eq → tc (trans (sym (one-zero t)) eq)))
  (one-zero t)

two-one : ∀ (t c : Fin (suc (suc n))) → two t c ⟨$⟩ʳ suc zero ≡ c
two-one t c = pin-correct (one t) (suc zero) c

three : Fin (suc (suc (suc n))) → Fin (suc (suc (suc n))) →
  Fin (suc (suc (suc n))) → Permutation′ (suc (suc (suc n)))
three t a b = pin (two t a) (suc (suc zero)) b

three-zero : ∀ (t a b : Fin (suc (suc (suc n)))) → t ≢ a → t ≢ b →
  three t a b ⟨$⟩ʳ zero ≡ t
three-zero t a b ta tb = trans
  (pin-preserves (two t a) (suc (suc zero)) b zero (λ ())
    (λ eq → tb (trans (sym (two-zero t a ta)) eq)))
  (two-zero t a ta)

three-one : ∀ (t a b : Fin (suc (suc (suc n)))) → a ≢ b →
  three t a b ⟨$⟩ʳ suc zero ≡ a
three-one t a b ab = trans
  (pin-preserves (two t a) (suc (suc zero)) b (suc zero) (λ ())
    (λ eq → ab (trans (sym (two-one t a)) eq)))
  (two-one t a)

three-two : ∀ (t a b : Fin (suc (suc (suc n)))) →
  three t a b ⟨$⟩ʳ suc (suc zero) ≡ b
three-two t a b = pin-correct (two t a) (suc (suc zero)) b

route : Permutation′ n → C.Circuit n
route {n} p = C.route (proj₁ (S.go n p))

route-correct : ∀ (p : Permutation′ n) s i →
  C.act (route p) s i ≡ s (p ⟨$⟩ʳ i)
route-correct {n} p s i = trans (C.route-correct (proj₁ (S.go n p)) s i)
  (cong s (proj₂ (S.go n p) i))

-- The requested physical alphabet, with every SWAP expanded.
physical-route : Permutation′ n → HH.Circuit n
physical-route p = C.physical (route p)
