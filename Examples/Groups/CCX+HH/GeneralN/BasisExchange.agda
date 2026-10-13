------------------------------------------------------------------------
-- Presentations of groups
--
-- A two-level exchange permutes ordinary computational basis columns.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.BasisExchange where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
open import Data.Fin.Properties using (_≟_)
import Data.Fin.Permutation.Components as PC
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (X-gen)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis ; basis-!)
open import Examples.Groups.CCX+HH.GeneralN.WirePermutations using (transpose-other)

private variable n : ℕ

swap : Fin n → Fin n → Fin n → Fin n
swap = PC.transpose

swap-sym : ∀ (a b i : Fin n) → swap a b i ≡ swap b a i
swap-sym a b i = choose (i ≟ a)
  where
  choose : Dec (i ≡ a) → swap a b i ≡ swap b a i
  choose (yes refl) = trans (PC.transpose[i,j,i]≡j a b) (sym (PC.transpose[i,j,j]≡i b a))
  choose (no ia) = next (i ≟ b)
    where
    next : Dec (i ≡ b) → swap a b i ≡ swap b a i
    next (yes refl) = trans (PC.transpose[i,j,j]≡i a b) (sym (PC.transpose[i,j,i]≡j b a))
    next (no ib) = trans (transpose-other ia ib) (sym (transpose-other ib ia))

swap-involutive : ∀ (a b i : Fin n) → swap a b (swap a b i) ≡ i
swap-involutive a b i = trans (cong (swap a b) (swap-sym a b i)) (PC.transpose-inverse a b)

δ-swap : ∀ (a b i j : Fin n) → A.δ (swap a b j) i ≡ A.δ j (swap a b i)
δ-swap a b i j = choose (j ≟ swap a b i)
  where
  choose : Dec (j ≡ swap a b i) → A.δ (swap a b j) i ≡ A.δ j (swap a b i)
  choose (yes refl) = trans (cong (λ k → A.δ k i) (swap-involutive a b i))
    (trans (A.δ-refl i) (sym (A.δ-refl (swap a b i))))
  choose (no ne) = trans (A.δ-≢ {x = swap a b j} {y = i} (λ eq → ne
    (trans (sym (swap-involutive a b j)) (cong (swap a b) eq)))) (sym (A.δ-≢ ne))

exchange-row : ∀ {a b : Fin n} .(p : a < b) (v : Vec D n) j →
  A.actV (X-gen a b p) v A.! j ≡ v A.! swap a b j
exchange-row {a = a} {b} p v j = choose (j ≟ a)
  where
  choose : Dec (j ≡ a) → A.actV (X-gen a b p) v A.! j ≡ v A.! swap a b j
  choose (yes refl) = trans (A.actV-Xa p v) (cong (v A.!_) (sym (PC.transpose[i,j,i]≡j a b)))
  choose (no ja) = next (j ≟ b)
    where
    next : Dec (j ≡ b) → A.actV (X-gen a b p) v A.! j ≡ v A.! swap a b j
    next (yes refl) = trans (A.actV-Xb p v) (cong (v A.!_) (sym (PC.transpose[i,j,j]≡i a b)))
    next (no jb) = trans (A.actV-X≢ p v ja jb) (cong (v A.!_) (sym (transpose-other ja jb)))

exchange-basis : ∀ {a b : Fin n} .(p : a < b) i →
  A.actV (X-gen a b p) (basis i) ≡ basis (swap a b i)
exchange-basis {a = a} {b} p i = A.vec-ext λ j → trans (exchange-row p (basis i) j)
  (trans (basis-! i (swap a b j)) (trans (δ-swap a b i j) (sym (basis-! (swap a b i) j))))
