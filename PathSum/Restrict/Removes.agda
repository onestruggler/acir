------------------------------------------------------------------------
-- Presentations of groups
--
-- A chain of restriction steps removes at most n path variables
-- (Amy, QPL 2018, section 4.1)
--
-- Section 4.1 says the restriction "results in a significant
-- simplification for some circuits, instantly removing up to n path
-- variables".  PathSum.Gauss proves the bound for its elimination
-- (reified-removes); here it is proved for every chain of the general
-- restriction steps of PathSum.Restrict, whatever the outputs.  Each
-- step solves its wire, which stays solved along the rest of the chain
-- (Restrict.Solved-↝*), and a step cannot pivot on a solved wire: on
-- the path it does not keep, its wire reads ¬x_w (unsolved-pivot).  So
-- the wires the steps pivot on are pairwise distinct (pivots: their
-- set, as a predicate on wires, has at least as many elements as the
-- chain has steps), and there are at most n of them
-- (restriction-removes).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Restrict.Removes (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (zero; suc; _+_; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Base using (PathSum)
open import PathSum.Denotation M₀ using (Assign; outBit)
open import PathSum.Gauss.Forms using (countᵂ; countᵂ-≤; countᵂ-grow)
open import PathSum.Reorder using (insertᵃ)
open import PathSum.Restrict M₀ using
  (Solved; Restricts; restricts-Solved; _↝_; step; _↝*_; εʳ; _◅ʳ_)

private
  variable
    n k m m′ : ℕ

  not-≢ : ∀ b → not b ≢ b
  not-≢ false ()
  not-≢ true  ()


------------------------------------------------------------------------
-- A step does not pivot on a solved wire

unsolved-pivot : {ξ : PathSum n k (suc m)} {w : Fin n} {j : Fin (suc m)}
                 {ρ : PathSum n k m} → Restricts ξ w j ρ → ¬ Solved ξ w
unsolved-pivot {n} {m = m} {w = w} {j = j} r s = not-≢ (x₀ w)
  (trans (sym (Restricts.miss r x₀ g₀))
         (s x₀ (insertᵃ j (not (Restricts.keep r x₀ g₀)) g₀)))
  where
  x₀ : Assign n
  x₀ _ = false

  g₀ : Assign m
  g₀ _ = false


------------------------------------------------------------------------
-- The pivots of a chain

-- The set of wires the steps pivot on, the number of steps, and the
-- facts the bound needs: a wire solved at the start is not a pivot,
-- and the set has at least as many elements as there are steps.

record Pivots {n k m m′ : ℕ} (ξ : PathSum n k m) (ρ : PathSum n k m′) : Set where
  field
    wires : Fin n → Bool
    steps : ℕ
    total : m ≡ steps + m′
    bound : steps ≤ countᵂ wires
    fresh : ∀ v → Solved ξ v → wires v ≡ false

private
  ⌊≟⌋-false : {v w : Fin n} → v ≢ w → ⌊ v Fin.≟ w ⌋ ≡ false
  ⌊≟⌋-false {v = v} {w} ne with v Fin.≟ w
  ... | yes e = contradiction e ne
  ... | no  _ = refl

  ⌊≟⌋-refl : (w : Fin n) → ⌊ w Fin.≟ w ⌋ ≡ true
  ⌊≟⌋-refl w with w Fin.≟ w
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

pivots : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ → Pivots ξ ρ
pivots εʳ = record
  { wires = λ _ → false ; steps = 0 ; total = refl ; bound = z≤n
  ; fresh = λ _ _ → refl }
pivots {ξ = ξ} (step w j r ◅ʳ c) = record
  { wires = set
  ; steps = suc (Pivots.steps P)
  ; total = cong suc (Pivots.total P)
  ; bound = ℕ.≤-trans (s≤s (Pivots.bound P))
      (countᵂ-grow (Pivots.wires P) set
        (λ v e → trans (cong (⌊ v Fin.≟ w ⌋ ∨_) e) (∨-zeroʳ _))
        w (Pivots.fresh P w (Restricts.solves r))
        (cong (_∨ Pivots.wires P w) (⌊≟⌋-refl w)))
  ; fresh = λ v s → cong₂ _∨_
      (⌊≟⌋-false (λ { refl → unsolved-pivot r s }))
      (Pivots.fresh P v (restricts-Solved r v s))
  }
  where
  P = pivots c

  set : Fin _ → Bool
  set v = ⌊ v Fin.≟ w ⌋ ∨ Pivots.wires P v


------------------------------------------------------------------------
-- The bound

-- "Instantly removing up to n path variables."

restriction-removes : {ξ : PathSum n k m} {ρ : PathSum n k m′} →
                      ξ ↝* ρ → m ≤ m′ + n
restriction-removes {n = n} {m′ = m′} c = ℕ.≤-trans
  (ℕ.≤-reflexive (trans (Pivots.total P) (ℕ.+-comm (Pivots.steps P) m′)))
  (ℕ.+-monoʳ-≤ m′ (ℕ.≤-trans (Pivots.bound P) (countᵂ-≤ (Pivots.wires P))))
  where
  P = pivots c
