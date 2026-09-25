------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 3.1 for all of figure 2 at any internal path variables
--
-- Every step of PathSum.Full's calculus is a rule of
-- PathSum.Reduction.General applied to ξ renumbered at most twice, so
-- its soundness is that of the head rule (Reduction.Sound.⟶ᴳ-sound:
-- [Elim] from PathSum.Denotation, [ω] and [HH] with Boolean-valued
-- quotients by the calculations of appendix A, [Case] from
-- PathSum.Reduction.CaseSound) together with the fact that
-- renumbering does not change the denotation
-- (Anywhere.Sound.front-≋).  Both are already proved, and the generic
-- Anywhere.Sound.Anywhere-sound composes them; applying it twice
-- gives proposition 3.1 for every rule of figure 2 at every internal
-- path variable, and [Case] at every ordered pair of distinct ones
-- (⟶ᶠ-sound), and for chains by transitivity (⟶ᶠ*-sound).  Moving a
-- pair of variables to the front preserves the denotation (front₂-≋),
-- being two single renumberings.  Nothing here assumes well-formedness
-- or that the path variables are internal beyond what each rule's
-- premises say.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Sound (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; suc)
open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality using (_≢_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum)
open import PathSum.Denotation M₀ using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open import PathSum.Reduction.General M using (_⟶ᴳ_)
open import PathSum.Reduction.Sound M₀ using (⟶ᴳ-sound)
open import PathSum.Reorder using (front)
open import PathSum.Reorder.Pair using (skip; front₂)
open import PathSum.Anywhere M using (Anywhere)
open import PathSum.Anywhere.Sound M₀ using (Anywhere-sound; front-≋)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Renumbering a pair preserves the denotation

front₂-≋ : (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
           (ξ : PathSum n k (suc (suc m))) → front₂ i j i≢j ξ ≋ ξ
front₂-≋ i j i≢j ξ =
  ≋-trans {ξ = front₂ i j i≢j ξ} {ζ = front j ξ} {χ = ξ}
    (front-≋ (suc (skip i≢j)) (front j ξ)) (front-≋ j ξ)

≋-front₂ : (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
           (ξ : PathSum n k (suc (suc m))) → ξ ≋ front₂ i j i≢j ξ
≋-front₂ i j i≢j ξ =
  ≋-sym {ξ = front₂ i j i≢j ξ} {ζ = ξ} (front₂-≋ i j i≢j ξ)


------------------------------------------------------------------------
-- Proposition 3.1

-- A step is a sound head step after at most two renumberings.  The
-- path-sums are written out: _≋_ matches on both normalisations, so
-- none of them is recoverable by unification.

⟶ᶠ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ → ξ ≋ ζ
⟶ᶠ-sound {ξ = a} {ζ = b} =
  Anywhere-sound {R = Anywhere _⟶ᴳ_}
    (λ {_} {_} {_} {_} {_} {ξ} {ζ} →
       Anywhere-sound {R = _⟶ᴳ_}
         (λ {_} {_} {_} {_} {_} {ξ′} {ζ′} → ⟶ᴳ-sound {ξ = ξ′} {ζ = ζ′})
         {ξ = ξ} {ζ = ζ})
    {ξ = a} {ζ = b}

⟶ᶠ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ* ζ → ξ ≋ ζ
⟶ᶠ*-sound (εᶠ {ξ = a}) = ≋-refl {ξ = a}
⟶ᶠ*-sound (_◅ᶠ_ {ξ = a} {ζ = b} {χ = d} step steps) =
  ≋-trans {ξ = a} {ζ = b} {χ = d} (⟶ᶠ-sound step) (⟶ᶠ*-sound steps)
