------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 3.1: HH = I
--
-- The paper illustrates its calculus on the identity circuit HH, whose
-- path-sum is
--
--    HH : |x⟩ ↦ 1/√2² Σ_{y1,y2} e^{2πi (x y1 + y1 y2)/2} |y2⟩,
--
-- and reduces it to |x⟩ by summing over the internal variable y1: the
-- quotient ½(x + y2) forces y2 = x ([HH]), after which y1 no longer
-- occurs and is summed away ([Elim]).  (The paper's prose says the
-- paths "y1 = 0 and y2 = 1" interfere; it means y1 = 0 and y1 = 1.)
--
-- Three versions are checked here.
--
--  * The paper's literal HHᵖ, in its variable order: [HH] then
--    [Elim], ending at the identity's polynomials, so HHᵖ ≋ idPS.  The
--    formal [HH] keeps the substituted variable y2 as a dummy (and the
--    normalisation), which is why [Elim] must follow -- the paper's
--    "[HH, Elim]".
--  * The circuit's own path-sum ⟦ HH ⟧, which lists y2 before y1: the
--    same two rules, at y1 through the rules at any path variable
--    (PathSum.Anywhere), prove ⟦ HH ⟧ ≋ idPS directly.  Moving y1 to
--    the front gives the paper's literal exactly, coefficient by
--    coefficient, so ⟦ HH ⟧ ≋ HHᵖ as well.
--  * Corollary 4.4's route: the isometry restriction ⟦ HH ⟧ᴿ has
--    already solved y2 = x, so a single [Elim] finishes it, and lemma
--    4.1 carries the verdict to ⟦ HH ⟧.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Section3 where

open import Data.Bool.Base using (false)
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Base
open import PathSum.Polynomial
open import PathSum.Reduction 3 using
  (_⟶*_; ε; _◅_; elim-reduct; hh-reduct; ½)
open import PathSum.Reduction.Decidable 3 using (elim!; hh!; hhAt!)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere 3 using (_⟶ᵍ*_; εᵍ; _◅ᵍ_; plain)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Congruence 0 using
  (Congruent; congruent?; reduces-to-id!; reduces-to-idᵍ!)
open import PathSum.Examples.Base using
  (xᵐ; yᵐ; HH; ⟦_⟧; ⟦_⟧ᴿ; mono; circuit-id!; circuit-renumbered-≋)


------------------------------------------------------------------------
-- The paper's path-sum

-- ½(x y1 + y1 y2), output y2; y1 is yᵐ zero.

HHᵖ : PathSum 1 2 2
HHᵖ = ⟨ ½ ·ᴾ (mono (xᵐ zero ∪ᵐ yᵐ zero) +ᴾ
              mono (yᵐ zero ∪ᵐ yᵐ (suc zero)))
      , (λ _ → μ y[ suc zero ]) ⟩

-- [HH] at y1 with quotient ½(x ⊕ y2), solving y2 = x; with y1 gone,
-- y2 is the reduct's y[ zero ].

HHᵖ₁ : PathSum 1 2 1
HHᵖ₁ = hh-reduct HHᵖ zero false (xᵐ zero ∪ᵐ yᵐ zero)

-- [Elim] of the dummy y2.

HHᵖ₂ : PathSum 1 0 0
HHᵖ₂ = elim-reduct HHᵖ₁

HHᵖ-reduces : HHᵖ ⟶* HHᵖ₂
HHᵖ-reduces = hh! HHᵖ zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! HHᵖ₁ ◅ ε)

HHᵖ-id : HHᵖ ≋ idPS
HHᵖ-id = reduces-to-id! HHᵖ-reduces


------------------------------------------------------------------------
-- The circuit's path-sum, by the paper's chain

-- ⟦ HH ⟧ lists y2 first; front (suc zero) brings y1 to the front.

HHᵍ₁ : PathSum 1 2 1
HHᵍ₁ = hh-reduct (front (suc zero) ⟦ HH ⟧) zero false
                 (xᵐ zero ∪ᵐ yᵐ zero)

HHᵍ₂ : PathSum 1 0 0
HHᵍ₂ = elim-reduct HHᵍ₁

HH-reducesᵍ : ⟦ HH ⟧ ⟶ᵍ* HHᵍ₂
HH-reducesᵍ =
  hhAt! ⟦ HH ⟧ (suc zero) zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ᵍ
  (plain (elim! HHᵍ₁) ◅ᵍ εᵍ)

HH-idᵍ : ⟦ HH ⟧ ≋ idPS
HH-idᵍ = reduces-to-idᵍ! HH-reducesᵍ

-- Renumbered, the circuit's path-sum is the paper's.

HH-renumbered : Congruent (front (suc zero) ⟦ HH ⟧) HHᵖ
HH-renumbered =
  toWitness {a? = congruent? (front (suc zero) ⟦ HH ⟧) HHᵖ} tt

HH-literal : ⟦ HH ⟧ ≋ HHᵖ
HH-literal = circuit-renumbered-≋ HH HHᵖ (suc zero ∷ []) refl refl


------------------------------------------------------------------------
-- The restriction, and lemma 4.1

-- The restriction substitutes x for the last variable on the wire, so
-- its phase is ½xy + ½yx, which vanishes modulo 1: [Elim] applies.

_ : phase ⟦ HH ⟧ᴿ (xᵐ zero ∪ᵐ yᵐ zero) ≡ + 8
_ = refl

HH-reduces : ⟦ HH ⟧ᴿ ⟶* elim-reduct ⟦ HH ⟧ᴿ
HH-reduces = elim! ⟦ HH ⟧ᴿ ◅ ε

HH-id : ⟦ HH ⟧ ≋ idPS
HH-id = circuit-id! HH HH-reduces
