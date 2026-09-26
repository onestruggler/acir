------------------------------------------------------------------------
-- Presentations of groups
--
-- A circuit composed after any path-sum acts on its columns
--
-- Section 3 of Amy's QPL 2018 paper checks a circuit C against a
-- specification ξ through the miter ⟦ C† ⟧ ∘ ξ, a composite of
-- path-sums (definition 2.6), and section 5.1 validates a compiler's
-- output C₂ against its input C₁ through the miter of two circuits.
-- PathSum.Miter and PathSum.CRK.Miter stated the first on the columns
-- of ξ, never forming the composite.  This module supplies the one
-- fact needed to form it: if a path-sum ξ′ computes a circuit D on the
-- basis columns, then the composite ξ′ ∘ᴾ ξ has, at every input x, the
-- column D applied to ξ's column at x (∘ᴾ-applyᴳ).  It is proved for
-- any gate model of PathSum.Compose.Gates, so it holds for both gate
-- sets, and nothing is asked of ξ.
--
-- The argument is PathSum.Compose.Gates's simulate-∘ with its first
-- hypothesis dropped.  By proposition 2.7 (prop-2-7ʳ) the composite's
-- column at x is Σ_y ζ^{P(x,y)} times ξ′'s column at the state f(x,y)
-- that the path y reaches; ξ′'s columns at basis states are D applied
-- to basis columns; D is linear for such sums (applyᴳ-Σrot), so it may
-- be applied after the sum; and the sum of the rotated basis columns
-- is ξ's own column at x (amp-Σδ).  simulate-∘ then read ξ's column as
-- a circuit's, which is not needed here.
--
-- The plan of phase B of the work package (the miter as the paper
-- writes it, and translation validation):
--
--  1. The composed miter, for {H, S, CZ} (PathSum.Miter.Compose) and
--     for {H, CNOT, R_k, R_k†} (PathSum.CRK.Miter.Compose).  By
--     ∘ᴾ-applyᴳ the columns of ⟦ C† ⟧ ∘ᴾ ξ are C† applied to those of
--     ξ, which is what PathSum.Miter.spec-miter and its CRK twin
--     characterise; so ⟦ C ⟧ ≋ ξ ⇔ (⟦ C† ⟧ ∘ᴾ ξ) ≋ idPS for any ξ, the
--     normalisation of the composite being k + norm (C†) as definition
--     2.6 makes it.  Lemma 4.1 applies at the miter when ξ is
--     WellFormed, because ⟦ C† ⟧ is an isometry and composing after an
--     isometry keeps WellFormed (PathSum.Compose.WellFormed); for two
--     circuits no hypothesis is left.  The paper's miter of two
--     circuits, ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧, is ≋ to the circuit C₁ ++ C₂ †
--     (PathSum.Compose.Clifford/CRK's ⟦++⟧), the form the earlier
--     modules use.  With composition, prepending a circuit is shown to
--     respect and reflect ≋ as well.
--  2. Translation validation (section 5.1) for circuits over
--     {H, CNOT, R_k, R_k†} at any level (PathSum.CRK.Validation): the
--     restriction of the miter C₁ ++ C₂ † by Gaussian elimination
--     (PathSum.Gauss.Corollary), then any chain of all of figure 2 at
--     any variables (PathSum.Full).  Sound: a chain to a syntactic
--     identity proves ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧; and the two refutations the
--     paper uses, the elimination finding no solution and a reduct
--     matching lemma 4.2 (corrected, PathSum.Interference), prove
--     ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧).  Incomplete beyond Clifford, as the paper
--     says; complete for Clifford circuits along every chain.  The
--     same verdicts for a circuit against a specification ξ, read off
--     reducts of the composed miter ⟦ C† ⟧ ∘ᴾ ξ, as section 5.2 uses
--     it (PathSum.CRK.Specification).
--  3. Worked instances at M₀ = 0 (PathSum.Examples.Validation): two
--     Clifford+T equivalences and the two refutations.
--  4. WellFormed-∘ under a contraction after, and hence under a partial
--     isometry after (PathSum.Compose.Contraction).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Apply (M₀ : ℕ) where

open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import PathSum.Base using (PathSum; phase)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Gates M₀ using
  (GateModel; module Compositional)
open import PathSum.Compose.Properties M₀ using (amp-Σδ; prop-2-7ʳ)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; Σᴮ; Σᴮ-cong; rot; rot-map)
open import PathSum.Denotation M₀ using (Assign; amp; outBit)
open import PathSum.Polynomial using (eval)

private
  variable
    n k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- A circuit after any path-sum

module _ (𝔊 : GateModel) where

  open GateModel 𝔊 using (G)
  open Compositional 𝔊 using (applyᴳ; applyᴳ-cong; applyᴳ-Σrot)

  -- If ξ′ computes D on the basis columns, ξ′ ∘ ξ computes D on the
  -- columns of ξ, whatever ξ is.

  ∘ᴾ-applyᴳ : (ξ : PathSum n k m) (ξ′ : PathSum n k′ m′) (D : List (G n)) →
              (∀ w z → amp ξ′ w z ≐ applyᴳ D (δ w) z) →
              ∀ x z → amp (ξ′ ∘ᴾ ξ) x z ≐ applyᴳ D (amp ξ x) z
  ∘ᴾ-applyᴳ ξ ξ′ D h x z =
    prop-2-7ʳ ξ′ ξ x z
    ∙ Σᴮ-cong (λ y → rot-map (eval (phase ξ) x y) (h (outBit ξ x y) z))
    ∙ ≐-sym (applyᴳ-Σrot D (λ y → eval (phase ξ) x y)
                           (λ y → δ (outBit ξ x y)) z)
    ∙ applyᴳ-cong D {λ w → Σᴮ (λ y → rot (eval (phase ξ) x y)
                                          (δ (outBit ξ x y) w))}
                    {amp ξ x}
                    (λ w → ≐-sym (amp-Σδ ξ x w)) z
