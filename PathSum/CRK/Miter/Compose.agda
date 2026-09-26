------------------------------------------------------------------------
-- Presentations of groups
--
-- The miter as a composite of path-sums, for circuits over
-- {H, CNOT, R_k, R_k†} (Amy, QPL 2018, section 3)
--
-- PathSum.Miter.Compose for the paper's own gate set, with the inverse
-- C† of PathSum.CRK.Adjoint, the matrices of PathSum.CRK.Semantics and
-- the gate model of PathSum.Compose.CRK, whose gates' path-sums are
-- the ones definition 2.9 prints.  The miter of section 3 is formed by
-- definition 2.6 (PathSum.Compose's _∘ᴾ_) and
--
--    ⟦ C ⟧ ≋ ξ  ⇔  (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS                 (spec-miter-∘)
--
-- for every path-sum ξ, the composite's normalisation being
-- k + norm (C †) as definition 2.6 makes it.  The columns of the
-- composite are C† applied to those of ξ (amp-∘ᴾ, from
-- PathSum.Compose.Apply's ∘ᴾ-applyᴳ), which PathSum.CRK.Miter's
-- spec-miter characterises.  Lemma 4.1 holds at the miter of a
-- WellFormed ξ, ⟦ C † ⟧ being an isometry (PathSum.CRK.Unitarity):
-- miter-lemma-4-1, spec-miter-restriction.  For two circuits the miter
-- is ⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧ (miter-∘, miter-restriction with no hypothesis
-- left), ≋ to the circuit C₁ ++ C₂ † (miter-∘-++, from
-- PathSum.Compose.CRK's ⟦++⟧), the form PathSum.CRK.Miter.miter and
-- the translation validation of PathSum.CRK.Validation use.  And
-- prepending a circuit respects and reflects ≋ (++-congˡ,
-- ++-†-cancelˡ, ++-cancelˡ), through ⟦ D ++ C ⟧ ≋ ⟦ C ⟧ ∘ᴾ ⟦ D ⟧ and
-- the congruence of composition (PathSum.Compose.Laws).  The
-- statements hold at every level: nothing here asks the circuits to be
-- Clifford.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Miter.Compose (M₀ : ℕ) where

open import Data.List.Base using (_++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (sym; trans; cong; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Apply M₀ using (∘ᴾ-applyᴳ)
open import PathSum.Compose.CRK M₀ using
  (crkGates; applyᴳ; applyᴳ≡applyᴬ; ⟦++⟧)
open import PathSum.Compose.Laws M₀ using
  (amp-idPS-δ; ∘ᴾ-congˡ; ∘ᴾ-congʳ; ∘ᴾ-identityʳ)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-∘)
open import PathSum.CRK.Adjoint M using (_†; norm-†)
open import PathSum.CRK.Circuit M using (Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Miter M₀ using (spec-miter; †-inverseˡ)
open import PathSum.CRK.Semantics M₀ using (applyᴬ; prop-2-10)
open import PathSum.CRK.Unitarity M₀ using (circuit-Isometric)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; ≋-sym; ≋-trans)
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id; lemma-4-1)
open import PathSum.PartialIsometry M₀ using (Isometric⇒WellFormed)

private
  variable
    n k m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- The matrix of the gate model is the circuit's, at one entry.

  applyᴳ≐applyᴬ : (C : Circuit n) (ψ : Column n) (z : Assign n) →
                  applyᴳ C ψ z ≐ applyᴬ C ψ z
  applyᴳ≐applyᴬ C ψ z i = cong (λ φ → φ z i) (applyᴳ≡applyᴬ C ψ)


------------------------------------------------------------------------
-- A circuit composed after any path-sum

-- The columns of ⟦ D ⟧ ∘ ξ are D applied to the columns of ξ.

amp-∘ᴾ : (D : Circuit n) (ξ : PathSum n k m) (x z : Assign n) →
         amp (⟦ D ⟧ ∘ᴾ ξ) x z ≐ applyᴬ D (amp ξ x) z
amp-∘ᴾ D ξ x z =
  ∘ᴾ-applyᴳ crkGates ξ ⟦ D ⟧ D
    (λ w u → prop-2-10 D w u ∙ ≐-sym (applyᴳ≐applyᴬ D (δ w) u)) x z
  ∙ applyᴳ≐applyᴬ D (amp ξ x) z


------------------------------------------------------------------------
-- The miter against a specification

-- ⟦ C ⟧ ≡ ξ exactly when the miter ⟦ C† ⟧ ∘ ξ is the identity, for any
-- path-sum ξ.

spec-miter-∘ : (C : Circuit n) (ξ : PathSum n k m) →
               (⟦ C ⟧ ≋ ξ ⇔ (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS)
spec-miter-∘ {k = k} C ξ = mk⇔ to from
  where
  to : ⟦ C ⟧ ≋ ξ → (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS
  to eq x z =
    amp-∘ᴾ (C †) ξ x z
    ∙ Equivalence.to (spec-miter C ξ) eq x z
    ∙ scale-exp (δ x z) (cong (k ℕ+_) (sym (norm-† C)))
    ∙ scale-map (k ℕ+ norm (C †)) (≐-sym (amp-idPS-δ x z))

  from : (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS → ⟦ C ⟧ ≋ ξ
  from eq = Equivalence.from (spec-miter C ξ) (λ x z →
    ≐-sym (amp-∘ᴾ (C †) ξ x z)
    ∙ eq x z
    ∙ scale-map (k ℕ+ norm (C †)) (amp-idPS-δ x z)
    ∙ scale-exp (δ x z) (cong (k ℕ+_) (norm-† C)))

-- Lemma 4.1 at the miter: after the isometry ⟦ C† ⟧ a well-formed ξ
-- stays well formed, so the miter is the identity exactly when its
-- isometry restriction is.

miter-WellFormed : (C : Circuit n) (ξ : PathSum n k m) → WellFormed ξ →
                   WellFormed (⟦ C † ⟧ ∘ᴾ ξ)
miter-WellFormed C ξ wf =
  WellFormed-∘ ⟦ C † ⟧ ξ (circuit-Isometric (C †)) wf

miter-lemma-4-1 : (C : Circuit n) (ξ : PathSum n k m) → WellFormed ξ →
                  ((⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS ⇔ Restriction-id (⟦ C † ⟧ ∘ᴾ ξ))
miter-lemma-4-1 C ξ wf = lemma-4-1 (⟦ C † ⟧ ∘ᴾ ξ) (miter-WellFormed C ξ wf)

-- Hence ⟦ C ⟧ ≡ ξ is decided on the diagonal of the miter.

spec-miter-restriction : (C : Circuit n) (ξ : PathSum n k m) →
                         WellFormed ξ →
                         (⟦ C ⟧ ≋ ξ ⇔ Restriction-id (⟦ C † ⟧ ∘ᴾ ξ))
spec-miter-restriction C ξ wf = mk⇔
  (λ eq → Equivalence.to (miter-lemma-4-1 C ξ wf)
            (Equivalence.to (spec-miter-∘ C ξ) eq))
  (λ rid → Equivalence.from (spec-miter-∘ C ξ)
             (Equivalence.from (miter-lemma-4-1 C ξ wf) rid))


------------------------------------------------------------------------
-- The miter of two circuits

-- ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧, C₁ run first.

miter-∘ : (C₁ C₂ : Circuit n) →
          (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ (⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧) ≋ idPS)
miter-∘ C₁ C₂ = mk⇔
  (λ eq → Equivalence.to (spec-miter-∘ C₂ ⟦ C₁ ⟧)
            (≋-sym {ξ = ⟦ C₁ ⟧} {ζ = ⟦ C₂ ⟧} eq))
  (λ eq → ≋-sym {ξ = ⟦ C₂ ⟧} {ζ = ⟦ C₁ ⟧}
            (Equivalence.from (spec-miter-∘ C₂ ⟦ C₁ ⟧) eq))

-- No hypothesis is left for lemma 4.1: ⟦ C₁ ⟧ is an isometry.

miter-restriction : (C₁ C₂ : Circuit n) →
                    (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
                     Restriction-id (⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧))
miter-restriction C₁ C₂ = mk⇔
  (λ eq → Equivalence.to (spec-miter-restriction C₂ ⟦ C₁ ⟧ wf)
            (≋-sym {ξ = ⟦ C₁ ⟧} {ζ = ⟦ C₂ ⟧} eq))
  (λ rid → ≋-sym {ξ = ⟦ C₂ ⟧} {ζ = ⟦ C₁ ⟧}
             (Equivalence.from (spec-miter-restriction C₂ ⟦ C₁ ⟧ wf) rid))
  where
  wf : WellFormed ⟦ C₁ ⟧
  wf = Isometric⇒WellFormed ⟦ C₁ ⟧ (circuit-Isometric C₁)

-- The composed miter is the circuit C₁ ++ C₂ †, up to ≋.

miter-∘-++ : (C₁ C₂ : Circuit n) → (⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧) ≋ ⟦ C₁ ++ C₂ † ⟧
miter-∘-++ C₁ C₂ =
  ≋-sym {ξ = ⟦ C₁ ++ C₂ † ⟧} {ζ = ⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧} (⟦++⟧ C₁ (C₂ †))


------------------------------------------------------------------------
-- Prepending a circuit respects ≋

-- ⟦ D ++ C ⟧ is ⟦ C ⟧ ∘ ⟦ D ⟧ up to ≋ (⟦++⟧), and composition respects
-- ≋ on either side (PathSum.Compose.Laws), so an equivalence of C and
-- C′ carries over to D ++ C and D ++ C′: C and C′ now act on the
-- columns of D, which the composite reads path by path.

++-congˡ : (D C C′ : Circuit n) → ⟦ C ⟧ ≋ ⟦ C′ ⟧ →
           ⟦ D ++ C ⟧ ≋ ⟦ D ++ C′ ⟧
++-congˡ D C C′ eq =
  ≋-trans {ξ = ⟦ D ++ C ⟧} {ζ = ⟦ C ⟧ ∘ᴾ ⟦ D ⟧} {χ = ⟦ D ++ C′ ⟧}
    (⟦++⟧ D C)
    (≋-trans {ξ = ⟦ C ⟧ ∘ᴾ ⟦ D ⟧} {ζ = ⟦ C′ ⟧ ∘ᴾ ⟦ D ⟧}
             {χ = ⟦ D ++ C′ ⟧}
      (∘ᴾ-congˡ ⟦ C ⟧ ⟦ C′ ⟧ ⟦ D ⟧ eq)
      (≋-sym {ξ = ⟦ D ++ C′ ⟧} {ζ = ⟦ C′ ⟧ ∘ᴾ ⟦ D ⟧} (⟦++⟧ D C′)))

-- D can be cancelled again by prepending D†, which undoes it.

++-†-cancelˡ : (D C : Circuit n) → ⟦ D † ++ (D ++ C) ⟧ ≋ ⟦ C ⟧
++-†-cancelˡ D C =
  subst (λ E → ⟦ E ⟧ ≋ ⟦ C ⟧) (++-assoc (D †) D C) regrouped
  where
  regrouped : ⟦ (D † ++ D) ++ C ⟧ ≋ ⟦ C ⟧
  regrouped =
    ≋-trans {ξ = ⟦ (D † ++ D) ++ C ⟧} {ζ = ⟦ C ⟧ ∘ᴾ ⟦ D † ++ D ⟧}
            {χ = ⟦ C ⟧}
      (⟦++⟧ (D † ++ D) C)
      (≋-trans {ξ = ⟦ C ⟧ ∘ᴾ ⟦ D † ++ D ⟧} {ζ = ⟦ C ⟧ ∘ᴾ idPS}
               {χ = ⟦ C ⟧}
        (∘ᴾ-congʳ ⟦ C ⟧ ⟦ D † ++ D ⟧ idPS (†-inverseˡ D))
        (∘ᴾ-identityʳ ⟦ C ⟧))

++-cancelˡ : (D C C′ : Circuit n) → ⟦ D ++ C ⟧ ≋ ⟦ D ++ C′ ⟧ →
             ⟦ C ⟧ ≋ ⟦ C′ ⟧
++-cancelˡ D C C′ eq =
  ≋-trans {ξ = ⟦ C ⟧} {ζ = ⟦ D † ++ (D ++ C) ⟧} {χ = ⟦ C′ ⟧}
    (≋-sym {ξ = ⟦ D † ++ (D ++ C) ⟧} {ζ = ⟦ C ⟧} (++-†-cancelˡ D C))
    (≋-trans {ξ = ⟦ D † ++ (D ++ C) ⟧} {ζ = ⟦ D † ++ (D ++ C′) ⟧}
             {χ = ⟦ C′ ⟧}
      (++-congˡ (D †) (D ++ C) (D ++ C′) eq) (++-†-cancelˡ D C′))
