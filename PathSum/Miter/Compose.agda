------------------------------------------------------------------------
-- Presentations of groups
--
-- The miter as a composite of path-sums, for circuits over {H , S , CZ}
-- (Amy, QPL 2018, section 3)
--
-- Section 3: "the verification question we're generally concerned with
-- is given a circuit C and path-sum ξ, is ⟦C⟧ ≡ ξ?  From an automated
-- perspective it is simpler to instead check that the path-sum miter
-- ⟦C†⟧ ∘ ξ is the identity transformation."  PathSum.Miter proved this
-- on the columns of ξ (spec-miter); here it is proved of the composite
-- itself, formed by definition 2.6 (PathSum.Compose's _∘ᴾ_):
--
--    ⟦ C ⟧ ≋ ξ  ⇔  (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS                 (spec-miter-∘)
--
-- for every path-sum ξ, well formed or not.  The composite's
-- normalisation is the one definition 2.6 gives it, k + norm (C †),
-- and nothing is adjusted.  The proof: the columns of ⟦ C † ⟧ ∘ᴾ ξ are
-- C† applied to the columns of ξ (amp-∘ᴾ, from
-- PathSum.Compose.Apply's ∘ᴾ-applyᴳ at the gate model of
-- PathSum.Compose.Clifford), and spec-miter says when those are the
-- basis columns, scaled; the identity's columns are the basis columns
-- (PathSum.Compose.Laws's amp-idPS-δ), and norm (C †) = norm C
-- (PathSum.Adjoint).
--
-- Lemma 4.1 at the miter.  If ξ is WellFormed, so is ⟦ C † ⟧ ∘ᴾ ξ,
-- since ⟦ C † ⟧ is an isometry (PathSum.Unitarity) and composing
-- after an isometry keeps WellFormed (PathSum.Compose.WellFormed's
-- WellFormed-∘).  Then the miter is the identity exactly when its
-- isometry restriction is (miter-lemma-4-1), and so ⟦ C ⟧ ≋ ξ can be
-- read off the diagonal of the miter alone (spec-miter-restriction).
-- The paper notes that lemma 4.1 needs well-formedness; the hypothesis
-- is kept here, on ξ.
--
-- For two circuits the miter is ⟦ C₂ † ⟧ ∘ᴾ ⟦ C₁ ⟧, C₁ run first:
-- ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ exactly when it is the identity (miter-∘), exactly
-- when its restriction is (miter-restriction; no hypothesis is left,
-- ⟦ C₁ ⟧ being an isometry), and it is ≋ to the single circuit
-- C₁ ++ C₂ † (miter-∘-++, from PathSum.Compose.Clifford's ⟦++⟧), which
-- is the form PathSum.Miter.miter uses.
--
-- Composition also settles what PathSum.Miter left open: prepending a
-- circuit respects ≋ (++-congˡ), since ⟦ D ++ C ⟧ ≋ ⟦ C ⟧ ∘ᴾ ⟦ D ⟧ and
-- composition respects ≋ on either side (PathSum.Compose.Laws); and
-- prepending D† cancels D (++-†-cancelˡ), so prepending also reflects
-- ≋ (++-cancelˡ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Miter.Compose (M₀ : ℕ) where

open import Data.List.Base using (_++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (sym; trans; cong; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M using (_†; norm-†)
open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.Circuit M using (Circuit; norm; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; applyᴬ; prop-2-10)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Apply M₀ using (∘ᴾ-applyᴳ)
open import PathSum.Compose.Clifford M₀ using
  (cliffordGates; applyᴳ; applyᴳ≡applyᴬ; ⟦++⟧)
open import PathSum.Compose.Laws M₀ using
  (amp-idPS-δ; ∘ᴾ-congˡ; ∘ᴾ-congʳ; ∘ᴾ-identityʳ)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-∘)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; ≋-sym; ≋-trans)
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id; lemma-4-1)
open import PathSum.Miter M₀ using (spec-miter; †-inverseˡ)
open import PathSum.PartialIsometry M₀ using (Isometric⇒WellFormed)
open import PathSum.Unitarity M₀ using (circuit-Isometric)

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
  ∘ᴾ-applyᴳ cliffordGates ξ ⟦ D ⟧ D
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
