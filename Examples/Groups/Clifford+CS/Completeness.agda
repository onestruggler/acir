------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the Clifford+CS equational theory, as far as it goes
--
-- The analogue of Clément's Theorem 8.9 for Clifford+CS circuits: two
-- n-qubit circuits with the same matrix over ℤ[½,i] are equal by the
-- rules of Syntactics.  The proof goes width by width, each width by
-- the back-and-forth argument (BackAndForth) with an auxiliary language
-- whose theory is complete:
--
--   * no wire and one wire: the one- and two-level words on one and two
--     indices, with the complete theory of Bian and Selinger
--     (Clifford+CS-TwoLevel); the decodings of their relations are
--     derived from the rules (ZeroQubit, OneQubit, Lemmas.OneWire) —
--     proved;
--   * two wires: the same on four indices (TwoQubit); the encoding, the
--     decoding and the semantics of the encoding are in place, and the
--     two lemmas of the argument — the decoding respects the relations,
--     and inverts the encoding (the analogues of Clément's Lemmas 7.5
--     and 7.4) — are hypotheses here;
--   * three wires: Bian and Selinger's 3-qubit Clifford+CS circuits,
--     whose relations are the rules here (ThreeQubit), with their
--     completeness theorem (Clifford+CS-3qubit) — proved;
--   * four wires and more: the analogue of Clément's Section 8 —
--     circuits there have determinant 1, so the auxiliary language is a
--     generating set of the determinant-one subgroup of U_{2ⁿ}(ℤ[½,i]),
--     with an encoding by Gray codes and a decoding into multi-
--     controlled gates — is not done; completeness there is a
--     hypothesis.  (The rules of Syntactics are those of three qubits;
--     Clément's theory needs a schema on every width from five on, and
--     the Clifford+CS one presumably will too.)
--
-- With soundness, the rules present their image, a sub-monoid of the
-- 2ⁿ × 2ⁿ matrices over ℤ[½,i], at every width where completeness
-- holds.  Every gate has an inverse word, so the image is a group, the
-- Clifford+CS operators on n qubits, and the rules present it as one
-- (presentationᴳ; outright on 0, 1 and 3 qubits).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Completeness where

open import Algebra.Bundles using (Group ; Monoid)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Level using (0ℓ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄₊)

open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_ ; _IsPresentationOf_)
open import Presentation.Units using (module Generated ; Units ; units-subpresentation)
open import Normalization.StarPresentation using (module MonoidSem)

open import Examples.Groups.Clifford+CS.Semantics using (Scaled-monoid ; _~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ ; ~-⟦⟧ᴱ)
open import Examples.Groups.Clifford+CS.Soundness using (axiom-soundᴱ)

import Examples.Groups.Clifford+CS.ZeroQubit as ZeroQubit
import Examples.Groups.Clifford+CS.OneQubit as OneQubit
import Examples.Groups.Clifford+CS.TwoQubit as TwoQubit
import Examples.Groups.Clifford+CS.ThreeQubit as ThreeQubit

------------------------------------------------------------------------
-- Completeness at a width

Complete : ℕ → Set
Complete n = ∀ {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → n ⊢ w ≈ v

-- The widths proved.
complete₀ : Complete 0
complete₀ = ZeroQubit.complete

complete₁ : Complete 1
complete₁ = OneQubit.complete

complete₃ : Complete 3
complete₃ = ThreeQubit.complete

-- Two wires, given the two lemmas of the back-and-forth argument.
complete₂ : TwoQubit.Lemma-7-4 → TwoQubit.Lemma-7-5 → Complete 2
complete₂ l74 l75 = TwoQubit.Lemma-7-6.complete l74 l75

------------------------------------------------------------------------
-- The theorem

private
  -- The reading as a monoid homomorphism, at each width.
  module MS (n : ℕ) = MonoidSem (n VRel,_===_) (Monoid.setoid (Scaled-monoid n))
                                (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ)

  -- The group it generates (Presentation.Units).
  module G (n : ℕ) = Generated (grouplike {n}) {M = Scaled-monoid n} (MS.⟦_⟧ n)
                               (MS.Cong.isMonoidHomomorphism n axiom-soundᴱ)

  injective : ∀ n → Complete n → ∀ {w v} → MS.⟦ n ⟧ w ~ MS.⟦ n ⟧ v → n ⊢ w ≈ v
  injective n complete {w} {v} e = complete {w} {v} (~-⟦⟧ᴱ {w = w} {v} e)

-- With soundness, completeness at a width makes the rules a
-- presentation of their image there.
subpresentation : ∀ n → Complete n → (n VRel,_===_) IsSubMonoidPresentationOf Scaled-monoid n
subpresentation n complete = record
  { ⟦_⟧  = MS.⟦_⟧ n
  ; mono = record
    { isMonoidHomomorphism = MS.Cong.isMonoidHomomorphism n axiom-soundᴱ
    ; injective            = injective n complete
    }
  }

------------------------------------------------------------------------
-- The group versions

-- Every gate has an inverse word (Syntactics.grouplike), so the image is
-- a group: the Clifford+CS operators on n qubits, the circuits compared
-- by their matrices.  Soundness alone makes it a group.
CliffordCS : ℕ → Group 0ℓ 0ℓ
CliffordCS n = G.group n

-- Completeness at a width makes the rules a presentation of it there,
presentationᴳ : ∀ n → Complete n → (n VRel,_===_) IsPresentationOf CliffordCS n
presentationᴳ n complete = G.presentation n (injective n complete)

-- The widths proved.
presentation₀ : (0 VRel,_===_) IsPresentationOf CliffordCS 0
presentation₀ = presentationᴳ 0 complete₀

presentation₁ : (1 VRel,_===_) IsPresentationOf CliffordCS 1
presentation₁ = presentationᴳ 1 complete₁

presentation₃ : (3 VRel,_===_) IsPresentationOf CliffordCS 3
presentation₃ = presentationᴳ 3 complete₃

-- and a sub-presentation of the group of invertible scaled operators.
subpresentationᵁ : ∀ n → Complete n → (n VRel,_===_) IsSubPresentationOf Units (Scaled-monoid n)
subpresentationᵁ n complete =
  units-subpresentation {M = Scaled-monoid n} (subpresentation n complete) grouplike

-- Every width, given the two-qubit lemmas and completeness from four
-- wires on.
module Theorem
  (lemma-7-4 : TwoQubit.Lemma-7-4)
  (lemma-7-5 : TwoQubit.Lemma-7-5)
  (above     : ∀ k → Complete (₄₊ k))
  where

  completeness : ∀ n → Complete n
  completeness ₀      = complete₀
  completeness ₁      = complete₁
  completeness ₂      = complete₂ lemma-7-4 lemma-7-5
  completeness ₃      = complete₃
  completeness (₄₊ k) = above k

  presentation : ∀ n → (n VRel,_===_) IsPresentationOf CliffordCS n
  presentation n = presentationᴳ n (completeness n)
