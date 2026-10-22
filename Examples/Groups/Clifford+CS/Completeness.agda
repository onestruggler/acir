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
--   * two wires: the same on four indices (TwoQubit), the decoding
--     respecting the relations and inverting the encoding (the
--     analogues of Clément's Lemmas 7.5 and 7.4) by derivations on two
--     wires (TwoQubit.Decoding, Lemmas.TwoWire, Lemmas.TwoWireMacro) —
--     proved;
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
-- holds.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Completeness where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ)
import Data.Nat as ℕ
open import Data.Product using (_,_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄₊)

open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
open import Normalization.StarPresentation using (module MonoidSem)

open import Examples.Groups.Clifford+CS.Semantics using (Scaled-monoid ; _~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ ; ~-⟦⟧ᴱ)
open import Examples.Groups.Clifford+CS.Soundness using (axiom-soundᴱ)

import Examples.Groups.Clifford+CS.ZeroQubit as ZeroQubit
import Examples.Groups.Clifford+CS.OneQubit as OneQubit
import Examples.Groups.Clifford+CS.TwoQubit as TwoQubit
import Examples.Groups.Clifford+CS.TwoQubit.Decoding as Decoding
import Examples.Groups.Clifford+CS.ThreeQubit as ThreeQubit
import Examples.Groups.Clifford+CS.Weakening as Weakening

------------------------------------------------------------------------
-- Completeness at a width

open import Examples.Groups.Clifford+CS.SemanticSteps using (Complete) public

-- The widths proved.
complete₀ : Complete 0
complete₀ = ZeroQubit.complete

complete₁ : Complete 1
complete₁ = OneQubit.complete

complete₂ : Complete 2
complete₂ = TwoQubit.Lemma-7-6.complete Decoding.lemma-7-4 Decoding.lemma-7-5

complete₃ : Complete 3
complete₃ = ThreeQubit.complete

-- Every width up to three.
complete≤₃ : ∀ {n} → n ℕ.≤ 3 → Complete n
complete≤₃ ℕ.z≤n                         = complete₀
complete≤₃ (ℕ.s≤s ℕ.z≤n)                 = complete₁
complete≤₃ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))         = complete₂
complete≤₃ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) = complete₃

-- And on the bottom wires of any wider circuit.
complete≤₃↓ : ∀ {n} k → n ℕ.≤ 3 → ∀ {w v : Circuit n} →
              ⟦ w ⟧ ~ ⟦ v ⟧ → (n ℕ.+ k) ⊢ w ↓ᵏ k ≈ v ↓ᵏ k
complete≤₃↓ k le e = Weakening.weaken k (complete≤₃ le e)

------------------------------------------------------------------------
-- The theorem

-- With soundness, completeness at a width makes the rules a
-- presentation of their image there.
subpresentation : ∀ n → Complete n → (n VRel,_===_) IsSubMonoidPresentationOf Scaled-monoid n
subpresentation n complete = record
  { ⟦_⟧  = MS.⟦_⟧
  ; mono = record
    { isMonoidHomomorphism = MS.Cong.isMonoidHomomorphism axiom-soundᴱ
    ; injective            = λ {w} {v} e → complete {w} {v} (~-⟦⟧ᴱ {w = w} {v} e)
    }
  }
  where
  module MS = MonoidSem (n VRel,_===_) (Monoid.setoid (Scaled-monoid n))
                        (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ)

-- So up to three wires the rules present their image.
subpresentation≤₃ : ∀ {n} → n ℕ.≤ 3 → (n VRel,_===_) IsSubMonoidPresentationOf Scaled-monoid n
subpresentation≤₃ {n} n≤3 = subpresentation n (complete≤₃ n≤3)

-- Every width, given completeness from four wires on.
module Theorem (above : ∀ k → Complete (₄₊ k)) where

  completeness : ∀ n → Complete n
  completeness ₀      = complete₀
  completeness ₁      = complete₁
  completeness ₂      = complete₂
  completeness ₃      = complete₃
  completeness (₄₊ k) = above k
