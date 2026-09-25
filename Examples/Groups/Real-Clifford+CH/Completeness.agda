------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the real-Clifford+CH equational theory (Clément,
-- Theorem 8.9), assembled from its parts
--
-- The theorem: two n-qubit circuits with the same matrix are equal in
-- QC.  The paper proves it width by width — trivially on 0 qubits, by
-- the normal form of Lemma 7.1 on one, by the back-and-forth encoding
-- into the 1- and 2-level matrices on two (Lemma 7.6), and by the
-- back-and-forth encoding into the index-4 subgroup P (Section 8) on
-- three or more.
--
-- What is proved here outright: soundness (Soundness), the width-0 and
-- width-1 cases, and the shape of the argument at every other width
-- (BackAndForth).  What the paper takes from the literature or proves
-- in its appendix appears as hypotheses:
--
--   * Theorem 4.4, completeness of Figure 7 for the matrices on four
--     basis vectors — for two qubits; Figure 7 is sound for those
--     matrices (Auxiliary.Soundness), and Lemmas 7.4 and 7.5 of
--     Appendix C are proved (TwoQubit.Decoding);
--   * for n ≥ 3, with the generators P and Figure 8, the encoding and
--     the decoding of Definitions 8.2 and 8.3 all defined (Section8),
--     and the encoding proved to preserve the semantics at every width
--     (EncodingSemantics): the completeness of Figure 8 (Theorem 4.10,
--     Appendix A) and Lemmas 8.7 and 8.8 (Appendix E).  Checks8
--     decides the soundness of Figure 8 on three qubits.
--
-- Theorem 4.10 is in fact proved from Theorem 4.4 at the width of P
-- (Auxiliary.Theorem410Proof), and `Theorem-8-9′` below takes that
-- instead: its hypotheses are Theorem 4.4 and Lemmas 8.7 and 8.8.
--
-- The presented monoid is then a sub-monoid of the 2ⁿ × 2ⁿ matrices
-- over ℤ[1/√2] at every width: the paper's completeness theorem in the
-- form the rest of this library states such results.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Completeness where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Level using (Level ; suc ; 0ℓ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃₊)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
open import Normalization.StarPresentation using (module MonoidSem)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Soundness using (axiom-soundᴱ)

import Examples.Groups.Real-Clifford+CH.EncodingSemantics as EncodingSemantics
import Examples.Groups.Real-Clifford+CH.OneQubit as OneQubit
import Examples.Groups.Real-Clifford+CH.Section8 as Section8
import Examples.Groups.Real-Clifford+CH.TwoQubit as TwoQubit
import Examples.Groups.Real-Clifford+CH.TwoQubit.Decoding as Decoding
open TwoQubit.BF using () renaming (⟦_⟧Y to ⟦_⟧Y₂)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410Proof as T410

------------------------------------------------------------------------
-- Width 0: there is one circuit

-- Every circuit on no wires is the empty one, there being no generator
-- to write.
zero-wires : (w : Circuit 0) → 0 ⊢ w ≈ ε
zero-wires [ gate₀ () ]ʷ
zero-wires ε       = PB.refl
zero-wires (w • v) =
  PB.trans (PB.cong (zero-wires w) (zero-wires v)) PB.left-unit

------------------------------------------------------------------------
-- Theorem 8.9

module Theorem-8-9
  -- Two qubits: Theorem 4.4.
  (theorem-4-4 : ∀ {u t : Word (G.Gen 4)} → ⟦ u ⟧Y₂ ~ ⟦ t ⟧Y₂ →
                 PB._≈_ (4 G.G,_===_) u t)
  -- Three qubits and more: Section 8, for each k with n = k + 3.
  (theorem-4-10 : ∀ k → Section8.Theorem-4-10 k)
  (lemma-8-8    : ∀ k → Section8.Lemma-8-8 k)
  (lemma-8-7    : ∀ k → Section8.Lemma-8-7 k)
  where

  private
    module L76 = TwoQubit.Lemma-7-6 theorem-4-4 Decoding.lemma-7-4 Decoding.lemma-7-5
    module S8 (k : ℕ) = Section8.Complete k (theorem-4-10 k) (EncodingSemantics.e-sem k) (lemma-8-8 k) (lemma-8-7 k)

  -- Two circuits with the same matrix over ℤ[1/√2] are equal in QC.
  completeness : ∀ n {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → n ⊢ w ≈ v
  completeness ₀      {w} {v} _ = PB.trans (zero-wires w) (PB.sym (zero-wires v))
  completeness ₁              = OneQubit.complete
  completeness ₂              = L76.complete
  completeness (₃₊ k)         = S8.complete k

  -- With soundness (Proposition 3.1): QC ⊢ C₁ = C₂ iff ⟦ C₁ ⟧ = ⟦ C₂ ⟧,
  -- that is, Figure 4 presents its image, a sub-monoid of the matrices
  -- over ℤ[1/√2], at every width.  The interpretation is the library's
  -- reading through the monoid, which is ⟦_⟧ (Interpretation.⟦⟧ᴱ-def).
  subpresentation : ∀ n → (n VRel,_===_) IsSubMonoidPresentationOf Scaled-monoid n
  subpresentation n = record
    { ⟦_⟧  = MS.⟦_⟧
    ; mono = record
      { isMonoidHomomorphism = MS.Cong.isMonoidHomomorphism axiom-soundᴱ
      ; injective            = λ {w} {v} e → completeness n {w} {v} (~-⟦⟧ᴱ {w = w} {v} e)
      }
    }
    where
    module MS = MonoidSem (n VRel,_===_) (Monoid.setoid (Scaled-monoid n))
                          (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ)

------------------------------------------------------------------------
-- Theorem 8.9 with Theorem 4.10 proved
--
-- Appendix A's Theorem 4.10 — Figure 8 complete for the alphabet P — is
-- a theorem here (Auxiliary.Theorem410Proof: the Reidemeister–Schreier
-- method, both of its conditions derived from Figure 10's (65), which
-- Auxiliary.Eq65H proves), given completeness of Figure 7 at the width
-- of P.  That is how the paper obtains it: its Theorem 4.4, taken from
-- the literature, is the completeness of Figure 7 for the matrices on
-- any number of basis vectors.  So what is left as hypotheses is that
-- imported theorem, at two qubits and at every larger width, and
-- Lemmas 8.7 and 8.8 of Appendix E.

module Theorem-8-9′
  (theorem-4-4  : ∀ {u t : Word (G.Gen 4)} → ⟦ u ⟧Y₂ ~ ⟦ t ⟧Y₂ →
                  PB._≈_ (4 G.G,_===_) u t)
  (theorem-4-4ₙ : ∀ k → T410.Theorem-4-4 k)
  (lemma-8-8    : ∀ k → Section8.Lemma-8-8 k)
  (lemma-8-7    : ∀ k → Section8.Lemma-8-7 k)
  where

  open Theorem-8-9 theorem-4-4 (λ k → T410.theorem-4-10 k (theorem-4-4ₙ k)) lemma-8-8 lemma-8-7
    public using (completeness ; subpresentation)
