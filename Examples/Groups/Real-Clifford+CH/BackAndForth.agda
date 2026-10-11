------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness by a back-and-forth encoding (Clément, Sections 7.2 and 8)
--
-- The paper proves completeness on n ≥ 2 qubits by translating
-- circuits into an auxiliary language — words over 1- and 2-level
-- matrices with a known complete equational theory — and back:
--
--   * an encoding E of circuits as words, preserving the semantics;
--   * a decoding D of words as circuits, a monoid homomorphism that
--     respects the auxiliary theory (Lemmas 7.5 and 8.8) and inverts
--     the encoding up to QC (Lemmas 7.4 and 8.7);
--   * completeness of the auxiliary theory (Theorems 4.4 and 4.10).
--
-- Then ⟦C₁⟧ = ⟦C₂⟧ gives ⟦E C₁⟧ = ⟦E C₂⟧, hence E C₁ ≈ E C₂ in the
-- auxiliary theory, hence D (E C₁) = D (E C₂) in QC, hence C₁ = C₂.
--
-- This module is that argument, once, over an arbitrary auxiliary
-- presentation.  The middle two steps are exactly the library's
-- simplified Reidemeister–Schreier engine (Normalization.Reidemeister-
-- Schreier.Star-Injective-Simplified): a monoid map (E ʷ) with a
-- retraction (D ʷ) that respects the target's relations is injective
-- modulo the presentations.  The two-qubit instance is TwoQubit; the
-- general instance, whose auxiliary theory is the paper's Figure 8,
-- is taken as data in Completeness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics

module Examples.Groups.Real-Clifford+CH.BackAndForth
  (n : ℕ)
  {Y : Set} (Δ : WRel Y)              -- the auxiliary presentation
  (⟦_⟧ʸ : Y → Scaled n)               -- the matrices of its generators
  where

open import Algebra.Bundles using (Monoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Presentation.Base as PB
open import Normalization.Reidemeister-Schreier
  using (module Star-Injective-Simplified)

open import Examples.Groups.Real-Clifford+CH.Interpretation

------------------------------------------------------------------------
-- The semantics of auxiliary words: the product of the generators'
-- matrices, in the order written (Definition 4.3)

⟦_⟧Y : Word Y → Scaled n
⟦_⟧Y = E.⟦_⟧
  where
  open import Normalization.StarInterp Δ
  module E = Extend (Scaled-monoid n) ⟦_⟧ʸ

open PB Δ using () renaming (_≈_ to _≈ʸ_)

-- Circuits read through the monoid (Interpretation.Ext): the reading
-- under which ⟦ w • v ⟧ is ⟦ w ⟧ ∙ ⟦ v ⟧ on the nose; it is ⟦_⟧.
private
  ⟦_⟧ᴱ : Circuit n → Scaled n
  ⟦_⟧ᴱ = Ext.⟦_⟧ᴱ n

------------------------------------------------------------------------
-- The argument

module Complete
  (complete-Y : ∀ {u t : Word Y} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → u ≈ʸ t)  -- Theorem 4.4 / 4.10
  (e     : Gen n → Word Y)                                    -- the encoding, on generators
  (e-sem : ∀ g → ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧)                       -- it preserves the semantics
  (d     : Y → Circuit n)                                     -- the decoding, on generators
  (d-wd  : ∀ {u t} → Δ u t → n ⊢ (d ʷ) u ≈ (d ʷ) t)            -- Lemma 7.5 / 8.8
  (d∘e   : ∀ g → n ⊢ [ g ]ʷ ≈ (d ʷ) (e g))                    -- Lemma 7.4 / 8.7
  where

  -- The encoding of a whole circuit preserves the semantics: both
  -- sides are monoid homomorphisms.
  eʷ-sem : ∀ (w : Circuit n) → ⟦ (e ʷ) w ⟧Y ~ ⟦ w ⟧ᴱ
  eʷ-sem [ g ]ʷ  = Eq.subst (⟦ e g ⟧Y ~_) (Eq.sym (⟦⟧ᴱ-def [ g ]ʷ)) (e-sem g)
  eʷ-sem ε       = ~-refl ε∙
  eʷ-sem (w • v) =
    ∙-cong {s = ⟦ (e ʷ) w ⟧Y} {s' = ⟦ w ⟧ᴱ} {t = ⟦ (e ʷ) v ⟧Y} {t' = ⟦ v ⟧ᴱ}
           (eʷ-sem w) (eʷ-sem v)

  -- The encoding is injective modulo the two theories: Reidemeister–
  -- Schreier with the decoding as retraction.
  private
    module RS = Star-Injective-Simplified (n VRel,_===_) Δ
    module R  = RS.Reidemeister-Schreier-Simplified e d d-wd d∘e

  -- Two circuits with the same matrix are equal in QC.
  complete : ∀ {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → n ⊢ w ≈ v
  complete {w} {v} eq =
    R.fʷ-inj (complete-Y {u = (e ʷ) w} {t = (e ʷ) v}
      (~-trans {s = ⟦ (e ʷ) w ⟧Y} {t = ⟦ w ⟧ᴱ} {u = ⟦ (e ʷ) v ⟧Y} (eʷ-sem w)
        (~-trans {s = ⟦ w ⟧ᴱ} {t = ⟦ v ⟧ᴱ} {u = ⟦ (e ʷ) v ⟧Y} (⟦⟧ᴱ-~ {w = w} {v} eq)
          (~-sym {s = ⟦ (e ʷ) v ⟧Y} {t = ⟦ v ⟧ᴱ} (eʷ-sem v)))))
