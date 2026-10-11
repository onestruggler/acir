------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the auxiliary theory (Figure 7) for the matrices on four
-- basis vectors
--
-- The completeness of Figure 7 for O₄(ℤ[1/√2]) is Theorem 4.4, which
-- the paper takes from the literature and this development takes as
-- a hypothesis.  Its soundness is checked here on the 4 × 4 matrices
-- of TwoQubit: each equation, at each choice of distinct indices, is
-- an equality of stored tries.  This pins down both the transcription
-- of Figure 7 and the reading of a word as the product of its
-- letters' matrices in the order written.
--
-- The words are spelled out at every call: the localisation relation
-- unfolds to an equation between operators, from which Agda cannot
-- recover them (Interpretation, performance discipline).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Soundness where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.TwoQubit using (by-triesY ; module BF)
open BF using (⟦_⟧Y)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics

private
  -- The generic equations, at every choice of distinct indices.
  a2-sound : ∀ a b → a ≢ b → ⟦ X a b • X a b ⟧Y ~ ⟦ ε {Gen 4} ⟧Y
  a2-sound ₀ ₁ _ = by-triesY (X ₀ ₁ • X ₀ ₁) (ε {Gen 4}) Eq.refl
  a2-sound ₀ ₂ _ = by-triesY (X ₀ ₂ • X ₀ ₂) (ε {Gen 4}) Eq.refl
  a2-sound ₀ ₃ _ = by-triesY (X ₀ ₃ • X ₀ ₃) (ε {Gen 4}) Eq.refl
  a2-sound ₁ ₀ _ = by-triesY (X ₁ ₀ • X ₁ ₀) (ε {Gen 4}) Eq.refl
  a2-sound ₁ ₂ _ = by-triesY (X ₁ ₂ • X ₁ ₂) (ε {Gen 4}) Eq.refl
  a2-sound ₁ ₃ _ = by-triesY (X ₁ ₃ • X ₁ ₃) (ε {Gen 4}) Eq.refl
  a2-sound ₂ ₀ _ = by-triesY (X ₂ ₀ • X ₂ ₀) (ε {Gen 4}) Eq.refl
  a2-sound ₂ ₁ _ = by-triesY (X ₂ ₁ • X ₂ ₁) (ε {Gen 4}) Eq.refl
  a2-sound ₂ ₃ _ = by-triesY (X ₂ ₃ • X ₂ ₃) (ε {Gen 4}) Eq.refl
  a2-sound ₃ ₀ _ = by-triesY (X ₃ ₀ • X ₃ ₀) (ε {Gen 4}) Eq.refl
  a2-sound ₃ ₁ _ = by-triesY (X ₃ ₁ • X ₃ ₁) (ε {Gen 4}) Eq.refl
  a2-sound ₃ ₂ _ = by-triesY (X ₃ ₂ • X ₃ ₂) (ε {Gen 4}) Eq.refl
  a2-sound ₀ ₀ p = ⊥-elim (p Eq.refl)
  a2-sound ₁ ₁ p = ⊥-elim (p Eq.refl)
  a2-sound ₂ ₂ p = ⊥-elim (p Eq.refl)
  a2-sound ₃ ₃ p = ⊥-elim (p Eq.refl)

  a3-sound : ∀ a b → a ≢ b → ⟦ H a b • H a b ⟧Y ~ ⟦ ε {Gen 4} ⟧Y
  a3-sound ₀ ₁ _ = by-triesY (H ₀ ₁ • H ₀ ₁) (ε {Gen 4}) Eq.refl
  a3-sound ₀ ₂ _ = by-triesY (H ₀ ₂ • H ₀ ₂) (ε {Gen 4}) Eq.refl
  a3-sound ₀ ₃ _ = by-triesY (H ₀ ₃ • H ₀ ₃) (ε {Gen 4}) Eq.refl
  a3-sound ₁ ₀ _ = by-triesY (H ₁ ₀ • H ₁ ₀) (ε {Gen 4}) Eq.refl
  a3-sound ₁ ₂ _ = by-triesY (H ₁ ₂ • H ₁ ₂) (ε {Gen 4}) Eq.refl
  a3-sound ₁ ₃ _ = by-triesY (H ₁ ₃ • H ₁ ₃) (ε {Gen 4}) Eq.refl
  a3-sound ₂ ₀ _ = by-triesY (H ₂ ₀ • H ₂ ₀) (ε {Gen 4}) Eq.refl
  a3-sound ₂ ₁ _ = by-triesY (H ₂ ₁ • H ₂ ₁) (ε {Gen 4}) Eq.refl
  a3-sound ₂ ₃ _ = by-triesY (H ₂ ₃ • H ₂ ₃) (ε {Gen 4}) Eq.refl
  a3-sound ₃ ₀ _ = by-triesY (H ₃ ₀ • H ₃ ₀) (ε {Gen 4}) Eq.refl
  a3-sound ₃ ₁ _ = by-triesY (H ₃ ₁ • H ₃ ₁) (ε {Gen 4}) Eq.refl
  a3-sound ₃ ₂ _ = by-triesY (H ₃ ₂ • H ₃ ₂) (ε {Gen 4}) Eq.refl
  a3-sound ₀ ₀ p = ⊥-elim (p Eq.refl)
  a3-sound ₁ ₁ p = ⊥-elim (p Eq.refl)
  a3-sound ₂ ₂ p = ⊥-elim (p Eq.refl)
  a3-sound ₃ ₃ p = ⊥-elim (p Eq.refl)

  c1-sound : ∀ a b → a ≢ b → ⟦ −1 a • X a b ⟧Y ~ ⟦ X a b • −1 b ⟧Y
  c1-sound ₀ ₁ _ = by-triesY (−1 ₀ • X ₀ ₁) (X ₀ ₁ • −1 ₁) Eq.refl
  c1-sound ₀ ₂ _ = by-triesY (−1 ₀ • X ₀ ₂) (X ₀ ₂ • −1 ₂) Eq.refl
  c1-sound ₀ ₃ _ = by-triesY (−1 ₀ • X ₀ ₃) (X ₀ ₃ • −1 ₃) Eq.refl
  c1-sound ₁ ₀ _ = by-triesY (−1 ₁ • X ₁ ₀) (X ₁ ₀ • −1 ₀) Eq.refl
  c1-sound ₁ ₂ _ = by-triesY (−1 ₁ • X ₁ ₂) (X ₁ ₂ • −1 ₂) Eq.refl
  c1-sound ₁ ₃ _ = by-triesY (−1 ₁ • X ₁ ₃) (X ₁ ₃ • −1 ₃) Eq.refl
  c1-sound ₂ ₀ _ = by-triesY (−1 ₂ • X ₂ ₀) (X ₂ ₀ • −1 ₀) Eq.refl
  c1-sound ₂ ₁ _ = by-triesY (−1 ₂ • X ₂ ₁) (X ₂ ₁ • −1 ₁) Eq.refl
  c1-sound ₂ ₃ _ = by-triesY (−1 ₂ • X ₂ ₃) (X ₂ ₃ • −1 ₃) Eq.refl
  c1-sound ₃ ₀ _ = by-triesY (−1 ₃ • X ₃ ₀) (X ₃ ₀ • −1 ₀) Eq.refl
  c1-sound ₃ ₁ _ = by-triesY (−1 ₃ • X ₃ ₁) (X ₃ ₁ • −1 ₁) Eq.refl
  c1-sound ₃ ₂ _ = by-triesY (−1 ₃ • X ₃ ₂) (X ₃ ₂ • −1 ₂) Eq.refl
  c1-sound ₀ ₀ p = ⊥-elim (p Eq.refl)
  c1-sound ₁ ₁ p = ⊥-elim (p Eq.refl)
  c1-sound ₂ ₂ p = ⊥-elim (p Eq.refl)
  c1-sound ₃ ₃ p = ⊥-elim (p Eq.refl)

  c5-sound : ∀ a b c → a ≢ b → a ≢ c → b ≢ c →
             ⟦ H a c • X b c ⟧Y ~ ⟦ X b c • H a b ⟧Y
  c5-sound ₀ ₁ ₂ _ _ _ = by-triesY (H ₀ ₂ • X ₁ ₂) (X ₁ ₂ • H ₀ ₁) Eq.refl
  c5-sound ₀ ₁ ₃ _ _ _ = by-triesY (H ₀ ₃ • X ₁ ₃) (X ₁ ₃ • H ₀ ₁) Eq.refl
  c5-sound ₀ ₂ ₁ _ _ _ = by-triesY (H ₀ ₁ • X ₂ ₁) (X ₂ ₁ • H ₀ ₂) Eq.refl
  c5-sound ₀ ₂ ₃ _ _ _ = by-triesY (H ₀ ₃ • X ₂ ₃) (X ₂ ₃ • H ₀ ₂) Eq.refl
  c5-sound ₀ ₃ ₁ _ _ _ = by-triesY (H ₀ ₁ • X ₃ ₁) (X ₃ ₁ • H ₀ ₃) Eq.refl
  c5-sound ₀ ₃ ₂ _ _ _ = by-triesY (H ₀ ₂ • X ₃ ₂) (X ₃ ₂ • H ₀ ₃) Eq.refl
  c5-sound ₁ ₀ ₂ _ _ _ = by-triesY (H ₁ ₂ • X ₀ ₂) (X ₀ ₂ • H ₁ ₀) Eq.refl
  c5-sound ₁ ₀ ₃ _ _ _ = by-triesY (H ₁ ₃ • X ₀ ₃) (X ₀ ₃ • H ₁ ₀) Eq.refl
  c5-sound ₁ ₂ ₀ _ _ _ = by-triesY (H ₁ ₀ • X ₂ ₀) (X ₂ ₀ • H ₁ ₂) Eq.refl
  c5-sound ₁ ₂ ₃ _ _ _ = by-triesY (H ₁ ₃ • X ₂ ₃) (X ₂ ₃ • H ₁ ₂) Eq.refl
  c5-sound ₁ ₃ ₀ _ _ _ = by-triesY (H ₁ ₀ • X ₃ ₀) (X ₃ ₀ • H ₁ ₃) Eq.refl
  c5-sound ₁ ₃ ₂ _ _ _ = by-triesY (H ₁ ₂ • X ₃ ₂) (X ₃ ₂ • H ₁ ₃) Eq.refl
  c5-sound ₂ ₀ ₁ _ _ _ = by-triesY (H ₂ ₁ • X ₀ ₁) (X ₀ ₁ • H ₂ ₀) Eq.refl
  c5-sound ₂ ₀ ₃ _ _ _ = by-triesY (H ₂ ₃ • X ₀ ₃) (X ₀ ₃ • H ₂ ₀) Eq.refl
  c5-sound ₂ ₁ ₀ _ _ _ = by-triesY (H ₂ ₀ • X ₁ ₀) (X ₁ ₀ • H ₂ ₁) Eq.refl
  c5-sound ₂ ₁ ₃ _ _ _ = by-triesY (H ₂ ₃ • X ₁ ₃) (X ₁ ₃ • H ₂ ₁) Eq.refl
  c5-sound ₂ ₃ ₀ _ _ _ = by-triesY (H ₂ ₀ • X ₃ ₀) (X ₃ ₀ • H ₂ ₃) Eq.refl
  c5-sound ₂ ₃ ₁ _ _ _ = by-triesY (H ₂ ₁ • X ₃ ₁) (X ₃ ₁ • H ₂ ₃) Eq.refl
  c5-sound ₃ ₀ ₁ _ _ _ = by-triesY (H ₃ ₁ • X ₀ ₁) (X ₀ ₁ • H ₃ ₀) Eq.refl
  c5-sound ₃ ₀ ₂ _ _ _ = by-triesY (H ₃ ₂ • X ₀ ₂) (X ₀ ₂ • H ₃ ₀) Eq.refl
  c5-sound ₃ ₁ ₀ _ _ _ = by-triesY (H ₃ ₀ • X ₁ ₀) (X ₁ ₀ • H ₃ ₁) Eq.refl
  c5-sound ₃ ₁ ₂ _ _ _ = by-triesY (H ₃ ₂ • X ₁ ₂) (X ₁ ₂ • H ₃ ₁) Eq.refl
  c5-sound ₃ ₂ ₀ _ _ _ = by-triesY (H ₃ ₀ • X ₂ ₀) (X ₂ ₀ • H ₃ ₂) Eq.refl
  c5-sound ₃ ₂ ₁ _ _ _ = by-triesY (H ₃ ₁ • X ₂ ₁) (X ₂ ₁ • H ₃ ₂) Eq.refl
  c5-sound ₀ ₀ _ p _ _ = ⊥-elim (p Eq.refl)
  c5-sound ₁ ₁ _ p _ _ = ⊥-elim (p Eq.refl)
  c5-sound ₂ ₂ _ p _ _ = ⊥-elim (p Eq.refl)
  c5-sound ₃ ₃ _ p _ _ = ⊥-elim (p Eq.refl)
  c5-sound ₀ _ ₀ _ q _ = ⊥-elim (q Eq.refl)
  c5-sound ₁ _ ₁ _ q _ = ⊥-elim (q Eq.refl)
  c5-sound ₂ _ ₂ _ q _ = ⊥-elim (q Eq.refl)
  c5-sound ₃ _ ₃ _ q _ = ⊥-elim (q Eq.refl)
  c5-sound _ ₀ ₀ _ _ r = ⊥-elim (r Eq.refl)
  c5-sound _ ₁ ₁ _ _ r = ⊥-elim (r Eq.refl)
  c5-sound _ ₂ ₂ _ _ r = ⊥-elim (r Eq.refl)
  c5-sound _ ₃ ₃ _ _ r = ⊥-elim (r Eq.refl)

  d2-sound : ∀ a b → a ≢ b → ⟦ −1 b • H a b ⟧Y ~ ⟦ H a b • X a b ⟧Y
  d2-sound ₀ ₁ _ = by-triesY (−1 ₁ • H ₀ ₁) (H ₀ ₁ • X ₀ ₁) Eq.refl
  d2-sound ₀ ₂ _ = by-triesY (−1 ₂ • H ₀ ₂) (H ₀ ₂ • X ₀ ₂) Eq.refl
  d2-sound ₀ ₃ _ = by-triesY (−1 ₃ • H ₀ ₃) (H ₀ ₃ • X ₀ ₃) Eq.refl
  d2-sound ₁ ₀ _ = by-triesY (−1 ₀ • H ₁ ₀) (H ₁ ₀ • X ₁ ₀) Eq.refl
  d2-sound ₁ ₂ _ = by-triesY (−1 ₂ • H ₁ ₂) (H ₁ ₂ • X ₁ ₂) Eq.refl
  d2-sound ₁ ₃ _ = by-triesY (−1 ₃ • H ₁ ₃) (H ₁ ₃ • X ₁ ₃) Eq.refl
  d2-sound ₂ ₀ _ = by-triesY (−1 ₀ • H ₂ ₀) (H ₂ ₀ • X ₂ ₀) Eq.refl
  d2-sound ₂ ₁ _ = by-triesY (−1 ₁ • H ₂ ₁) (H ₂ ₁ • X ₂ ₁) Eq.refl
  d2-sound ₂ ₃ _ = by-triesY (−1 ₃ • H ₂ ₃) (H ₂ ₃ • X ₂ ₃) Eq.refl
  d2-sound ₃ ₀ _ = by-triesY (−1 ₀ • H ₃ ₀) (H ₃ ₀ • X ₃ ₀) Eq.refl
  d2-sound ₃ ₁ _ = by-triesY (−1 ₁ • H ₃ ₁) (H ₃ ₁ • X ₃ ₁) Eq.refl
  d2-sound ₃ ₂ _ = by-triesY (−1 ₂ • H ₃ ₂) (H ₃ ₂ • X ₃ ₂) Eq.refl
  d2-sound ₀ ₀ p = ⊥-elim (p Eq.refl)
  d2-sound ₁ ₁ p = ⊥-elim (p Eq.refl)
  d2-sound ₂ ₂ p = ⊥-elim (p Eq.refl)
  d2-sound ₃ ₃ p = ⊥-elim (p Eq.refl)

  e2-sound : ∀ b c → b ≢ c → ⟦ H c b • X b c ⟧Y ~ ⟦ X b c • H b c ⟧Y
  e2-sound ₀ ₁ _ = by-triesY (H ₁ ₀ • X ₀ ₁) (X ₀ ₁ • H ₀ ₁) Eq.refl
  e2-sound ₀ ₂ _ = by-triesY (H ₂ ₀ • X ₀ ₂) (X ₀ ₂ • H ₀ ₂) Eq.refl
  e2-sound ₀ ₃ _ = by-triesY (H ₃ ₀ • X ₀ ₃) (X ₀ ₃ • H ₀ ₃) Eq.refl
  e2-sound ₁ ₀ _ = by-triesY (H ₀ ₁ • X ₁ ₀) (X ₁ ₀ • H ₁ ₀) Eq.refl
  e2-sound ₁ ₂ _ = by-triesY (H ₂ ₁ • X ₁ ₂) (X ₁ ₂ • H ₁ ₂) Eq.refl
  e2-sound ₁ ₃ _ = by-triesY (H ₃ ₁ • X ₁ ₃) (X ₁ ₃ • H ₁ ₃) Eq.refl
  e2-sound ₂ ₀ _ = by-triesY (H ₀ ₂ • X ₂ ₀) (X ₂ ₀ • H ₂ ₀) Eq.refl
  e2-sound ₂ ₁ _ = by-triesY (H ₁ ₂ • X ₂ ₁) (X ₂ ₁ • H ₂ ₁) Eq.refl
  e2-sound ₂ ₃ _ = by-triesY (H ₃ ₂ • X ₂ ₃) (X ₂ ₃ • H ₂ ₃) Eq.refl
  e2-sound ₃ ₀ _ = by-triesY (H ₀ ₃ • X ₃ ₀) (X ₃ ₀ • H ₃ ₀) Eq.refl
  e2-sound ₃ ₁ _ = by-triesY (H ₁ ₃ • X ₃ ₁) (X ₃ ₁ • H ₃ ₁) Eq.refl
  e2-sound ₃ ₂ _ = by-triesY (H ₂ ₃ • X ₃ ₂) (X ₃ ₂ • H ₃ ₂) Eq.refl
  e2-sound ₀ ₀ p = ⊥-elim (p Eq.refl)
  e2-sound ₁ ₁ p = ⊥-elim (p Eq.refl)
  e2-sound ₂ ₂ p = ⊥-elim (p Eq.refl)
  e2-sound ₃ ₃ p = ⊥-elim (p Eq.refl)

-- Every equation of Figure 7 at N = 4 holds of the matrices.
sound : ∀ {u t} → 4 G, u === t → ⟦ u ⟧Y ~ ⟦ t ⟧Y
sound a1* = by-triesY (−1 ₀ • −1 ₀) ε Eq.refl
sound (a2 {a = a} {b = b} p) = a2-sound a b p
sound (a3 {a = a} {b = b} p) = a3-sound a b p
sound b1* = by-triesY (−1 ₀ • −1 ₁) (−1 ₁ • −1 ₀) Eq.refl
sound b4* = by-triesY (−1 ₁ • H ₀ ₂) (H ₀ ₂ • −1 ₁) Eq.refl
sound b6* = by-triesY (H ₀ ₁ • H ₂ ₃) (H ₂ ₃ • H ₀ ₁) Eq.refl
sound (c1 {a = a} {b = b} p) = c1-sound a b p
sound (c5 {a = a} {b = b} {c = c} p q r) = c5-sound a b c p q r
sound (d2 {a = a} {b = b} p) = d2-sound a b p
sound d3* = by-triesY
  (H ₀ ₁ • H ₀ ₂ • H ₁ ₃ • H ₀ ₁ • −1 ₀ • −1 ₁ • H ₀ ₂ • H ₁ ₃)
  (H ₀ ₂ • H ₁ ₃ • H ₀ ₁ • −1 ₀ • −1 ₁ • H ₀ ₂ • H ₁ ₃ • H ₀ ₁) Eq.refl
sound (e2* {b = b} {c = c} p) = e2-sound b c p
