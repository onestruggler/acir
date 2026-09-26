------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpreter's result is the circuit's path-sum, up to ≋ (for
-- Amy, QPL 2018, corollary 2.15)
--
-- PathSum.Size.Interpreter proves that the sparse interpreter's result
-- denotes ⟦ C ⟧ (Denotes: the right number of path variables, the
-- phase modulo 2^M and the outputs).  By
-- PathSum.Size.Equivalence.represents-≋ that means what it should: the
-- path-sum the result stands for, psʳ (norm C) R, denotes the same
-- operator as ⟦ C ⟧ (denotes-≋).  So for both gate sets, compacted or
-- not, the computed representation is the path-sum of the circuit up
-- to ≋ (interpᴷ-≋, compactᴷ-≋, interpᶜ-≋, compactᶜ-≋).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Size.Interpreter.Equivalence (M₀ : ℕ) where

open import Data.Product.Base using (∃; proj₁; proj₂)

open import PathSum.Base using (PathSum)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Size.Equivalence M₀ using (represents-≋)

import PathSum.Circuit
import PathSum.CRK.Circuit
import PathSum.Size.Interpreter
import PathSum.Size.Interpreter.Clifford
import PathSum.Size.Sparse

private
  M : ℕ
  M = suc (suc (suc M₀))

  module K = PathSum.CRK.Circuit M
  module Q = PathSum.Circuit M

open PathSum.Size.Sparse M using (Rep; psʳ)
open PathSum.Size.Interpreter M using
  (Denotes; denotes; interpᴷ; interpᴷ-correct; compactᴷ;
   compactᴷ-correct)
open PathSum.Size.Interpreter.Clifford M using
  (interpᶜ; interpᶜ-correct; compactᶜ; compactᶜ-correct)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- A denoted path-sum is its representation's

denotes-≋ : (ξ : PathSum n k m) (p : ∃ (Rep n)) → Denotes ξ p →
            ξ ≋ psʳ k (proj₂ p)
denotes-≋ ξ _ (denotes R r) = represents-≋ ξ R r


------------------------------------------------------------------------
-- At circuits

interpᴷ-≋ : (C : K.Circuit n) → K.⟦ C ⟧ ≋ psʳ (K.norm C) (proj₂ (interpᴷ C))
interpᴷ-≋ C = denotes-≋ K.⟦ C ⟧ (interpᴷ C) (interpᴷ-correct C)

compactᴷ-≋ : (C : K.Circuit n) →
             K.⟦ C ⟧ ≋ psʳ (K.norm C) (proj₂ (compactᴷ C))
compactᴷ-≋ C = denotes-≋ K.⟦ C ⟧ (compactᴷ C) (compactᴷ-correct C)

interpᶜ-≋ : (C : Q.Circuit n) → Q.⟦ C ⟧ ≋ psʳ (Q.norm C) (proj₂ (interpᶜ C))
interpᶜ-≋ C = denotes-≋ Q.⟦ C ⟧ (interpᶜ C) (interpᶜ-correct C)

compactᶜ-≋ : (C : Q.Circuit n) →
             Q.⟦ C ⟧ ≋ psʳ (Q.norm C) (proj₂ (compactᶜ C))
compactᶜ-≋ C = denotes-≋ Q.⟦ C ⟧ (compactᶜ C) (compactᶜ-correct C)
