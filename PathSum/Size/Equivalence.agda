------------------------------------------------------------------------
-- Presentations of groups
--
-- A representation stands for its path-sum (for Amy, QPL 2018,
-- corollary 2.15)
--
-- PathSum.Size bounds the size of a representation R of the path-sum
-- of a circuit: a sparse phase and a linear form for each output.
-- That R represents ξ (Sparse.Represents) is a syntactic statement --
-- the phases agree modulo 2^M and the outputs coefficient by
-- coefficient -- so it is worth saying that it means what it should:
-- ξ and the path-sum psʳ k R that R stands for denote the same
-- operator (represents-≋, by PathSum.Congruence.≈-≋, the outputs
-- being needed only modulo 2).  At a circuit, ⟦ C ⟧ ≋ psʳ (norm C) R
-- for both gate sets (repᴷ-≋, repᶜ-≋).  So the small representation
-- is the path-sum, up to ≋, and not merely a polynomial close to it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Size.Equivalence (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
  renaming (_-_ to _-ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import PathSum.Base using (PathSum; out)
open import PathSum.Congruence M₀ using (≈-≋)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Linear using (liftᴸ)
open import PathSum.Polynomial using (_≈[_]_)
open import PathSum.Polynomial.Properties using (i∣0)

import Data.Integer.Properties as ℤP
import PathSum.Circuit
import PathSum.CRK.Circuit
import PathSum.Size
import PathSum.Size.Sparse

private
  M : ℕ
  M = suc (suc (suc M₀))

  module K = PathSum.CRK.Circuit M
  module Q = PathSum.Circuit M

open PathSum.Size.Sparse M using (Rep; forms; Represents; psʳ)
open PathSum.Size M using (repᴷ; repᴷ-represents; repᶜ; repᶜ-represents)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- A represented path-sum is its representation's

represents-≋ : (ξ : PathSum n k m) (R : Rep n m) → Represents ξ R →
               ξ ≋ psʳ k R
represents-≋ {k = k} ξ R (eqP , eqf) = ≈-≋ ξ (psʳ k R) outs eqP
  where
  outs : ∀ w → out ξ w ≈[ + 2 ] out (psʳ k R) w
  outs w γ = subst (λ z → (+ 2) ∣ (z -ℤ liftᴸ (forms R w) γ))
    (sym (eqf w γ))
    (subst ((+ 2) ∣_) (sym (ℤP.+-inverseʳ (liftᴸ (forms R w) γ))) i∣0)


------------------------------------------------------------------------
-- At circuits

repᴷ-≋ : (C : K.Circuit n) → K.⟦ C ⟧ ≋ psʳ (K.norm C) (repᴷ C)
repᴷ-≋ C = represents-≋ K.⟦ C ⟧ (repᴷ C) (repᴷ-represents C)

repᶜ-≋ : (C : Q.Circuit n) → Q.⟦ C ⟧ ≋ psʳ (Q.norm C) (repᶜ C)
repᶜ-≋ C = represents-≋ Q.⟦ C ⟧ (repᶜ C) (repᶜ-represents C)
