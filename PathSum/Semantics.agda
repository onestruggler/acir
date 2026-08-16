------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic interface a path-sum calculus is required to satisfy
--
-- The denotation of a path-sum is an exponential sum of complex
-- numbers, which is outside the scope of this development.  Section
-- 4.3 uses that denotation only through two results proved earlier in
-- the paper -- the correctness of the rewrite rules (proposition 3.1)
-- and the destructive-interference criterion (lemma 4.2) -- so those,
-- together with the fact that equivalence of path-sums is an
-- equivalence relation, are collected here as the fields of a record.
-- Everything in PathSum.Clifford is proved relative to such a record.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Semantics (M : ℕ) where

open import Data.Bool.Base using (Bool; false)
open import Data.Fin.Subset using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (suc; _<_)
open import Data.Product.Base using (_×_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Order M
open import PathSum.Polynomial
open import PathSum.Reduction M

private
  variable
    n k m k′ m′ k″ m″ : ℕ


record Semantics : Set₁ where
  infix 4 _≋_
  field
    -- Definition 2.3: two path-sums are equivalent when they denote
    -- the same operator.  The relation is heterogeneous in both the
    -- normalisation and the number of path variables, since the
    -- rewrite rules change them.
    _≋_ : PathSum n k m → PathSum n k′ m′ → Set

    ≋-refl  : {ξ : PathSum n k m} → ξ ≋ ξ
    ≋-sym   : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ≋ ζ → ζ ≋ ξ
    ≋-trans : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              {χ : PathSum n k″ m″} → ξ ≋ ζ → ζ ≋ χ → ξ ≋ χ

    -- Proposition 3.1 (correctness): the rules of figure 2 preserve
    -- the denotation.
    ⟶-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ≋ ζ

    -- Lemma 4.2 (destructive interference): if the quotient of the
    -- phase by an internal path variable is ½Q for a non-zero Q
    -- containing no path variable, then some input makes the two
    -- branches of that variable cancel, so ξ is not the identity.
    interference :
      (ξ : PathSum n k (suc m)) (c : Bool) (S : Mon n m) →
      head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
      (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
      proj₂ S ≡ ⊥ → ¬ (c ≡ false × S ≡ 1ᵐ) →
      ¬ (ξ ≋ idPS)

    -- The case lemma 4.3 leaves implicit: [Elim] applies to the phase
    -- but the normalisation cannot pay for it.  Summing a path
    -- variable away without paying doubles every amplitude, and the
    -- identity's, at a normalisation below 2, is not even.
    undersized-elim :
      (ξ : PathSum n k (suc m)) →
      head-part (phase ξ) ≈[ pow M ] 0ᴾ →
      (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
      k < 2 → ¬ (ξ ≋ idPS)

    -- And the same for [ω], which needs one unit: the amplitude is
    -- then root 2 times something, and the identity's is not.
    undersized-ω :
      (ξ : PathSum n 0 (suc m)) (c : Bool) (S : Mon n m) →
      head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
      (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
      ¬ (ξ ≋ idPS)
