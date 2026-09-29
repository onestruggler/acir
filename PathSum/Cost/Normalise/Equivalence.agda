------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalisation preserves the operator (for Amy, QPL 2018,
-- propositions 3.1 and 3.2)
--
-- PathSum.Cost.Normalise proves that the algorithm's result comes with
-- a dense chain from the input ξ to a path-sum the result represents.
-- Proposition 3.1 along the chain (PathSum.Anywhere.Sound.⟶ᵍ*-sound)
-- and PathSum.Size.Equivalence.represents-≋ then give the same operator
-- for the path-sum the result stands for (PathSum.Cost.Normalise.psᴺ):
-- ξ ≋ psᴺ r, and so psʳ k R ≋ psᴺ r for the input representation R.
-- This holds at M = 3 + M₀, the precision of PathSum.Denotation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Normalise.Equivalence (M₀ : ℕ) where

open import Data.Nat.Base using (suc; _≤_)
open import Data.Product.Base using (_×_; _,_)

open import PathSum.Anywhere.Sound M₀ using (⟶ᵍ*-sound)
open import PathSum.Base using (PathSum; phase)
open import PathSum.Cost using (value)
open import PathSum.Denotation M₀ using (_≋_; ≋-sym; ≋-trans)
open import PathSum.Size.Equivalence M₀ using (represents-≋)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Cost.Normalise M using
  (normaliseᶜ; nrep; psᴺ; reduct; chain; reduct-represents;
   normalise-sound)
open import PathSum.Order M using (Ord≤)
open import PathSum.Size.Sparse M using (Rep; Represents; psʳ)

private
  variable
    n k m : ℕ

-- The input, and the path-sum its representation stands for, denote
-- the operator of the path-sum the result stands for.

normalise-≋ : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k m) (R : Rep n m) →
              Represents ξ R → Ord≤ d (phase ξ) →
              (ξ ≋ psᴺ (value (normaliseᶜ d k R))) ×
              (psʳ k R ≋ psᴺ (value (normaliseᶜ d k R)))
normalise-≋ {k = k} d 2≤d ξ R rp ordP = ξ≋ , R≋
  where
  N = normalise-sound d 2≤d ξ R rp ordP
  r = value (normaliseᶜ d k R)

  ξ≋ : ξ ≋ psᴺ r
  ξ≋ = ≋-trans {ξ = ξ} {ζ = reduct N} {χ = psᴺ r} (⟶ᵍ*-sound (chain N))
               (represents-≋ (reduct N) (nrep r) (reduct-represents N))

  R≋ : psʳ k R ≋ psᴺ r
  R≋ = ≋-trans {ξ = psʳ k R} {ζ = ξ} {χ = psᴺ r}
               (≋-sym {ξ = ξ} {ζ = psʳ k R} (represents-≋ ξ R rp)) ξ≋
