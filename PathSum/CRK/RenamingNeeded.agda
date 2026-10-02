------------------------------------------------------------------------
-- Presentations of groups
--
-- Even congruence needs the renaming (Amy, QPL 2018, remark 2.8)
--
-- PathSum.CRK.Structural shows that structurally equivalent circuits
-- have path-sums equal up to a renaming of their path variables, and
-- that the renaming cannot be dropped: H on wire 0 then H on wire 1
-- (HH₀₁) against the other order (HH₁₀) are structurally equivalent
-- (HH-∼), but ¬ (⟦ HH₀₁ ⟧ ≡ᴿ⟨ id ⟩ ⟦ HH₁₀ ⟧) (renaming-needed): their
-- phases differ, as integers, at the coefficient of x₀ y₀ -- 0 in the
-- one and ½ in the other.
--
-- That leaves open whether the weaker reading of the paper's "strictly
-- equal" -- phases equal modulo 2^M and outputs modulo 2, which is how
-- a path-sum is read (PathSum.Permute.Sound's ≈ᴿ) -- could do without
-- the renaming.  It cannot: ½ is 2^(M-1), which 2^M does not divide,
-- so the two phases are not congruent at that coefficient either
-- (renaming-needed-≈).  The renaming, the α-conversion of the bound
-- path variables, is needed however coefficients are compared.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.CRK.RenamingNeeded (M₀ : ℕ) where

open import Data.Fin.Permutation using (id)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (0ℤ; 1ℤ; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣⇒∣ᵤ; ∣m⇒∣-m)
open import Data.Integer.Properties using
  (+-identityˡ; *-zeroʳ; *-identityʳ; neg-involutive)
open import Data.Nat.Base using (_∸_; z≤n; s≤s)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong₂; subst)
open import Relation.Nullary.Negation using (¬_)

import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (phase)
open import PathSum.CRK.Circuit M using (⟦_⟧)
open import PathSum.CRK.Structural M₀ using (HH₀₁; HH₁₀)
open import PathSum.Order M using (pow)
open import PathSum.Permute using (renumberᴾ)
open import PathSum.Permute.Sound M₀ using (_≈ᴿ⟨_⟩_; congruent-renamed)
open import PathSum.Polynomial using (Mon)
open import PathSum.Reduction M using (½)

private
  -- The monomial x₀ y₀.
  γ₀ : Mon 2 2
  γ₀ = inside ∷ outside ∷ [] , inside ∷ outside ∷ []

  -- Its coefficient in either phase (as in PathSum.CRK.Structural).
  at₀₁ : renumberᴾ id (phase ⟦ HH₀₁ ⟧) γ₀ ≡ 0ℤ
  at₀₁ = trans (+-identityˡ (½ * 0ℤ)) (*-zeroʳ ½)

  at₁₀ : phase ⟦ HH₁₀ ⟧ γ₀ ≡ ½
  at₁₀ = trans (+-identityˡ (½ * 1ℤ)) (*-identityʳ ½)

  -- 2^(e+1) does not divide 2^e.
  pow-∤ : ∀ e → ¬ (pow (suc e) ∣ pow e)
  pow-∤ e h = ℕ.<⇒≱ (ℕ.^-monoʳ-< 2 (s≤s (s≤s z≤n)) (ℕ.n<1+n e))
                    (ℕDiv.∣⇒≤ {{ℕ.m^n≢0 2 e}} (∣⇒∣ᵤ h))

-- Not even congruent without the renaming.

renaming-needed-≈ : ¬ (⟦ HH₀₁ ⟧ ≈ᴿ⟨ id ⟩ ⟦ HH₁₀ ⟧)
renaming-needed-≈ (congruent-renamed _ (_ , ph)) = pow-∤ (M ∸ 1) ∣½
  where
  ∣0-½ : pow M ∣ (0ℤ - ½)
  ∣0-½ = subst (pow M ∣_) (cong₂ _-_ at₀₁ at₁₀) (ph γ₀)

  ∣½ : pow M ∣ ½
  ∣½ = subst (pow M ∣_) (neg-involutive ½)
         (∣m⇒∣-m (subst (pow M ∣_) (+-identityˡ (- ½)) ∣0-½))
