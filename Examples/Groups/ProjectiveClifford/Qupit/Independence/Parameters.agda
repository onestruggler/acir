------------------------------------------------------------------------
-- Presentations of groups
--
-- Concrete parameters for the qupit Clifford rules
--
-- Paper-V1 is stated for p = 3 + p-3 prime and a primitive root g of
-- ℤ/pℤ, given with a discrete logarithm for every unit.  This module
-- supplies those parameters at p = 3 (g = 2) and p = 5 (g = 2 and
-- g = 3).  The primality proofs are the standard library's decision
-- procedure, and each discrete logarithm is a table.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (from-yes)

open import Notations
open import ForStdlib.Data.Fin.Mod

------------------------------------------------------------------------
-- p = 3

prime-3 : Prime 3
prime-3 = from-yes (prime? 3)

-- 2 generates ℤ/3ℤ*: 1 = 2⁰, 2 = 2¹.
root-3 : ℤ* 3
root-3 = ₂ , λ ()

root-3-gen : ∀ ((x , _) : ℤ* 3) → ∃ λ (k : ℤ 2) → x ≡ ₂ ^′ toℕ k
root-3-gen (₀ , x≢0) = ⊥-elim (x≢0 refl)
root-3-gen (₁ , _)   = ₀ , refl
root-3-gen (₂ , _)   = ₁ , refl

------------------------------------------------------------------------
-- p = 5

prime-5 : Prime 5
prime-5 = from-yes (prime? 5)

-- 2 generates ℤ/5ℤ*: 1 = 2⁰, 2 = 2¹, 4 = 2², 3 = 2³.
root-5 : ℤ* 5
root-5 = ₂ , λ ()

root-5-gen : ∀ ((x , _) : ℤ* 5) → ∃ λ (k : ℤ 4) → x ≡ ₂ ^′ toℕ k
root-5-gen (₀ , x≢0) = ⊥-elim (x≢0 refl)
root-5-gen (₁ , _)   = ₀ , refl
root-5-gen (₂ , _)   = ₁ , refl
root-5-gen (₃ , _)   = ₃ , refl
root-5-gen (₄ , _)   = ₂ , refl

-- So does 3: 1 = 3⁰, 3 = 3¹, 4 = 3², 2 = 3³.  This root is odd.
root-5' : ℤ* 5
root-5' = ₃ , λ ()

root-5'-gen : ∀ ((x , _) : ℤ* 5) → ∃ λ (k : ℤ 4) → x ≡ ₃ ^′ toℕ k
root-5'-gen (₀ , x≢0) = ⊥-elim (x≢0 refl)
root-5'-gen (₁ , _)   = ₀ , refl
root-5'-gen (₂ , _)   = ₃ , refl
root-5'-gen (₃ , _)   = ₁ , refl
root-5'-gen (₄ , _)   = ₂ , refl
