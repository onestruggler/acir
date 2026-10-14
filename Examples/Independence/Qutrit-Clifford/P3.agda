------------------------------------------------------------------------
-- Presentations of groups
--
-- The qupit Clifford development at p = 3
--
-- The qupit library (Examples.Groups.ProjectiveClifford.Qupit,
-- Examples.Groups.Clifford+MinusOne.Qupit) is parameterised by an odd
-- prime p and a primitive root g mod p.  Here p = 3 and g = 2: 2 has
-- order 2 = p - 1 mod 3, so every unit is a power of it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.P3 where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product.Base using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (toWitness)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

-- p - 3, the parameter of the qupit modules.
p-3 : ℕ
p-3 = 0

p-prime : Prime 3
p-prime = toWitness {a? = prime? 3} _

open PrimeModulus' 1 p-prime public

g* : ℤ* ₚ
g* = ₂ , λ ()

g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ ₂ ^′ toℕ k
g-gen (₀ , nz) = ⊥-elim (nz refl)
g-gen (₁ , _)  = ₀ , refl
g-gen (₂ , _)  = ₁ , refl
