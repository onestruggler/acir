------------------------------------------------------------------------
-- Presentations of groups
--
-- The primitive-root data instantiating Symplectic.Simplified at p = 2.
--
-- Examples.Groups.Symplectic.Simplified.* is parameterised by a
-- generator g of the multiplicative group ℤ*ₚ together with a proof that
-- every unit is a power of it.  At p = 2 the group ℤ*₂ = {1} is trivial,
-- so 1 is a primitive root and the proof is a two-case match.
--
-- Collected here so the qubit modules can pass (g* , g-gen) on without
-- each repeating the construction.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.PrimitiveRoot where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (∃ ; _,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (from-yes)

open import Notations
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

-- Qubit case: fix the prime to 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus' p-2 p-prime

-- ℤ*₂ = {₁}, so 1 generates it.
g* : ℤ* ₚ
g* = ₁ , λ ()

g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ (g* .proj₁) ^′ toℕ k
g-gen (₀ , ne) = ⊥-elim (ne Eq.refl)
g-gen (₁ , _)  = ₀ , Eq.refl
