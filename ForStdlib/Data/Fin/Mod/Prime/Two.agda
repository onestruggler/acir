------------------------------------------------------------------------
-- The Agda standard library
--
-- The prime modulus 2
--
-- ℤ/2ℤ is the smallest prime modulus.  Its group of units ℤ*₂ = {₁} is
-- trivial, so ₁ is a primitive root and the generation proof is a
-- two-case match.
--
-- Everything downstream of a prime modulus -- the field structure,
-- Fermat's little theorem, discrete logarithms -- is parameterised by
-- exactly the data assembled here, so it is collected once rather than
-- rebuilt at each use site.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Prime.Two.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Prime.Two where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product.Base using (∃ ; _,_ ; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (from-yes)

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


------------------------------------------------------------------------
-- The modulus
--
-- A prime modulus is indexed throughout by its excess over 2, so the
-- modulus 2 is p-2 = 0.

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus' p-2 p-prime


------------------------------------------------------------------------
-- A primitive root
--
-- ₁ is the only unit, and it is ₁ ^′ 0, so it generates.

g* : ℤ* ₚ
g* = ₁ , λ ()

g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ (g* .proj₁) ^′ toℕ k
g-gen (₀ , ne) = ⊥-elim (ne refl)
g-gen (₁ , _)  = ₀ , refl
