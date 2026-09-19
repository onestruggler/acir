------------------------------------------------------------------------
-- Presentations of groups
--
-- The exponents of ω: the cyclic group ℤ₈
--
-- Phases of CNOT-dihedral operators are eighth roots of unity, ω^k with
-- k modulo 8.  ℤ₈ is Fin 8 with addition modulo 8; its laws are decided
-- by exhaustion, there being 512 cases at most.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Semantics.Z8 where

open import Data.Fin using (Fin ; zero ; suc ; toℕ)
open import Data.Fin.Properties using (all? ; _≟_)
open import Data.Nat using (ℕ)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (toWitness ; _→?_)

import Data.Nat as ℕ

ℤ₈ : Set
ℤ₈ = Fin 8

0₈ 1₈ : ℤ₈
0₈ = zero
1₈ = suc zero

infixl 6 _+_

_+_ : ℤ₈ → ℤ₈ → ℤ₈
a + b = (toℕ a ℕ.+ toℕ b) mod 8

_≟₈_ : DecidableEquality ℤ₈
_≟₈_ = _≟_

------------------------------------------------------------------------
-- The laws, by exhaustion

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc = toWitness
  {a? = all? λ a → all? λ b → all? λ c → ((a + b) + c) ≟ (a + (b + c))} _

+-comm : ∀ a b → a + b ≡ b + a
+-comm = toWitness {a? = all? λ a → all? λ b → (a + b) ≟ (b + a)} _

+-identityˡ : ∀ a → 0₈ + a ≡ a
+-identityˡ = toWitness {a? = all? λ a → (0₈ + a) ≟ a} _

+-identityʳ : ∀ a → a + 0₈ ≡ a
+-identityʳ = toWitness {a? = all? λ a → (a + 0₈) ≟ a} _

+-cancelˡ : ∀ a b c → a + b ≡ a + c → b ≡ c
+-cancelˡ = toWitness
  {a? = all? λ a → all? λ b → all? λ c → ((a + b) ≟ (a + c)) →? (b ≟ c)} _
