------------------------------------------------------------------------
-- Presentations of groups
--
-- The sign-tracking Clifford action on the Pauli group P4 (p = 2).
--
-- Conjugation of a phased Pauli i^s X^a Z^b by a Clifford generator g:
--
--     g (i^s X^a Z^b) g⁻¹ = i^{s + δ g P} (act1 g P),   P = (a , b),
--
-- where act1 is the phaseless symplectic action and δ g P ∈ ℤ/4 is the
-- phase the conjugation introduces.  The phase formulas (verified against
-- the exact Clifford matrices) are, per acted qubit,
--
--     δ (S^j) = incl (j·a),     δ (H^j) = ι ((j mod 2)·a·b),
--     δ (CZ^j) = ι (j·a·a'),    δ (g↥)  = δ g on the tail,
--
-- with ι : ℤ/2 → ℤ/4 the ×2 map (from SignedPauli) and incl the ×1 map.
-- cact extends the action to Clifford words; each cact w is an
-- automorphism of P4 (proven in a later module).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.CliffordAction where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
open import Relation.Nullary.Decidable using (from-yes)

open import Notations
open import Zp.ModularArithmetic
open import Word.Base using (Word)
open import Presentation.GroupLike using (word-act)

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.Symplectic.Action p-2 p-prime using (act1)
open import Examples.Groups.Symplectic.Symplectic-Derived p-2 p-prime
  using (module Symplectic-Derived-Gen)
open Symplectic-Derived-Gen
  using (Gen ; gate₁ ; gate₂ ; H-gen ; S-gen ; CZ-gen ; _↥)
open import Examples.Groups.Clifford.Qubit.SignedPauli using (Φ ; P4Carrier ; ι)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Phase bookkeeping

-- Parity ℤ/4 → ℤ/2, and the ×1 inclusion ℤ/2 → ℤ/4.
oddℤ2 : ℤ ₄ → ℤ ₚ
oddℤ2 ₀ = ₀
oddℤ2 ₁ = ₁
oddℤ2 ₂ = ₀
oddℤ2 ₃ = ₁

incl : ℤ ₚ → Φ
incl ₀ = ₀
incl ₁ = ₁

-- The conjugation phase δ g P ∈ ℤ/4.
δ : Gen n → Pauli n → Φ
δ (gate₁ (H-gen j))  ((a , b) ∷ ps)             = ι (oddℤ2 j * a * b)
δ (gate₁ (S-gen j))  ((a , b) ∷ ps)             = incl (j * a)
δ (gate₂ (CZ-gen j)) ((a , b) ∷ (a' , b') ∷ ps) = ι (j * a * a')
δ (g ↥)              (p ∷ ps)                   = δ g ps

------------------------------------------------------------------------
-- The action

cact1 : Gen n → P4Carrier n → P4Carrier n
cact1 g (s , P) = (s + δ g P) , act1 g P

cact : Word (Gen n) → P4Carrier n → P4Carrier n
cact = word-act cact1
