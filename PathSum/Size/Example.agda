------------------------------------------------------------------------
-- Presentations of groups
--
-- The size of the Toffoli circuit's path-sum, computed (for Amy, QPL
-- 2018, corollary 2.15 and example 3.3)
--
-- PathSum.Size bounds the size of the representation repᴷ C of the
-- path-sum of a circuit.  Here it is computed for Nielsen and
-- Chuang's seven-T Toffoli circuit (PathSum.Examples.Toffoli.ToffoliC,
-- over {H, CNOT, T, T†} at M = 3): three inputs, two Hadamards and so
-- two path variables, level 3, so d = 3 and the terms are listed on
-- the 1 + 5 + 10 + 10 = 26 monomials of degree at most 3 in the five
-- variables (Toffoli-length), 8 bits each, besides three forms of
-- 6 bits: 226 bits in all (Toffoli-size), against the general bound
-- 2 · 22^4.  Exactly three of the coefficients are nonzero modulo 1
-- (Toffoli-support): the phase is ½(x3y + x1x2y + y′y), y being the
-- first Hadamard's variable, which the circuit lists second -- the
-- paper's ½(x3y1 + x1x2y1 + y1y2) with y1 = y and y2 = y′.  Everything
-- is checked by computation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Size.Example where

open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PathSum.Examples.Base using (x₁; x₂; x₃; y₁; y₂)
open import PathSum.Examples.Toffoli using (ToffoliC)
open import PathSum.Polynomial using (Mon; _∪ᵐ_)
open import PathSum.Size 3 using (repᴷ)
open import PathSum.Size.Sparse 3 using (Term; terms; size)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The nonzero terms

-- The terms with a nonzero coefficient, as (monomial, numerator over
-- 2^M) pairs.

support : List (Term n m) → List (Mon n m × ℕ)
support []             = []
support ((δ , c) ∷ ts) with toℕ c
... | zero  = support ts
... | suc a = (δ , suc a) ∷ support ts


------------------------------------------------------------------------
-- The seven-T Toffoli circuit

Toffoli-length : length (terms (repᴷ ToffoliC)) ≡ 26
Toffoli-length = refl

Toffoli-size : size (repᴷ ToffoliC) ≡ 226
Toffoli-size = refl

-- ½ = 4/8 on x1x2y, x3y and y′y, where y = y₂ and y′ = y₁ in the
-- circuit's numbering.

Toffoli-support :
  support (terms (repᴷ ToffoliC)) ≡
  (x₁ ∪ᵐ x₂ ∪ᵐ y₂ , 4) ∷ (x₃ ∪ᵐ y₂ , 4) ∷ (y₁ ∪ᵐ y₂ , 4) ∷ []
Toffoli-support = refl
