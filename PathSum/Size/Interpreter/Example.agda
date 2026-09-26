------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse interpreter run on the Toffoli circuit (for Amy, QPL
-- 2018, corollary 2.15 and example 3.3)
--
-- PathSum.Size.Interpreter run on Nielsen and Chuang's seven-T Toffoli
-- circuit (PathSum.Examples.Toffoli.ToffoliC, over {H, CNOT, T, T†} at
-- M = 3), by computation.  The two Hadamards act on forms of weight 1
-- and add 2 terms each; the seven T and T† gates act on forms of
-- weights 2, 3, 2, 1, 1, 2 and 1 and add 4, 8, 4, 2, 2, 4 and 2: 30
-- terms (Toffoli-interp-terms), 21 of them with a nonzero
-- coefficient (Toffoli-interp-nonzero), 258 bits
-- (Toffoli-interp-size), over two path variables
-- (Toffoli-interp-paths).  Compacted at degree 3 they become the 26
-- terms of PathSum.Size.Example -- one per monomial of degree at most
-- 3 in the five variables, 226 bits -- of which exactly the paper's
-- three are nonzero, ½(x3y + x1x2y + y′y) (Toffoli-compact-support),
-- as Interpreter.compactᴷ≡repᴷ says they must be.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Size.Interpreter.Example where

open import Data.List.Base using ([]; _∷_; length)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PathSum.Examples.Base using (x₁; x₂; x₃; y₁; y₂)
open import PathSum.Examples.Toffoli using (ToffoliC)
open import PathSum.Polynomial using (_∪ᵐ_)
open import PathSum.Size.Example using (support)
open import PathSum.Size.Interpreter 3 using (interpᴷ; compactᴷ)
open import PathSum.Size.Sparse 3 using (terms; size)


------------------------------------------------------------------------
-- As the interpreter leaves it

Toffoli-interp-paths : proj₁ (interpᴷ ToffoliC) ≡ 2
Toffoli-interp-paths = refl

Toffoli-interp-terms : length (terms (proj₂ (interpᴷ ToffoliC))) ≡ 30
Toffoli-interp-terms = refl

Toffoli-interp-nonzero :
  length (support (terms (proj₂ (interpᴷ ToffoliC)))) ≡ 21
Toffoli-interp-nonzero = refl

Toffoli-interp-size : size (proj₂ (interpᴷ ToffoliC)) ≡ 258
Toffoli-interp-size = refl


------------------------------------------------------------------------
-- Compacted

Toffoli-compact-terms : length (terms (proj₂ (compactᴷ ToffoliC))) ≡ 26
Toffoli-compact-terms = refl

Toffoli-compact-size : size (proj₂ (compactᴷ ToffoliC)) ≡ 226
Toffoli-compact-size = refl

Toffoli-compact-support :
  support (terms (proj₂ (compactᴷ ToffoliC))) ≡
  (x₁ ∪ᵐ x₂ ∪ᵐ y₂ , 4) ∷ (x₃ ∪ᵐ y₂ , 4) ∷ (y₁ ∪ᵐ y₂ , 4) ∷ []
Toffoli-compact-support = refl
