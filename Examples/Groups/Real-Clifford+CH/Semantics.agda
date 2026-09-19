------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic domain of real-Clifford+CH circuits: matrices over
-- ℤ[1/√2] on n qubits, and the four gate matrices
--
-- Clément's Definition 2.3 reads an n-qubit circuit as a linear map on
-- ℂ^{2ⁿ}; all four gates are real with entries in ℤ[1/√2], and so is
-- every circuit.  The domain taken here is the monoid of 2ⁿ × 2ⁿ
-- matrices over ℤ[1/√2] (Semantics.Scaled), in which a matrix is a
-- matrix over ℤ[√2] together with the power of 1/√2 that scales it.
-- Nothing here mentions the syntax: the matrices below are named after
-- the gates they will interpret, but the map from circuits to them is
-- Interpretation, and that it respects the relations is Soundness.
--
-- Each gate matrix below is √2 times the paper's gate, so that its
-- entries lie in ℤ[√2]; the interpretation pairs it with one power of
-- 1/√2 (Interpretation.⟦_⟧).  Basis vectors are bit vectors with wire 0
-- first; a two-wire matrix is indexed by (x₀ ∷ x₁ ∷ []), and CH is
-- controlled by x₁ with target x₀.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using ([] ; _∷_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra public
open import Examples.Groups.Real-Clifford+CH.Semantics.Local public
open import Examples.Groups.Real-Clifford+CH.Semantics.Scaled public

------------------------------------------------------------------------
-- The gate matrices (Definition 2.3), times √2

private
  -- √2 H = [[1 , 1] , [1 , −1]].
  hval : Bool → Bool → 𝔽
  hval true true = -1#
  hval _    _    = 1#

  -- √2 Z = diag(√2 , −√2).
  zval : Bool → Bool → 𝔽
  zval false false = √2
  zval true  true  = -√2
  zval _     _     = 0#

  -- √2 CZ = √2 diag(1 , 1 , 1 , −1): the phase −1 on |11⟩.
  czval : Bool → Bool → 𝔽
  czval true true = -√2
  czval _    _    = √2

  -- √2 CH: √2 H on wire 0 when the control wire 1 is set, else √2 I.
  chval : Bits 2 → Bits 2 → 𝔽
  chval (x₀ ∷ true  ∷ []) (y₀ ∷ true  ∷ []) = hval x₀ y₀
  chval (x₀ ∷ false ∷ []) (y₀ ∷ false ∷ []) = √2 * δ₁ x₀ y₀
  chval _                 _                 = 0#

hM zM : Mat 1
hM = matOf (λ { (x ∷ []) (y ∷ []) → hval x y })
zM = matOf (λ { (x ∷ []) (y ∷ []) → zval x y })

czM chM : Mat 2
czM = matOf (λ { (x ∷ x' ∷ []) y → czval x x' * δb (x ∷ x' ∷ []) y })
chM = matOf chval
