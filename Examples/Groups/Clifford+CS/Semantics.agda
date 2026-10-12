------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic domain of Clifford+CS circuits: matrices over ℤ[½,i] on
-- n qubits, and the four gate matrices
--
-- A Clifford+CS circuit denotes a unitary matrix with entries in
-- ℤ[½,i].  The domain taken here is the monoid of 2ⁿ × 2ⁿ matrices over
-- ℤ[½,i] (Semantics.Scaled), in which a matrix is a matrix over ℤ[i]
-- together with the power of γ⁻¹ = 1/(1 + i) that scales it.  Nothing
-- here mentions the syntax: the matrices below are named after the
-- gates they will interpret, but the map from circuits to them is
-- Interpretation, and that it respects the relations is Soundness.
--
-- Each gate matrix below is γ times the gate, so that its entries lie
-- in ℤ[i]; the interpretation pairs it with one power of γ⁻¹
-- (Interpretation.⟦_⟧).  Basis vectors are bit vectors with wire 0
-- first.  All four gates are symmetric matrices.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Semantics where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ)
open import Data.Vec using ([] ; _∷_)

open import Examples.Groups.Clifford+CS.Semantics.Algebra public
open import Examples.Groups.Clifford+CS.Semantics.Local public
open import Examples.Groups.Clifford+CS.Semantics.Scaled public

------------------------------------------------------------------------
-- The gate matrices, times γ

private
  -- γ K = [[1 , 1] , [1 , −1]].
  kval : Bool → Bool → 𝔽
  kval true true = -1#
  kval _    _    = 1#

  -- γ S = diag(γ , γ i).
  sval : Bool → Bool → 𝔽
  sval false false = γ
  sval true  true  = γⅈ
  sval _     _     = 0#

  -- γ CS = diag(γ , γ , γ , γ i): the phase i on |11⟩.
  csval : Bool → Bool → 𝔽
  csval true true = γⅈ
  csval _    _    = γ

-- γ i, the scalar, at every width.
iOp : ∀ {n} → Op n
iOp = scal γⅈ

iM : ∀ {k} → Mat k
iM = matOf iOp

kM sM : Mat 1
kM = matOf (λ { (x ∷ []) (y ∷ []) → kval x y })
sM = matOf (λ { (x ∷ []) (y ∷ []) → sval x y })

csM : Mat 2
csM = matOf (λ { (x ∷ x' ∷ []) y → csval x x' * δb (x ∷ x' ∷ []) y })
