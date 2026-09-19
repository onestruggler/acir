------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrices of the auxiliary generators on n qubits (Clément,
-- Definition 4.1 at dimension 2ⁿ, indexed by the Gray code)
--
-- The 1- and 2-level matrices (−1)_[a], X_[a,b], H_[a,b] on 2ⁿ basis
-- vectors, the basis vector a being the bitstring G_n(a).  These are
-- the matrices of TwoQubit at n = 2, generalised; H carries one power
-- of 1/√2, as every gate does in Semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ) renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Equality of bitstrings, decided

eqᵇ : Bool → Bool → Bool
eqᵇ true  true  = true
eqᵇ false false = true
eqᵇ _     _     = false

eqB : Bits n → Bits n → Bool
eqB []       []       = true
eqB (a ∷ x) (b ∷ y) = eqᵇ a b ∧ eqB x y

------------------------------------------------------------------------
-- The one- and two-level matrices

-- (−1)_[i]: the sign −1 on basis vector i.
negOp : Bits n → Op n
negOp i x y = (if eqB x i then -1# else 1#) * δb x y

-- X_[i,j]: the exchange of basis vectors i and j.
swapOp : Bits n → Bits n → Op n
swapOp i j x y = δb (if eqB x i then j else if eqB x j then i else x) y

-- √2 H_[i,j]: the Hadamard on the span of i and j (in that order),
-- √2 times the identity elsewhere.
hadOp : Bits n → Bits n → Op n
hadOp i j x y =
  if eqB x i then (if eqB y i then 1# else if eqB y j then 1# else 0#)
  else if eqB x j then (if eqB y i then 1# else if eqB y j then -1# else 0#)
  else √2 * δb x y

-- The generators' matrices over ℤ[1/√2], basis vectors by the Gray
-- code.
⟦_⟧ᴳ : G.Gen (2 ^ℕ n) → Scaled n
⟦_⟧ᴳ {n} −1[ a ]    = 0 , negOp (code n a)
⟦_⟧ᴳ {n} X[ a , b ] = 0 , swapOp (code n a) (code n b)
⟦_⟧ᴳ {n} H[ a , b ] = 1 , hadOp (code n a) (code n b)
