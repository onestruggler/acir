------------------------------------------------------------------------
-- The exact matrix domain, independently of the circuit syntax.
-- Matrix denotes an 8 × 8 matrix over ℤ[1/√2], represented as
-- an integer-√2 numerator and a power of √2 in the denominator.
-- Equality retains the scalar; it is not projective equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Semantics where

open import Algebra.Bundles using (Monoid)
open import Level using (0ℓ)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra public
open import Examples.Groups.Real-Clifford+CH.Semantics.Scaled public

Matrix : Set
Matrix = Scaled 3

matrix-monoid : Monoid 0ℓ 0ℓ
matrix-monoid = Scaled-monoid 3
