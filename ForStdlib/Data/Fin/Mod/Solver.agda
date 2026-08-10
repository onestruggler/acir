------------------------------------------------------------------------
-- The Agda standard library
--
-- A ring solver for ℤ/nℤ
--
-- Sol instantiates the non-reflective ring solver at the commutative
-- ring ℤ/(2+m)ℤ.  It is opened publicly right after its definition, so
-- the modulus becomes the first explicit argument of solve.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.Solver.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod.Solver where

open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Notations using (₀ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Tactic.RingSolver.Core.AlmostCommutativeRing
  using (AlmostCommutativeRing ; fromCommutativeRing)

open import ForStdlib.Data.Fin.Mod.Base using (ℤ)
open import ForStdlib.Data.Fin.Mod.Properties using (+-*-commutativeRing)

------------------------------------------------------------------------
-- The solver

module Sol (m : ℕ) where

  open import Tactic.RingSolver.Core.AlmostCommutativeRing

  meq0 : (x : ℤ (₂₊ m)) → Maybe (₀ ≡ x)
  meq0 ₀ = just refl
  meq0 (₁₊ x) = nothing

  aring : AlmostCommutativeRing _ _
  aring = fromCommutativeRing (+-*-commutativeRing m) meq0

  open import Tactic.RingSolver.NonReflective (aring) using (solve ) public
  open import Tactic.RingSolver.Core.Expression public





open Sol public
