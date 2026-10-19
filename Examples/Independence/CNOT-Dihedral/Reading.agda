------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix reading of CNOT-dihedral circuits
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Semantics proves the reading
-- sound; Bridge compares it with Amy, Chen and Ross's operators, and
-- Semantics checks its two largest axioms through that comparison.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Reading where

open import Examples.Independence.CNOT-Dihedral.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; ωᵍ ; Xᵍ ; Tᵍ ; CXᵍ ; SWᵍ ; module Circuits)

-- The gates.
val : ∀ {k} → PGate k → Sc k
val ⌈ ω-gate ⌉  = ωᵍ
val ⌈ X-gate ⌉  = Xᵍ
val ⌈ T-gate ⌉  = Tᵍ
val ⌈ CX-gate ⌉ = CXᵍ
val swap = SWᵍ

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧ ; module Exact)
open Exact public using (_≈_)
