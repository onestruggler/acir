------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of qubit Clifford circuits, and its soundness
--
-- Section 3.1: ω, H, S and CNOT read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Every axiom of Cliff₂, and
-- the symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Clifford.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; ωᵍ ; Hᵍ ; Sᵍ ; CXᵍ ; SWᵍ ; module Circuits)

-- The gates.
val : ∀ {k} → PGate k → Sc k
val ⌈ ω-gate ⌉  = ωᵍ
val ⌈ H-gate ⌉  = Hᵍ
val ⌈ S-gate ⌉  = Sᵍ
val ⌈ CX-gate ⌉ = CXᵍ
val swap        = SWᵍ

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧)
open Circuits val using (module Exact)
open Exact public using (_≈_)
open Exact using (check ; module Symmetry)

open Symmetry
  (check 0 refl _ _ tt)
  (λ { H-gate → check 0 refl _ _ tt ; S-gate → check 0 refl _ _ tt })
  (λ { ⌈ CX-gate ⌉ → check 0 refl _ _ tt ; swap → check 0 refl _ _ tt })
  using (module Theory)

open Theory arity lhs rhs
  (λ { ω⁸  → check 0 refl _ _ tt
     ; H²  → check 0 refl _ _ tt
     ; S⁴  → check 0 refl _ _ tt
     ; E   → check 0 refl _ _ tt
     ; CPh → check 0 refl _ _ tt
     ; B   → check 0 refl _ _ tt
     ; CZ  → check 0 refl _ _ tt
     ; I   → check 0 refl _ _ tt })
  public using (sound)
