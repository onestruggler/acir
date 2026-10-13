------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of CNOT-dihedral circuits, and its soundness
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Every axiom, and the
-- symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

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

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧)
open Circuits val using (module Exact)
open Exact public using (_≈_)
open Exact using (check ; module Symmetry)

open Symmetry
  (check 0 refl _ _ tt)
  (λ { X-gate → check 0 refl _ _ tt ; T-gate → check 0 refl _ _ tt })
  (λ { ⌈ CX-gate ⌉ → check 0 refl _ _ tt ; swap → check 0 refl _ _ tt })
  (λ ())
  using (module Theory)

open Theory arity lhs rhs
  (λ { ω⁸ → check 0 refl _ _ tt ; X² → check 0 refl _ _ tt ; T⁸ → check 0 refl _ _ tt
     ; TX → check 0 refl _ _ tt ; XC → check 0 refl _ _ tt ; B → check 0 refl _ _ tt
     ; ZC → check 0 refl _ _ tt ; CPh → check 0 refl _ _ tt ; I → check 0 refl _ _ tt
     ; C²T → check 0 refl _ _ tt ; C³T → check 0 refl _ _ tt })
  public using (sound)
