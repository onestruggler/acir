------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of real Clifford circuits, and its soundness
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Every axiom, and the
-- symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Real-Clifford.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Real-Clifford.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; −1ᵍ ; Hᵍ ; Zᵍ ; CXᵍ ; SWᵍ ; module Circuits)

-- The gates.
val : ∀ {k} → PGate k → Sc k
val ⌈ m-gate ⌉  = −1ᵍ
val ⌈ H-gate ⌉  = Hᵍ
val ⌈ Z-gate ⌉  = Zᵍ
val ⌈ CX-gate ⌉ = CXᵍ
val swap = SWᵍ

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧)
open Circuits val using (module Exact)
open Exact public using (_≈_)
open Exact using (check ; module Symmetry)

open Symmetry
  (check 0 refl _ _ tt)
  (λ { H-gate → check 0 refl _ _ tt ; Z-gate → check 0 refl _ _ tt })
  (λ { ⌈ CX-gate ⌉ → check 0 refl _ _ tt ; swap → check 0 refl _ _ tt })
  (λ ())
  using (module Theory)

open Theory arity lhs rhs
  (λ { −² → check 0 refl _ _ tt ; H² → check 0 refl _ _ tt ; Z² → check 0 refl _ _ tt
     ; F → check 0 refl _ _ tt ; CX² → check 0 refl _ _ tt ; B → check 0 refl _ _ tt
     ; ZC → check 0 refl _ _ tt ; CZr → check 0 refl _ _ tt ; CF → check 0 refl _ _ tt
     ; I → check 0 refl _ _ tt })
  public using (sound)
