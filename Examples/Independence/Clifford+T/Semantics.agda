------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of Clifford+T circuits, and its soundness
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit.  Every axiom, and the
-- symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+T.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Clifford+T.Syntactics
open import Examples.Independence.Semantics.Qubit
  using (Sc ; ωᵍ ; Hᵍ ; Tᵍ ; CXᵍ ; SWᵍ ; SWᵍ-ok ; module Circuits)

-- The gates.
val : ∀ {k} → PGate k → Sc k
val ⌈ ω-gate ⌉  = ωᵍ
val ⌈ H-gate ⌉  = Hᵍ
val ⌈ T-gate ⌉  = Tᵍ
val ⌈ CX-gate ⌉ = CXᵍ
val swap = SWᵍ

open Circuits val public using (⟦_⟧₀ ; ⟦_⟧)
open Circuits val using (module Exact)
open Exact public using (_≈_)
open Exact using (check ; module Symmetry)

open Symmetry refl SWᵍ-ok
  using (module Theory)

open Theory _SRel,_===_
  (λ { ω⁸ → check 0 refl _ _ tt ; T⁸ → check 0 refl _ _ tt ; H² → check 0 refl _ _ tt
     ; E → check 0 refl _ _ tt ; TX → check 0 refl _ _ tt ; CPh → check 0 refl _ _ tt
     ; B → check 0 refl _ _ tt ; CZ → check 0 refl _ _ tt ; CSH → check 0 refl _ _ tt
     ; HT² → check 0 refl _ _ tt ; HTH → check 0 refl _ _ tt })
  public using (sound)
