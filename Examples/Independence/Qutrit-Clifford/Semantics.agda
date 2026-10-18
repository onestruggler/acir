------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of qutrit Clifford circuits, and its soundness
--
-- Section 3.2: the gates read as the matrices of
-- Examples.Independence.Semantics.Qutrit.  Every axiom of Cliff₃ (with
-- the scalar of (E) corrected, see Syntactics), and the symmetry
-- rules, are checked by evaluation on their own wires, so that every
-- derivable equation holds exactly, at every width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Qutrit-Clifford.Syntactics
open import Examples.Independence.Semantics.Qutrit
  using (Sc ; ωᵍ ; Hᵍ ; Sᵍ ; CXᵍ ; SWᵍ ; SWᵍ-ok ; module Circuits)

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

open Symmetry refl SWᵍ-ok
  using (module Theory)

open Theory _SRel,_===_
  (λ { ω¹² → check 0 refl _ _ _ ; H⁴ → check 0 refl _ _ _ ; S³ → check 0 refl _ _ _
     ; E → check 0 refl _ _ _ ; SS′ → check 0 refl _ _ _ ; CPh → check 0 refl _ _ _
     ; KC → check 0 refl _ _ _ ; CZ → check 0 refl _ _ _ ; B → check 0 refl _ _ _
     ; I → check 0 refl _ _ _ })
  public using (sound)
