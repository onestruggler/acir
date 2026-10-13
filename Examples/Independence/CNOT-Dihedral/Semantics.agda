------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of CNOT-dihedral circuits, and its soundness
--
-- Section 3.1: the gates read as the matrices of
-- Examples.Independence.Semantics.Qubit (Reading).  Every axiom, and
-- the symmetry rules, are checked by evaluation on their own wires, so
-- that every derivable equation holds exactly, at every width.
--
-- The two largest, (C²T) on three wires and (C³T) on four, are checked
-- on Amy, Chen and Ross's operators instead (Bridge.same-matrix): every
-- gate here sends a basis vector to a basis vector with a phase, so an
-- operator is a table of 2ⁿ entries, where the matrix is a 2ⁿ × 2ⁿ
-- product of every gate.  Checked as matrices they took some fifteen
-- minutes; as tables they take seconds.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Semantics where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Word.Base using (wmap)

open import Examples.Independence.CNOT-Dihedral.Syntactics
open import Examples.Independence.CNOT-Dihedral.Reading public
  using (val ; ⟦_⟧₀ ; ⟦_⟧ ; _≈_)
open import Examples.Independence.CNOT-Dihedral.Reading using (module Exact)
open import Examples.Independence.Semantics.Qubit using (SWᵍ-ok)
open import Examples.Independence.CNOT-Dihedral.Bridge using (ι⁻ ; same-matrix)
import Examples.Groups.CNOT+Dihedral.Interpretation as AI

open Exact using (check ; module Symmetry)

-- (C²T) and (C³T), on their operators' tables.
C²T-ok : ⟦ lhs C²T ⟧ ≈ ⟦ rhs C²T ⟧
C²T-ok = same-matrix (lhs C²T) (rhs C²T)
  (AI.by-relator (wmap ι⁻ (lhs C²T)) (wmap ι⁻ (rhs C²T)) refl refl refl)

C³T-ok : ⟦ lhs C³T ⟧ ≈ ⟦ rhs C³T ⟧
C³T-ok = same-matrix (lhs C³T) (rhs C³T)
  (AI.by-relator (wmap ι⁻ (lhs C³T)) (wmap ι⁻ (rhs C³T)) refl refl refl)

open Symmetry refl SWᵍ-ok
  using (module Theory)

open Theory arity lhs rhs
  (λ { ω⁸ → check 0 refl _ _ tt ; X² → check 0 refl _ _ tt ; T⁸ → check 0 refl _ _ tt
     ; TX → check 0 refl _ _ tt ; XC → check 0 refl _ _ tt ; B → check 0 refl _ _ tt
     ; ZC → check 0 refl _ _ tt ; CPh → check 0 refl _ _ tt ; I → check 0 refl _ _ tt
     ; C²T → C²T-ok ; C³T → C³T-ok })
  public using (sound)
