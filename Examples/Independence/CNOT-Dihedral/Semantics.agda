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

-- Every axiom, on its own wires: (C²T) and (C³T) on their operators'
-- tables, the others as matrices.
ax-ok : ∀ {n} {w v : Circuit n} → n SRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
ax-ok ω⁸  = check 0 refl _ _ _
ax-ok X²  = check 0 refl _ _ _
ax-ok T⁸  = check 0 refl _ _ _
ax-ok TX  = check 0 refl _ _ _
ax-ok XC  = check 0 refl _ _ _
ax-ok B   = check 0 refl _ _ _
ax-ok ZC  = check 0 refl _ _ _
ax-ok CPh = check 0 refl _ _ _
ax-ok I   = check 0 refl _ _ _
ax-ok {w = w} {v} C²T =
  same-matrix w v (AI.by-relator (wmap ι⁻ w) (wmap ι⁻ v) refl refl refl)
ax-ok {w = w} {v} C³T =
  same-matrix w v (AI.by-relator (wmap ι⁻ w) (wmap ι⁻ v) refl refl refl)

open Symmetry refl SWᵍ-ok
  using (module Theory)

open Theory _SRel,_===_ ax-ok public using (sound)
