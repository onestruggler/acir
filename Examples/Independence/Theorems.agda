------------------------------------------------------------------------
-- Presentations of groups
--
-- The main results of Blake, "Simpler presentations for many fragments
-- of quantum circuits" (FSCD 2026, arXiv:2602.09874), as formalised in
-- Examples.Independence
--
-- Six circuit fragments in PROPs with structural swaps (Prop): qubit
-- Clifford (Cliff₂), real Clifford (RCliff₂), qutrit Clifford (Cliff₃),
-- Clifford+T (CliffT₂), Clifford+CS (CliffCS₂) and CNOT-dihedral
-- (CNOTdihe₂).  For each:
--
-- * the syntax and rule set of Figures 2–7, with the shortcuts of
--   Figure 9 (<fragment>.Syntactics);
-- * the matrix semantics of Section 3, and soundness: every derivable
--   equation holds exactly, at every width (<fragment>.Semantics);
-- * Theorem 37, by the separators of Figure 8 (<fragment>.Minimality,
--   and <fragment>.Projective for the projective substitutions).
--
-- Completeness (Section 4) is not formalised here: it is transferred
-- from the source presentations, several of which this library proves
-- complete in their own developments.
--
-- Two departures from the paper.  The scalar of the qutrit axiom (E)
-- is printed ω₁₂⁷ in Figure 4, which is unsound for the semantics of
-- Section 3.2; it is ω₁₂ here.  And the separator #{CX, σ}[2] of the
-- Clifford axiom (CZ) does not respect the three-wire (I), but need not:
-- a derivation between two-wire circuits uses no three-wire axiom
-- (Prop.truncate, Remark 14), which is how every bounded separator is
-- applied here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Theorems where

open import Data.Nat.Base using (ℕ)

import Examples.Independence.Clifford.Syntactics       as Cliff
import Examples.Independence.Real-Clifford.Syntactics  as RCliff
import Examples.Independence.Qutrit-Clifford.Syntactics as Cliff3
import Examples.Independence.Clifford+T.Syntactics     as CliffT
import Examples.Independence.Clifford+CS.Syntactics    as CliffCS
import Examples.Independence.CNOT-Dihedral.Syntactics  as CNOTdihe

import Examples.Independence.Clifford.Semantics        as Cliff-Sem
import Examples.Independence.Real-Clifford.Semantics   as RCliff-Sem
import Examples.Independence.Qutrit-Clifford.Semantics as Cliff3-Sem
import Examples.Independence.Clifford+T.Semantics      as CliffT-Sem
import Examples.Independence.Clifford+CS.Semantics     as CliffCS-Sem
import Examples.Independence.CNOT-Dihedral.Semantics   as CNOTdihe-Sem

import Examples.Independence.Clifford.Minimality        as Cliff-Min
import Examples.Independence.Real-Clifford.Minimality   as RCliff-Min
import Examples.Independence.Qutrit-Clifford.Minimality as Cliff3-Min
import Examples.Independence.Clifford+T.Minimality      as CliffT-Min
import Examples.Independence.Clifford+CS.Minimality     as CliffCS-Min
import Examples.Independence.CNOT-Dihedral.Minimality   as CNOTdihe-Min

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Soundness for the matrix semantics (Section 3)

Cliff₂-sound : {w v : Cliff.Circuit n} →
               n Cliff.⊢ w ≈ v → Cliff-Sem.⟦ w ⟧ Cliff-Sem.≈ Cliff-Sem.⟦ v ⟧
Cliff₂-sound = Cliff-Sem.sound

RCliff₂-sound : {w v : RCliff.Circuit n} →
                n RCliff.⊢ w ≈ v → RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧
RCliff₂-sound = RCliff-Sem.sound

Cliff₃-sound : {w v : Cliff3.Circuit n} →
               n Cliff3.⊢ w ≈ v → Cliff3-Sem.⟦ w ⟧ Cliff3-Sem.≈ Cliff3-Sem.⟦ v ⟧
Cliff₃-sound = Cliff3-Sem.sound

CliffT₂-sound : {w v : CliffT.Circuit n} →
                n CliffT.⊢ w ≈ v → CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧
CliffT₂-sound = CliffT-Sem.sound

CliffCS₂-sound : {w v : CliffCS.Circuit n} →
                 n CliffCS.⊢ w ≈ v → CliffCS-Sem.⟦ w ⟧ CliffCS-Sem.≈ CliffCS-Sem.⟦ v ⟧
CliffCS₂-sound = CliffCS-Sem.sound

CNOTdihe₂-sound : {w v : CNOTdihe.Circuit n} →
                  n CNOTdihe.⊢ w ≈ v → CNOTdihe-Sem.⟦ w ⟧ CNOTdihe-Sem.≈ CNOTdihe-Sem.⟦ v ⟧
CNOTdihe₂-sound = CNOTdihe-Sem.sound

------------------------------------------------------------------------
-- Theorem 37

-- 1. Cliff₂ is minimal (all arities).
Cliff₂-minimal : Cliff.Minimal
Cliff₂-minimal = Cliff-Min.minimal

-- 2. RCliff₂ is minimal (all arities).
RCliff₂-minimal : RCliff.Minimal
RCliff₂-minimal = RCliff-Min.minimal

-- 3. Cliff₃ is minimal up to two qutrit wires.
Cliff₃-minimal-upto-2 : Cliff3.Minimal-upto 2
Cliff₃-minimal-upto-2 = Cliff3-Min.minimal-upto-2

-- 4. CliffT₂ is minimal up to one qubit wire, and its two-qubit axioms
-- (CPh), (B) and (CZ) are independent.
CliffT₂-minimal-upto-1 : CliffT.Minimal-upto 1
CliffT₂-minimal-upto-1 = CliffT-Min.minimal-upto-1

CliffT₂-CPh-independent : CliffT.Independent-axiom CliffT.CPh
CliffT₂-CPh-independent = CliffT-Min.CPh-independent

CliffT₂-B-independent : CliffT.Independent-axiom CliffT.B
CliffT₂-B-independent = CliffT-Min.B-independent

CliffT₂-CZ-independent : CliffT.Independent-axiom CliffT.CZ
CliffT₂-CZ-independent = CliffT-Min.CZ-independent

-- 5. CliffCS₂ is minimal up to two qubit wires, and its three-qubit
-- axiom (I) is independent.
CliffCS₂-minimal-upto-2 : CliffCS.Minimal-upto 2
CliffCS₂-minimal-upto-2 = CliffCS-Min.minimal-upto-2

CliffCS₂-I-independent : CliffCS.Independent-axiom CliffCS.I
CliffCS₂-I-independent = CliffCS-Min.I-independent

-- 6. CNOTdihe₂ is minimal (all arities).
CNOTdihe₂-minimal : CNOTdihe.Minimal
CNOTdihe₂-minimal = CNOTdihe-Min.minimal
