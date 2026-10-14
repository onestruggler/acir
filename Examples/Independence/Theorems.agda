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
-- Completeness (Section 4, Theorem 22) is transferred from the source
-- presentations, several of which this library proves complete in
-- their own developments.  It is formalised for Cliff₂, from Selinger's
-- presentation (Clifford.Completeness, through the paper's Appendices A
-- and G.1 and a bridge between the two matrix semantics), for RCliff₂,
-- from Makary, Ross and Selinger's (Real-Clifford.Completeness, the
-- same way), and for CNOTdihe₂, from Amy, Chen and Ross's
-- (CNOT-Dihedral.Completeness), so that all three are minimal complete
-- presentations of their semantics; for CliffT₂ up to two wires,
-- from Bian and Selinger's two-qubit presentation and the two-level
-- presentations of U₂ and U₁ over ℤ[1/√2,i] (Clifford+T.Completeness);
-- for CliffCS₂ up to three wires, from Bian and Selinger's
-- three-qubit presentation and the two-level presentations of U₄, U₂
-- and U₁ over ℤ[½,i], with the sources' scalars i refined to ω
-- (Clifford+CS.Completeness); and for Cliff₃ at every width, from the
-- presentation of the qutrit Clifford group modulo scalars by the rules
-- of Paper-V0 at p = 3, whose decodings hold up to powers of ω, which
-- the matrices then pin down (Qutrit-Clifford.Completeness).
--
-- Two departures from the paper.  The scalar of the qutrit axiom (E)
-- is printed ω₁₂⁷ in Figure 4, which is unsound for the semantics of
-- Section 3.2; it is ω₁₂ here.  And the separator #{CX, σ}[2] of the
-- Clifford axiom (CZ) does not respect the three-wire (I), but need not:
-- a derivation between two-wire circuits uses no three-wire axiom
-- (Prop.truncate, Remark 14), which is how every bounded separator is
-- applied here.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Theorems where

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Nullary.Negation using (¬_)

import Examples.Independence.Necessity as Necessity

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

import Examples.Independence.Clifford.Completeness      as Cliff-Cpl
import Examples.Independence.Real-Clifford.Completeness as RCliff-Cpl
import Examples.Independence.Qutrit-Clifford.Completeness as Cliff3-Cpl
import Examples.Independence.Clifford+T.Completeness     as CliffT-Cpl
import Examples.Independence.Clifford+CS.Completeness    as CliffCS-Cpl
import Examples.Independence.CNOT-Dihedral.Completeness as CNOTdihe-Cpl

private
  variable
    n : ℕ

-- The independence of each rule set's axioms.
module Cliff-Ax    = Cliff.Axioms Cliff._SRel,_===_
module RCliff-Ax   = RCliff.Axioms RCliff._SRel,_===_
module Cliff3-Ax   = Cliff3.Axioms Cliff3._SRel,_===_
module CliffT-Ax   = CliffT.Axioms CliffT._SRel,_===_
module CliffCS-Ax  = CliffCS.Axioms CliffCS._SRel,_===_
module CNOTdihe-Ax = CNOTdihe.Axioms CNOTdihe._SRel,_===_

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
Cliff₂-minimal : Cliff-Ax.Minimal
Cliff₂-minimal = Cliff-Min.minimal

-- 2. RCliff₂ is minimal (all arities).
RCliff₂-minimal : RCliff-Ax.Minimal
RCliff₂-minimal = RCliff-Min.minimal

-- 3. Cliff₃ is minimal up to two qutrit wires.
Cliff₃-minimal-upto-2 : Cliff3-Ax.Minimal-upto 2
Cliff₃-minimal-upto-2 = Cliff3-Min.minimal-upto-2

-- 4. CliffT₂ is minimal up to one qubit wire, and its two-qubit axioms
-- (CPh), (B) and (CZ) are independent.
CliffT₂-minimal-upto-1 : CliffT-Ax.Minimal-upto 1
CliffT₂-minimal-upto-1 = CliffT-Min.minimal-upto-1

CliffT₂-CPh-independent : CliffT-Ax.Independent-axiom CliffT.CPh
CliffT₂-CPh-independent = CliffT-Min.CPh-independent

CliffT₂-B-independent : CliffT-Ax.Independent-axiom CliffT.B
CliffT₂-B-independent = CliffT-Min.B-independent

CliffT₂-CZ-independent : CliffT-Ax.Independent-axiom CliffT.CZ
CliffT₂-CZ-independent = CliffT-Min.CZ-independent

-- 5. CliffCS₂ is minimal up to two qubit wires, and its three-qubit
-- axiom (I) is independent.
CliffCS₂-minimal-upto-2 : CliffCS-Ax.Minimal-upto 2
CliffCS₂-minimal-upto-2 = CliffCS-Min.minimal-upto-2

CliffCS₂-I-independent : CliffCS-Ax.Independent-axiom CliffCS.I
CliffCS₂-I-independent = CliffCS-Min.I-independent

-- 6. CNOTdihe₂ is minimal (all arities).
CNOTdihe₂-minimal : CNOTdihe-Ax.Minimal
CNOTdihe₂-minimal = CNOTdihe-Min.minimal

------------------------------------------------------------------------
-- Minimality against the matrix semantics (Section 5.1)
--
-- Every rule set is sound, so an independent axiom is necessary for
-- completeness: the other axioms do not derive every equation between
-- circuits on its wires that the matrices validate.

module Cliff-M    = Necessity.Fragment-Semantics Cliff.Gate Cliff._SRel,_===_
                      Cliff-Sem.⟦_⟧ Cliff-Sem._≈_ Cliff-Sem.sound
module RCliff-M   = Necessity.Fragment-Semantics RCliff.Gate RCliff._SRel,_===_
                      RCliff-Sem.⟦_⟧ RCliff-Sem._≈_ RCliff-Sem.sound
module Cliff3-M   = Necessity.Fragment-Semantics Cliff3.Gate Cliff3._SRel,_===_
                      Cliff3-Sem.⟦_⟧ Cliff3-Sem._≈_ Cliff3-Sem.sound
module CliffT-M   = Necessity.Fragment-Semantics CliffT.Gate CliffT._SRel,_===_
                      CliffT-Sem.⟦_⟧ CliffT-Sem._≈_ CliffT-Sem.sound
module CliffCS-M  = Necessity.Fragment-Semantics CliffCS.Gate CliffCS._SRel,_===_
                      CliffCS-Sem.⟦_⟧ CliffCS-Sem._≈_ CliffCS-Sem.sound
module CNOTdihe-M = Necessity.Fragment-Semantics CNOTdihe.Gate CNOTdihe._SRel,_===_
                      CNOTdihe-Sem.⟦_⟧ CNOTdihe-Sem._≈_ CNOTdihe-Sem.sound

Cliff₂-necessary : ∀ {n} {w v : Cliff.Circuit n} (ρ : Cliff._SRel,_===_ n w v) →
                   ¬ Cliff-M.Complete-without ρ n
Cliff₂-necessary ρ = Cliff-M.necessary ρ (Cliff₂-minimal ρ)

RCliff₂-necessary : ∀ {n} {w v : RCliff.Circuit n} (ρ : RCliff._SRel,_===_ n w v) →
                    ¬ RCliff-M.Complete-without ρ n
RCliff₂-necessary ρ = RCliff-M.necessary ρ (RCliff₂-minimal ρ)

Cliff₃-necessary : ∀ {n} {w v : Cliff3.Circuit n} (ρ : Cliff3._SRel,_===_ n w v) →
                   n ≤ 2 → ¬ Cliff3-M.Complete-without ρ n
Cliff₃-necessary ρ n≤2 = Cliff3-M.necessary ρ (Cliff₃-minimal-upto-2 ρ n≤2)

CliffT₂-necessary : ∀ {n} {w v : CliffT.Circuit n} (ρ : CliffT._SRel,_===_ n w v) →
                    n ≤ 1 → ¬ CliffT-M.Complete-without ρ n
CliffT₂-necessary ρ n≤1 = CliffT-M.necessary ρ (CliffT₂-minimal-upto-1 ρ n≤1)

CliffCS₂-necessary : ∀ {n} {w v : CliffCS.Circuit n} (ρ : CliffCS._SRel,_===_ n w v) →
                     n ≤ 2 → ¬ CliffCS-M.Complete-without ρ n
CliffCS₂-necessary ρ n≤2 = CliffCS-M.necessary ρ (CliffCS₂-minimal-upto-2 ρ n≤2)

CNOTdihe₂-necessary : ∀ {n} {w v : CNOTdihe.Circuit n} (ρ : CNOTdihe._SRel,_===_ n w v) →
                      ¬ CNOTdihe-M.Complete-without ρ n
CNOTdihe₂-necessary ρ = CNOTdihe-M.necessary ρ (CNOTdihe₂-minimal ρ)

------------------------------------------------------------------------
-- Completeness by transfer (Section 4, Theorem 22)

-- 1. Cliff₂ is complete, at every width: its axioms derive Selinger's,
-- decoded (Appendices A and G.1), whose presentation is complete.
Cliff₂-complete : {w v : Cliff.Circuit n} →
                  Cliff-Sem.⟦ w ⟧ Cliff-Sem.≈ Cliff-Sem.⟦ v ⟧ → n Cliff.⊢ w ≈ v
Cliff₂-complete = Cliff-Cpl.complete

-- So Cliff₂ is a minimal complete presentation.
Cliff₂-minimal-complete :
  (∀ {n} {w v : Cliff.Circuit n} →
     Cliff-Sem.⟦ w ⟧ Cliff-Sem.≈ Cliff-Sem.⟦ v ⟧ → n Cliff.⊢ w ≈ v) ×
  (∀ {n} {w v : Cliff.Circuit n} (ρ : Cliff._SRel,_===_ n w v) →
     ¬ Cliff-M.Complete-without ρ n)
Cliff₂-minimal-complete = Cliff₂-complete , Cliff₂-necessary

-- 2. RCliff₂ is complete, at every width: its axioms derive Makary, Ross
-- and Selinger's, decoded (Appendices D.2 and G.2; (R14)–(R16) from the
-- decoded (C13)–(C15), whose relators theirs rotate), whose
-- presentation is complete.
RCliff₂-complete : {w v : RCliff.Circuit n} →
                   RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧ → n RCliff.⊢ w ≈ v
RCliff₂-complete = RCliff-Cpl.complete

-- So RCliff₂ is a minimal complete presentation.
RCliff₂-minimal-complete :
  (∀ {n} {w v : RCliff.Circuit n} →
     RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧ → n RCliff.⊢ w ≈ v) ×
  (∀ {n} {w v : RCliff.Circuit n} (ρ : RCliff._SRel,_===_ n w v) →
     ¬ RCliff-M.Complete-without ρ n)
RCliff₂-minimal-complete = RCliff₂-complete , RCliff₂-necessary

-- 3. Cliff₃ is complete, at every width: Paper-V0's rules at p = 3
-- present the qutrit Clifford group modulo scalars (ProjectiveClifford.
-- Qupit), and its axioms derive them, decoded, up to powers of ω (the
-- paper's Appendix on qutrit Clifford circuits, and Knuth–Bendix
-- completion on one wire); two circuits with equal matrices are then
-- equal up to a power of ω, which has the identity's matrix and so is
-- ε.
Cliff₃-complete : {w v : Cliff3.Circuit n} →
                  Cliff3-Sem.⟦ w ⟧ Cliff3-Sem.≈ Cliff3-Sem.⟦ v ⟧ → n Cliff3.⊢ w ≈ v
Cliff₃-complete = Cliff3-Cpl.complete

-- So Cliff₃ is complete, and a minimal complete presentation on two
-- wires.
Cliff₃-minimal-complete-upto-2 :
  (∀ {n} {w v : Cliff3.Circuit n} →
     Cliff3-Sem.⟦ w ⟧ Cliff3-Sem.≈ Cliff3-Sem.⟦ v ⟧ → n Cliff3.⊢ w ≈ v) ×
  (∀ {n} {w v : Cliff3.Circuit n} (ρ : Cliff3._SRel,_===_ n w v) →
     n ≤ 2 → ¬ Cliff3-M.Complete-without ρ n)
Cliff₃-minimal-complete-upto-2 = Cliff₃-complete , Cliff₃-necessary

-- 4. CliffT₂ is complete up to two qubit wires: on two, its axioms
-- derive Bian and Selinger's, decoded (Appendices D.3 and G.4), whose
-- presentation is complete; on one and on none, the two-level
-- relations in dimensions 2 and 1, decoded.
CliffT₂-complete : {w v : CliffT.Circuit n} → n ≤ 2 →
                   CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧ → n CliffT.⊢ w ≈ v
CliffT₂-complete n≤2 = CliffT-Cpl.complete n≤2

-- So CliffT₂ is a minimal complete presentation on one wire, and
-- complete on two.
CliffT₂-minimal-complete-upto-1 :
  (∀ {n} {w v : CliffT.Circuit n} → n ≤ 2 →
     CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧ → n CliffT.⊢ w ≈ v) ×
  (∀ {n} {w v : CliffT.Circuit n} (ρ : CliffT._SRel,_===_ n w v) →
     n ≤ 1 → ¬ CliffT-M.Complete-without ρ n)
CliffT₂-minimal-complete-upto-1 = CliffT₂-complete , CliffT₂-necessary

-- 5. CliffCS₂ is complete up to three qubit wires: on three, its axioms
-- derive Bian and Selinger's, decoded (Appendices D.5 and G.5), whose
-- presentation is complete; on two, one and none, the two-level
-- relations in dimensions 4, 2 and 1, decoded.  On two wires only the
-- axioms of arity at most two are available, and every instance of a
-- relation is a relabelling of one (Clifford+CS.TwoWire).  The sources'
-- scalars are the powers of i, CliffCS₂'s those of ω (Clifford+CS.
-- Assemble).
CliffCS₂-complete : {w v : CliffCS.Circuit n} → n ≤ 3 →
                    CliffCS-Sem.⟦ w ⟧ CliffCS-Sem.≈ CliffCS-Sem.⟦ v ⟧ → n CliffCS.⊢ w ≈ v
CliffCS₂-complete n≤3 = CliffCS-Cpl.complete n≤3

-- So CliffCS₂ is a minimal complete presentation on two wires, and
-- complete on three.
CliffCS₂-minimal-complete-upto-2 :
  (∀ {n} {w v : CliffCS.Circuit n} → n ≤ 3 →
     CliffCS-Sem.⟦ w ⟧ CliffCS-Sem.≈ CliffCS-Sem.⟦ v ⟧ → n CliffCS.⊢ w ≈ v) ×
  (∀ {n} {w v : CliffCS.Circuit n} (ρ : CliffCS._SRel,_===_ n w v) →
     n ≤ 2 → ¬ CliffCS-M.Complete-without ρ n)
CliffCS₂-minimal-complete-upto-2 = CliffCS₂-complete , CliffCS₂-necessary

-- 6. CNOTdihe₂ is complete, at every width: its axioms derive Amy,
-- Chen and Ross's, whose presentation is complete.
CNOTdihe₂-complete : {w v : CNOTdihe.Circuit n} →
                     CNOTdihe-Sem.⟦ w ⟧ CNOTdihe-Sem.≈ CNOTdihe-Sem.⟦ v ⟧ →
                     n CNOTdihe.⊢ w ≈ v
CNOTdihe₂-complete = CNOTdihe-Cpl.complete

-- So CNOTdihe₂ is a minimal complete presentation: complete at every
-- width, and without any one of its axioms no longer complete on that
-- axiom's wires.
CNOTdihe₂-minimal-complete :
  (∀ {n} {w v : CNOTdihe.Circuit n} →
     CNOTdihe-Sem.⟦ w ⟧ CNOTdihe-Sem.≈ CNOTdihe-Sem.⟦ v ⟧ → n CNOTdihe.⊢ w ≈ v) ×
  (∀ {n} {w v : CNOTdihe.Circuit n} (ρ : CNOTdihe._SRel,_===_ n w v) →
     ¬ CNOTdihe-M.Complete-without ρ n)
CNOTdihe₂-minimal-complete = CNOTdihe₂-complete , CNOTdihe₂-necessary
