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
-- from Makary, Ross and Selinger's (Real-Clifford.Completeness, through
-- Appendix B and the decodings of G.2), and for CNOTdihe₂, from Amy,
-- Chen and Ross's (CNOT-Dihedral.Completeness), so that all three are
-- minimal complete presentations of their semantics; and for CliffT₂
-- up to two qubits, from Bian and Selinger's 2-qubit presentation and,
-- on one wire, Greylyn's two-level one (Clifford+T.Completeness, through
-- Appendices D and G.4), so that it is complete up to two qubits and
-- minimal up to one.
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

open import Data.Nat.Base using (ℕ ; _+_ ; _≤_)
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
import Examples.Independence.Clifford+T.Completeness   as CliffT-Cpl
import Examples.Independence.CNOT-Dihedral.Completeness as CNOTdihe-Cpl

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

------------------------------------------------------------------------
-- Minimality against the matrix semantics (Section 5.1)
--
-- Every rule set is sound, so an independent axiom is necessary for
-- completeness: the other axioms do not derive every equation between
-- circuits on its wires that the matrices validate.

module Cliff-M    = Necessity.Fragment-Semantics Cliff.Gate Cliff.arity Cliff.lhs Cliff.rhs
                      Cliff-Sem.⟦_⟧ Cliff-Sem._≈_ Cliff-Sem.sound
module RCliff-M   = Necessity.Fragment-Semantics RCliff.Gate RCliff.arity RCliff.lhs RCliff.rhs
                      RCliff-Sem.⟦_⟧ RCliff-Sem._≈_ RCliff-Sem.sound
module Cliff3-M   = Necessity.Fragment-Semantics Cliff3.Gate Cliff3.arity Cliff3.lhs Cliff3.rhs
                      Cliff3-Sem.⟦_⟧ Cliff3-Sem._≈_ Cliff3-Sem.sound
module CliffT-M   = Necessity.Fragment-Semantics CliffT.Gate CliffT.arity CliffT.lhs CliffT.rhs
                      CliffT-Sem.⟦_⟧ CliffT-Sem._≈_ CliffT-Sem.sound
module CliffCS-M  = Necessity.Fragment-Semantics CliffCS.Gate CliffCS.arity CliffCS.lhs CliffCS.rhs
                      CliffCS-Sem.⟦_⟧ CliffCS-Sem._≈_ CliffCS-Sem.sound
module CNOTdihe-M = Necessity.Fragment-Semantics CNOTdihe.Gate CNOTdihe.arity CNOTdihe.lhs CNOTdihe.rhs
                      CNOTdihe-Sem.⟦_⟧ CNOTdihe-Sem._≈_ CNOTdihe-Sem.sound

Cliff₂-necessary : ∀ ρ → ¬ Cliff-M.Complete-without ρ (Cliff.arity ρ + 0)
Cliff₂-necessary ρ = Cliff-M.necessary ρ (Cliff₂-minimal ρ)

RCliff₂-necessary : ∀ ρ → ¬ RCliff-M.Complete-without ρ (RCliff.arity ρ + 0)
RCliff₂-necessary ρ = RCliff-M.necessary ρ (RCliff₂-minimal ρ)

Cliff₃-necessary : ∀ ρ → Cliff3.arity ρ ≤ 2 →
                   ¬ Cliff3-M.Complete-without ρ (Cliff3.arity ρ + 0)
Cliff₃-necessary ρ ar≤2 = Cliff3-M.necessary ρ (Cliff₃-minimal-upto-2 ρ ar≤2)

CliffT₂-necessary : ∀ ρ → CliffT.arity ρ ≤ 1 →
                    ¬ CliffT-M.Complete-without ρ (CliffT.arity ρ + 0)
CliffT₂-necessary ρ ar≤1 = CliffT-M.necessary ρ (CliffT₂-minimal-upto-1 ρ ar≤1)

CliffCS₂-necessary : ∀ ρ → CliffCS.arity ρ ≤ 2 →
                     ¬ CliffCS-M.Complete-without ρ (CliffCS.arity ρ + 0)
CliffCS₂-necessary ρ ar≤2 = CliffCS-M.necessary ρ (CliffCS₂-minimal-upto-2 ρ ar≤2)

CNOTdihe₂-necessary : ∀ ρ → ¬ CNOTdihe-M.Complete-without ρ (CNOTdihe.arity ρ + 0)
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
  (∀ ρ → ¬ Cliff-M.Complete-without ρ (Cliff.arity ρ + 0))
Cliff₂-minimal-complete = Cliff₂-complete , Cliff₂-necessary

-- 2. RCliff₂ is complete, at every width: its axioms derive Makary,
-- Ross and Selinger's, decoded (Appendix B, with (R13)–(R16) derived
-- here), whose presentation is complete.
RCliff₂-complete : {w v : RCliff.Circuit n} →
                   RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧ → n RCliff.⊢ w ≈ v
RCliff₂-complete = RCliff-Cpl.complete

-- So RCliff₂ is a minimal complete presentation.
RCliff₂-minimal-complete :
  (∀ {n} {w v : RCliff.Circuit n} →
     RCliff-Sem.⟦ w ⟧ RCliff-Sem.≈ RCliff-Sem.⟦ v ⟧ → n RCliff.⊢ w ≈ v) ×
  (∀ ρ → ¬ RCliff-M.Complete-without ρ (RCliff.arity ρ + 0))
RCliff₂-minimal-complete = RCliff₂-complete , RCliff₂-necessary

-- 4. CliffT₂ is complete up to two qubits: on two wires its axioms
-- derive Bian and Selinger's, decoded (Appendices D and G.4), on one
-- wire Greylyn's at n = 2, and both presentations are complete; on no
-- wires a circuit is a power of ω.
CliffT₂-complete : n ≤ 2 → {w v : CliffT.Circuit n} →
                   CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧ → n CliffT.⊢ w ≈ v
CliffT₂-complete = CliffT-Cpl.complete

-- So CliffT₂ is complete up to two qubits and minimal up to one: each
-- one-wire axiom is needed for completeness on one wire.
CliffT₂-minimal-complete :
  (∀ {n} → n ≤ 2 → {w v : CliffT.Circuit n} →
     CliffT-Sem.⟦ w ⟧ CliffT-Sem.≈ CliffT-Sem.⟦ v ⟧ → n CliffT.⊢ w ≈ v) ×
  (∀ ρ → CliffT.arity ρ ≤ 1 → ¬ CliffT-M.Complete-without ρ (CliffT.arity ρ + 0))
CliffT₂-minimal-complete = CliffT₂-complete , CliffT₂-necessary

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
  (∀ ρ → ¬ CNOTdihe-M.Complete-without ρ (CNOTdihe.arity ρ + 0))
CNOTdihe₂-minimal-complete = CNOTdihe₂-complete , CNOTdihe₂-necessary
