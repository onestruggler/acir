------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026), CNOT-dihedral circuits (CNOTdihe₂): the main theorem,
-- for MainTheorems
--
-- CNOTdihe₂'s rule set is complete at every width (Theorem 22, by
-- transfer from Amy, Chen and Ross's presentation: Completeness) and no
-- axiom follows from the others (Theorem 37: Minimality).  The matrix
-- semantics being sound (Semantics), each such axiom is then necessary
-- for completeness on its own wires: the rule set is minimal
-- (MinimalComplete).  This module collects what MainTheorems states,
-- behind one import: the rule set on n wires (_⊢_===_), completeness
-- and minimality, and the theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.CNOT-Dihedral.MainTheorem where

open import Data.Product.Base using (_×_ ; _,_)

open import Examples.Independence.CNOT-Dihedral.Syntactics using (Gate ; _SRel,_===_)
open import Examples.Independence.CNOT-Dihedral.Syntactics public using (Circuit)
open import Examples.Independence.CNOT-Dihedral.Semantics public using (⟦_⟧ ; _≈_)
import Examples.Independence.CNOT-Dihedral.Completeness as Cpl
import Examples.Independence.CNOT-Dihedral.Minimality as Min
import Examples.Independence.CNOT-Dihedral.Semantics as Sem
import Examples.Independence.MinimalComplete as MC

------------------------------------------------------------------------
-- The rule set, complete and minimal

module R = MC.Rule-Set Gate _SRel,_===_ ⟦_⟧ _≈_ Sem.sound
open R public using (_⊢_===_ ; IsRuleSet ; rule-set ; _IsComplete ; _IsMinimal)

minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
minimal-complete = R.minimal Min.minimal , Cpl.complete
