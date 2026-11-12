------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026), qubit Clifford circuits (Cliff₂): the main theorem, for
-- MainTheorems
--
-- Cliff₂'s rule set is complete at every width (Theorem 22, by transfer
-- from Selinger's presentation: Completeness) and no axiom follows from
-- the others (Theorem 37: Minimality).  The matrix semantics being
-- sound (Semantics), each such axiom is then necessary for completeness
-- on its own wires: the rule set is minimal (MinimalComplete).  This
-- module collects what MainTheorems states, behind one import: the rule
-- set on n wires (_⊢_===_), completeness and minimality, and the
-- theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford.MainTheorem where

open import Data.Product.Base using (_×_ ; _,_)

open import Examples.Independence.Clifford.Syntactics using (Gate ; _SRel,_===_)
open import Examples.Independence.Clifford.Syntactics public using (Circuit)
open import Examples.Independence.Clifford.Semantics public using (⟦_⟧ ; _≈_)
import Examples.Independence.Clifford.Completeness as Cpl
import Examples.Independence.Clifford.Minimality as Min
import Examples.Independence.Clifford.Semantics as Sem
import Examples.Independence.MinimalComplete as MC

------------------------------------------------------------------------
-- The rule set, complete and minimal

module R = MC.Rule-Set Gate _SRel,_===_ ⟦_⟧ _≈_ Sem.sound
open R public using (_⊢_===_ ; IsRuleSet ; rule-set ; _IsComplete ; _IsMinimal)

minimal-complete : ∀ {n} → (n ⊢_===_) IsMinimal × (n ⊢_===_) IsComplete
minimal-complete = R.minimal Min.minimal , Cpl.complete
