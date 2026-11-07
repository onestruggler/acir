------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026), qutrit Clifford circuits (Cliff₃): the main theorem,
-- for MainTheorems
--
-- Cliff₃'s rule set is complete at every width (Theorem 22, by transfer
-- from the rules of Paper-V0 at p = 3: Completeness), and no axiom of
-- arity at most two follows from the others (Theorem 37: Minimality;
-- the three-qutrit (I) has no separator).  The matrix semantics being
-- sound (Semantics), each such axiom is then necessary for completeness
-- on its own wires: the rule set is minimal (MinimalComplete).  This
-- module collects what MainTheorems states, behind one import: the rule
-- set on n wires (_⊢_===_), completeness and minimality, and the
-- theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Qutrit-Clifford.MainTheorem where

open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_ ; _,_)

open import Examples.Independence.Qutrit-Clifford.Syntactics using (Gate ; _SRel,_===_)
open import Examples.Independence.Qutrit-Clifford.Syntactics public using (Circuit)
open import Examples.Independence.Qutrit-Clifford.Semantics public using (⟦_⟧ ; _≈_)
import Examples.Independence.Qutrit-Clifford.Completeness as Cpl
import Examples.Independence.Qutrit-Clifford.Minimality as Min
import Examples.Independence.Qutrit-Clifford.Semantics as Sem
import Examples.Independence.MinimalComplete as MC

------------------------------------------------------------------------
-- The rule set, complete and minimal

module R = MC.Rule-Set Gate _SRel,_===_ ⟦_⟧ _≈_ Sem.sound
open R public using (_⊢_===_ ; IsRuleSet ; rule-set ; _IsComplete ; _IsMinimal)

minimal-complete : ∀ {n} → (n ≤ 2 → (n ⊢_===_) IsMinimal) × (n ⊢_===_) IsComplete
minimal-complete = R.minimal-upto Min.minimal-upto-2 , Cpl.complete
