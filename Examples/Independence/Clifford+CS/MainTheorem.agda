------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026), Clifford+CS circuits (CliffCS₂): the main theorem, for
-- MainTheorems
--
-- CliffCS₂'s rule set is complete on at most three wires (Theorem 22,
-- by transfer from Bian and Selinger's three-qubit presentation and the
-- two-level presentations: Completeness), and no axiom of arity at most
-- two follows from the others (Theorem 37: Minimality; (SH₀)–(SH₃) have
-- no separator).  The matrix semantics being sound (Semantics), each
-- such axiom is then necessary for completeness on its own wires: the
-- rule set is minimal (MinimalComplete).  This module collects what
-- MainTheorems states, behind one import: the rule set on n wires
-- (_⊢_===_), completeness and minimality, and the theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.MainTheorem where

open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_ ; _,_)

open import Examples.Independence.Clifford+CS.Syntactics using (Gate ; _SRel,_===_)
open import Examples.Independence.Clifford+CS.Syntactics public using (Circuit)
open import Examples.Independence.Clifford+CS.Semantics public using (⟦_⟧ ; _≈_)
import Examples.Independence.Clifford+CS.Completeness as Cpl
import Examples.Independence.Clifford+CS.Minimality as Min
import Examples.Independence.Clifford+CS.Semantics as Sem
import Examples.Independence.MinimalComplete as MC

------------------------------------------------------------------------
-- The rule set, complete and minimal

module R = MC.Rule-Set Gate _SRel,_===_ ⟦_⟧ _≈_ Sem.sound
open R public using (_⊢_===_ ; IsRuleSet ; rule-set ; _IsComplete ; _IsMinimal)

minimal-complete : ∀ {n} → (n ≤ 2 → (n ⊢_===_) IsMinimal) × (n ≤ 3 → (n ⊢_===_) IsComplete)
minimal-complete = R.minimal-upto Min.minimal-upto-2 , Cpl.complete
