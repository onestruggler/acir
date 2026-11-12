------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026), Clifford+T circuits (CliffT₂): the main theorem, for
-- MainTheorems
--
-- CliffT₂'s rule set is complete on at most two wires (Theorem 22, by
-- transfer from Bian and Selinger's two-qubit presentation and the
-- two-level presentations: Completeness), and no axiom of arity at most
-- one follows from the others (Theorem 37: Minimality; (CSH), (HT²) and
-- (HTH) have no separator).  The matrix semantics being sound
-- (Semantics), each such axiom is then necessary for completeness on
-- its own wires: the rule set is minimal (MinimalComplete).  This
-- module collects what MainTheorems states, behind one import: the rule
-- set on n wires (_⊢_===_), completeness and minimality, and the
-- theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.MainTheorem where

open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_ ; _,_)

open import Examples.Independence.Clifford+T.Syntactics using (Gate ; _SRel,_===_)
open import Examples.Independence.Clifford+T.Syntactics public using (Circuit)
open import Examples.Independence.Clifford+T.Semantics public using (⟦_⟧ ; _≈_)
import Examples.Independence.Clifford+T.Completeness as Cpl
import Examples.Independence.Clifford+T.Minimality as Min
import Examples.Independence.Clifford+T.Semantics as Sem
import Examples.Independence.MinimalComplete as MC

------------------------------------------------------------------------
-- The rule set, complete and minimal

module R = MC.Rule-Set Gate _SRel,_===_ ⟦_⟧ _≈_ Sem.sound
open R public using (_⊢_===_ ; IsRuleSet ; rule-set ; _IsComplete ; _IsMinimal)

minimal-complete : ∀ {n} → (n ≤ 1 → (n ⊢_===_) IsMinimal) × (n ≤ 2 → (n ⊢_===_) IsComplete)
minimal-complete = R.minimal-upto Min.minimal-upto-1 , Cpl.complete
