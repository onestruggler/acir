------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness and completeness of the theory T on four wires
--
-- Four reduces completeness on four wires to the faithfulness of the
-- circuits that keep wire 3, and KFaithful proves it, so two
-- four-wire circuits over X, CX and CCX with the same function on the
-- sixteen states are equal by the rules of Figure 1 and the PROP laws;
-- and conversely (Semantics.sound).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Completeness where

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (⟦_⟧ ; _≐_)
import Examples.Groups.XCXCCX-4bit.Semantics as Sem
open import Examples.Groups.XCXCCX-4bit.KFaithful using (faithful₃)
import Examples.Groups.XCXCCX-4bit.Four as Four

-- Completeness: circuits with the same function are equal.
complete₄ : {u v : Circuit 4} → ⟦ u ⟧ ≐ ⟦ v ⟧ → 4 ⊢ u ≈ v
complete₄ = Four.complete₄ faithful₃

-- Soundness: equal circuits have the same function.
sound₄ : {u v : Circuit 4} → 4 ⊢ u ≈ v → ⟦ u ⟧ ≐ ⟦ v ⟧
sound₄ = Sem.sound
