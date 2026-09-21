------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma D.7 of Clément's paper: the twenty auxiliary equations on five
-- qubits, Equations (249)–(268), from completeness on two and three
-- qubits and the schema (19).  Typechecking this module checks all of
-- Appendix D.4.
--
-- The paper's conditional completeness on four qubits, Lemma D.6, is
-- not a parameter: no four-wire evaluation is used.  The families with
-- parametrised colours and signs, (263)–(268), are stated over Bool,
-- black being true.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.LemmaD7
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Examples.Groups.Real-Clifford+CH.FiveQubit.Auxiliary complete₂ complete₃ public
  using (eq249 ; eq250 ; eq251 ; eq252)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Colours complete₂ complete₃ public
  using (eq253 ; eq254 ; eq255 ; eq256 ; eq257 ; eq258 ; eq259 ; eq260)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations2 complete₂ complete₃ public
  using (eq261)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations complete₂ complete₃ public
  using (eq262)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies263 complete₂ complete₃ public
  using (eq263 ; eq264 ; eq265 ; eq266)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies267 complete₂ complete₃ public
  using (eq267)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies268 complete₂ complete₃ public
  using (eq268)
