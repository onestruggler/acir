------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- The original was checked with --call-by-name, which saved memory
-- while the rewrite loops of Presentation.Tactics.Words returned their
-- unevaluated argument.  With those loops fixed, call-by-name only
-- loses sharing, and the default call-by-need is much faster.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module contains the proof of the main soundness theorem. The
-- statement of the theorem was already given in Theorem.agda (under
-- the name "soundness-property").
--
-- Soundness is proved by translating every basic Clifford+CS relation
-- w === v into a relation on the 2-level generators
-- (f ʷ) w === (f ʷ) v, and showing that the latter follows from
-- the corresponding axioms. This is basically a large case distinction.

open import Presentation.Tactics.Equality as Eq using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index
open import Examples.Groups.Clifford+CS-3qubit.TwoLevel-Lemmas
open TwoLevel-Rewrite-Twolevel
open Inverse-TwoLevel

open import Examples.Groups.Clifford+CS-3qubit.Theorem
open TwoLevel
open CliffordCS hiding (Rel)

open Monoid-Equational

module Examples.Groups.Clifford+CS-3qubit.Soundness where

  -- Base case of the soundness theorem: The translation of every
  -- basic Clifford+CS relation is sound.
  soundness-base : ∀ {w v} -> w === v ∈ CliffordCS.Rel -> TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v
  soundness-base CliffordCS.ax-iI-iI-iI-iI=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-S0=S0-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-S1=S1-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-S2=S2-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-K0=K0-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-K1=K1-iI = rewrite-twolevel 200 auto
  soundness-base CliffordCS.ax-iI-K2=K2-iI = lemma-one-sided (rewrite-twolevel 1000 auto)
  soundness-base CliffordCS.ax-iI-CS01=CS01-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-iI-CS12=CS12-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S1-S0=S0-S1 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-S0=S0-S2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-S1=S1-S2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K1-K0=K0-K1 = lemma-K0K1 reversed
  soundness-base CliffordCS.ax-K2-K0=K0-K2 = lemma-K2K0
  soundness-base CliffordCS.ax-K2-K1=K1-K2 = lemma-K2K1

  soundness-base CliffordCS.ax-CS01-S0=S0-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-S0=S0-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-S1=S1-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-S1=S1-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-S2=S2-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-S2=S2-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-CS01=CS01-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S1-K0=K0-S1 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-K0=K0-S2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-K1=K1-S2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K1-S0=S0-K1 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K2-S0=S0-K2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K2-S1=S1-K2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-K2=K2-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-K0=K0-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S0-S0-S0-S0=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S1-S1-S1-S1=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-S2-S2-S2=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-CS01-CS01-CS01=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-CS12-CS12-CS12=ε = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K0-K0=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K1-K1=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-K2-K2=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S1-K1-S1-K1-S1-K1=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-S2-K2-S2-K2-S2-K2=iI-iI-iI = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-X0-CS01=CS01-CS01-CS01-X0-S1 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-X1-CS01=CS01-CS01-CS01-X1-S0 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-X1-CS12=CS12-CS12-CS12-X1-S2 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-X2-CS12=CS12-CS12-CS12-X2-S1 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12 = lemma-one-sided (rewrite-twolevel 4000 auto)
  soundness-base CliffordCS.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12 = lemma-one-sided (rewrite-twolevel 1000 auto)
  soundness-base CliffordCS.ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21 = rewrite-twolevel 100 auto
  soundness-base CliffordCS.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12 = lemma-one-sided (rewrite-twolevel 1000 auto)
  soundness-base CliffordCS.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1 = lemma-one-sided (rewrite-twolevel 1000 auto)
  
  -- Proof of the soundness theorem: All the work was done in the base
  -- cases. The rest is just an obvious induction.
  soundness : soundness-property
  soundness (axiom x) = soundness-base x
  soundness refl = refl
  soundness (symm deriv) = symm (soundness deriv)
  soundness (trans deriv deriv₁) = trans (soundness deriv) (soundness deriv₁)
  soundness (cong deriv deriv₁) = cong (soundness deriv) (soundness deriv₁)
  soundness assoc = assoc
  soundness left-unit = left-unit
  soundness right-unit = right-unit

