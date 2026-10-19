------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- Three more of the cases of Soundness.soundness-base, which rewrite long
-- two-level words (12.7 s and 7.3 s): lemmas in modules of their own,
-- each typed Goal r for its relation r.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


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


module Examples.Groups.Clifford+CS-3qubit.Soundness.Long2 where

  Goal : ∀ {w v} -> w === v ∈ CliffordCS.Rel -> Set
  Goal {w} {v} _ = TwoLevel.Rel ⊢ (f ʷ) w === (f ʷ) v

  sb-long2 : Goal CliffordCS.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12
  sb-long2 = lemma-one-sided (rewrite-twolevel 1000 auto)

  sb-long3 : Goal CliffordCS.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12
  sb-long3 = lemma-one-sided (rewrite-twolevel 1000 auto)

  sb-long4 : Goal CliffordCS.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1
  sb-long4 = lemma-one-sided (rewrite-twolevel 1000 auto)

