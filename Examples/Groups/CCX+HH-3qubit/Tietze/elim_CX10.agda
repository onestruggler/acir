{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : CX10 • CX10 ≈ CX10 • K01 • CX01 • K01
step0 = by-assoc-and (under (CX10) (ε) (axiom r012)) Eq.refl Eq.refl

step1 : CX10 • K01 • CX01 • K01 ≈ K01 • CX01 • K01 • K01 • CX01 • K01
step1 = by-assoc-and (under (ε) (K01 • CX01 • K01) (axiom r012)) Eq.refl Eq.refl

step2 : K01 • CX01 • K01 • K01 • CX01 • K01 ≈ K01 • CX01 • CX01 • K01
step2 = by-assoc-and (under (K01 • CX01) (CX01 • K01) (axiom r025)) Eq.refl Eq.refl

step3 : K01 • CX01 • CX01 • K01 ≈ K01 • K01
step3 = by-assoc-and (under (K01) (K01) (axiom r022)) Eq.refl Eq.refl

step4 : K01 • K01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (axiom r025)) Eq.refl Eq.refl

proved : CX10 • CX10 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
