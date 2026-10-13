{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_a where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : Z0 • K12 ≈ K01 • K01 • Z0 • K12
step0 = by-assoc-and (under (ε) (Z0 • K12) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z0 • K12 ≈ K01 • X0 • K01 • K12
step1 = by-assoc-and (under (K01) (K12) (axiom r041)) Eq.refl Eq.refl

step2 : K01 • X0 • K01 • K12 ≈ K01 • X0 • K12 • K01
step2 = by-assoc-and (under (K01 • X0) (ε) (axiom r039)) Eq.refl Eq.refl

step3 : K01 • X0 • K12 • K01 ≈ K01 • K12 • X0 • K01
step3 = by-assoc-and (under (K01) (K01) (axiom r027)) Eq.refl Eq.refl

step4 : K01 • K12 • X0 • K01 ≈ K12 • K01 • X0 • K01
step4 = by-assoc-and (under (ε) (X0 • K01) (axiom r039)) Eq.refl Eq.refl

step5 : K12 • K01 • X0 • K01 ≈ K12 • K01 • K01 • Z0
step5 = by-assoc-and (under (K12 • K01) (ε) (sym (axiom r041))) Eq.refl Eq.refl

step6 : K12 • K01 • K01 • Z0 ≈ K12 • Z0
step6 = by-assoc-and (under (K12) (Z0) (axiom r025)) Eq.refl Eq.refl

proved : Z0 • K12 ≈ K12 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
