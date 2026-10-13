{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : Z0 • Z0 ≈ K01 • K01 • Z0 • Z0
step0 = by-assoc-and (under (ε) (Z0 • Z0) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z0 • Z0 ≈ K01 • X0 • K01 • Z0
step1 = by-assoc-and (under (K01) (Z0) (axiom r041)) Eq.refl Eq.refl

step2 : K01 • X0 • K01 • Z0 ≈ K01 • X0 • X0 • K01
step2 = by-assoc-and (under (K01 • X0) (ε) (axiom r041)) Eq.refl Eq.refl

step3 : K01 • X0 • X0 • K01 ≈ K01 • K01
step3 = by-assoc-and (under (K01) (K01) (axiom r021)) Eq.refl Eq.refl

step4 : K01 • K01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (axiom r025)) Eq.refl Eq.refl

proved : Z0 • Z0 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
