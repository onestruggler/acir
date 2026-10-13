{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_b where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_e as bifunct_X_Z_e
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_b as bifunct_Z_K_b

step0 : Z0 • Z2 ≈ K01 • K01 • Z0 • Z2
step0 = by-assoc-and (under (ε) (Z0 • Z2) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z0 • Z2 ≈ K01 • X0 • K01 • Z2
step1 = by-assoc-and (under (K01) (Z2) (axiom r041)) Eq.refl Eq.refl

step2 : K01 • X0 • K01 • Z2 ≈ K01 • X0 • Z2 • K01
step2 = by-assoc-and (under (K01 • X0) (ε) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

step3 : K01 • X0 • Z2 • K01 ≈ K01 • Z2 • X0 • K01
step3 = by-assoc-and (under (K01) (K01) (bifunct_X_Z_e.proved)) Eq.refl Eq.refl

step4 : K01 • Z2 • X0 • K01 ≈ Z2 • K01 • X0 • K01
step4 = by-assoc-and (under (ε) (X0 • K01) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

step5 : Z2 • K01 • X0 • K01 ≈ Z2 • K01 • K01 • Z0
step5 = by-assoc-and (under (Z2 • K01) (ε) (sym (axiom r041))) Eq.refl Eq.refl

step6 : Z2 • K01 • K01 • Z0 ≈ Z2 • Z0
step6 = by-assoc-and (under (Z2) (Z0) (axiom r025)) Eq.refl Eq.refl

proved : Z0 • Z2 ≈ Z2 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
