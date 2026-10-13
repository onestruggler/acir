{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_b where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_K_b as bifunct_X_K_b
import Examples.Groups.CCX+HH-3qubit.Tietze.drel66 as drel66

step0 : Z2 • K01 ≈ Z2 • K12 • K12 • K01
step0 = by-assoc-and (under (Z2) (K01) (sym (axiom r023))) Eq.refl Eq.refl

step1 : Z2 • K12 • K12 • K01 ≈ K12 • X2 • K12 • K01
step1 = by-assoc-and (under (ε) (K12 • K01) (sym (drel66.proved))) Eq.refl Eq.refl

step2 : K12 • X2 • K12 • K01 ≈ K12 • X2 • K01 • K12
step2 = by-assoc-and (under (K12 • X2) (ε) (sym (axiom r039))) Eq.refl Eq.refl

step3 : K12 • X2 • K01 • K12 ≈ K12 • K01 • X2 • K12
step3 = by-assoc-and (under (K12) (K12) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

step4 : K12 • K01 • X2 • K12 ≈ K01 • K12 • X2 • K12
step4 = by-assoc-and (under (ε) (X2 • K12) (sym (axiom r039))) Eq.refl Eq.refl

step5 : K01 • K12 • X2 • K12 ≈ K01 • Z2 • K12 • K12
step5 = by-assoc-and (under (K01) (K12) (drel66.proved)) Eq.refl Eq.refl

step6 : K01 • Z2 • K12 • K12 ≈ K01 • Z2
step6 = by-assoc-and (under (K01 • Z2) (ε) (axiom r023)) Eq.refl Eq.refl

proved : Z2 • K01 ≈ K01 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
