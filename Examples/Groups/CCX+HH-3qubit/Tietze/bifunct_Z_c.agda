{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_c as bifunct_X_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64

step0 : Z1 • Z2 ≈ K12 • K12 • Z1 • Z2
step0 = by-assoc-and (under (ε) (Z1 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • Z1 • Z2 ≈ K12 • X1 • K12 • Z2
step1 = by-assoc-and (under (K12) (Z2) (sym (drel137.proved))) Eq.refl Eq.refl

step2 : K12 • X1 • K12 • Z2 ≈ K12 • X1 • X2 • K12
step2 = by-assoc-and (under (K12 • X1) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

step3 : K12 • X1 • X2 • K12 ≈ K12 • X2 • X1 • K12
step3 = by-assoc-and (under (K12) (K12) (bifunct_X_c.proved)) Eq.refl Eq.refl

step4 : K12 • X2 • X1 • K12 ≈ K12 • X2 • K12 • Z1
step4 = by-assoc-and (under (K12 • X2) (ε) (drel137.proved)) Eq.refl Eq.refl

step5 : K12 • X2 • K12 • Z1 ≈ K12 • K12 • Z2 • Z1
step5 = by-assoc-and (under (K12) (Z1) (drel64.proved)) Eq.refl Eq.refl

step6 : K12 • K12 • Z2 • Z1 ≈ Z2 • Z1
step6 = by-assoc-and (under (ε) (Z2 • Z1) (axiom r023)) Eq.refl Eq.refl

proved : Z1 • Z2 ≈ Z2 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
