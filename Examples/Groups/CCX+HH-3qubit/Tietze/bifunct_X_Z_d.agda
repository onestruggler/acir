{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_d where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K12 ; X1 ; X2 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_c as bifunct_X_Z_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.drel65 as drel65
import Examples.Groups.CCX+HH-3qubit.Tietze.drel66 as drel66

step0 : X1 • Z2 ≈ K12 • K12 • X1 • Z2
step0 = by-assoc-and (under (ε) (X1 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • X1 • Z2 ≈ K12 • Z1 • K12 • Z2
step1 = by-assoc-and (under (K12) (Z2) (drel65.proved)) Eq.refl Eq.refl

step2 : K12 • Z1 • K12 • Z2 ≈ K12 • Z1 • X2 • K12
step2 = by-assoc-and (under (K12 • Z1) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

step3 : K12 • Z1 • X2 • K12 ≈ K12 • X2 • Z1 • K12
step3 = by-assoc-and (under (K12) (K12) (sym (bifunct_X_Z_c.proved))) Eq.refl Eq.refl

step4 : K12 • X2 • Z1 • K12 ≈ Z2 • K12 • Z1 • K12
step4 = by-assoc-and (under (ε) (Z1 • K12) (drel66.proved)) Eq.refl Eq.refl

step5 : Z2 • K12 • Z1 • K12 ≈ Z2 • X1 • K12 • K12
step5 = by-assoc-and (under (Z2) (K12) (sym (drel137.proved))) Eq.refl Eq.refl

step6 : Z2 • X1 • K12 • K12 ≈ Z2 • X1
step6 = by-assoc-and (under (Z2 • X1) (ε) (axiom r023)) Eq.refl Eq.refl

proved : X1 • Z2 ≈ Z2 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
