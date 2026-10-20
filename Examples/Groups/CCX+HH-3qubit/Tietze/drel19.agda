{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel19 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; X1 ; X2 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_c as bifunct_X_c
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_c as bifunct_Z_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel133 as drel133
import Examples.Groups.CCX+HH-3qubit.Tietze.drel30 as drel30
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.drel65 as drel65
import Examples.Groups.CCX+HH-3qubit.Tietze.drel66 as drel66

step0 : Z2 • CX12 ≈ K12 • K12 • Z2 • CX12
step0 = by-assoc-and (under (ε) (Z2 • CX12) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • Z2 • CX12 ≈ K12 • X2 • K12 • CX12
step1 = by-assoc-and (under (K12) (CX12) (sym (drel64.proved))) Eq.refl Eq.refl

step2 : K12 • X2 • K12 • CX12 ≈ K12 • X2 • CX21 • K12
step2 = by-assoc-and (under (K12 • X2) (ε) (sym (drel30.proved))) Eq.refl Eq.refl

step3 : K12 • X2 • CX21 • K12 ≈ K12 • CX21 • X1 • X2 • K12
step3 = by-assoc-and (under (K12) (K12) (drel133.proved)) Eq.refl Eq.refl

step4 : K12 • CX21 • X1 • X2 • K12 ≈ K12 • CX21 • X2 • X1 • K12
step4 = by-assoc-and (under (K12 • CX21) (K12) (bifunct_X_c.proved)) Eq.refl Eq.refl

step5 : K12 • CX21 • X2 • X1 • K12 ≈ CX12 • K12 • X2 • X1 • K12
step5 = by-assoc-and (under (ε) (X2 • X1 • K12) (drel46.proved)) Eq.refl Eq.refl

step6 : CX12 • K12 • X2 • X1 • K12 ≈ CX12 • Z2 • K12 • X1 • K12
step6 = by-assoc-and (under (CX12) (X1 • K12) (drel66.proved)) Eq.refl Eq.refl

step7 : CX12 • Z2 • K12 • X1 • K12 ≈ CX12 • Z2 • Z1 • K12 • K12
step7 = by-assoc-and (under (CX12 • Z2) (K12) (drel65.proved)) Eq.refl Eq.refl

step8 : CX12 • Z2 • Z1 • K12 • K12 ≈ CX12 • Z2 • Z1
step8 = by-assoc-and (under (CX12 • Z2 • Z1) (ε) (axiom r023)) Eq.refl Eq.refl

step9 : CX12 • Z2 • Z1 ≈ CX12 • Z1 • Z2
step9 = by-assoc-and (under (CX12) (ε) (sym (bifunct_Z_c.proved))) Eq.refl Eq.refl

proved : Z2 • CX12 ≈ CX12 • Z1 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))
