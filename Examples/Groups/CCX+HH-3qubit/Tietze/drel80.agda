{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel80 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; X1 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel30 as drel30
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.drel65 as drel65
import Examples.Groups.CCX+HH-3qubit.Tietze.drel79 as drel79

step0 : CX12 • Z1 ≈ K12 • K12 • CX12 • Z1
step0 = by-assoc-and (under (ε) (CX12 • Z1) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CX12 • Z1 ≈ K12 • CX21 • K12 • Z1
step1 = by-assoc-and (under (K12) (Z1) (sym (drel30.proved))) Eq.refl Eq.refl

step2 : K12 • CX21 • K12 • Z1 ≈ K12 • CX21 • X1 • K12
step2 = by-assoc-and (under (K12 • CX21) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

step3 : K12 • CX21 • X1 • K12 ≈ K12 • X1 • CX21 • K12
step3 = by-assoc-and (under (K12) (K12) (sym (drel79.proved))) Eq.refl Eq.refl

step4 : K12 • X1 • CX21 • K12 ≈ Z1 • K12 • CX21 • K12
step4 = by-assoc-and (under (ε) (CX21 • K12) (drel65.proved)) Eq.refl Eq.refl

step5 : Z1 • K12 • CX21 • K12 ≈ Z1 • CX12 • K12 • K12
step5 = by-assoc-and (under (Z1) (K12) (drel46.proved)) Eq.refl Eq.refl

step6 : Z1 • CX12 • K12 • K12 ≈ Z1 • CX12
step6 = by-assoc-and (under (Z1 • CX12) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CX12 • Z1 ≈ Z1 • CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
