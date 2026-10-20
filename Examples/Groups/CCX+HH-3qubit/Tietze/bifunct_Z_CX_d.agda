{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_d where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_b as bifunct_Z_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_a as bifunct_Z_K_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46

step0 : Z0 • CX21 ≈ Z0 • K12 • K12 • CX21
step0 = by-assoc-and (under (Z0) (CX21) (sym (axiom r023))) Eq.refl Eq.refl

step1 : Z0 • K12 • K12 • CX21 ≈ Z0 • K12 • CX12 • K12
step1 = by-assoc-and (under (Z0 • K12) (ε) (drel46.proved)) Eq.refl Eq.refl

step2 : Z0 • K12 • CX12 • K12 ≈ K12 • Z0 • CX12 • K12
step2 = by-assoc-and (under (ε) (CX12 • K12) (bifunct_Z_K_a.proved)) Eq.refl Eq.refl

step3 : K12 • Z0 • CX12 • K12 ≈ K12 • CX12 • Z0 • K12
step3 = by-assoc-and (under (K12) (K12) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

step4 : K12 • CX12 • Z0 • K12 ≈ K12 • CX12 • K12 • Z0
step4 = by-assoc-and (under (K12 • CX12) (ε) (bifunct_Z_K_a.proved)) Eq.refl Eq.refl

step5 : K12 • CX12 • K12 • Z0 ≈ K12 • K12 • CX21 • Z0
step5 = by-assoc-and (under (K12) (Z0) (sym (drel46.proved))) Eq.refl Eq.refl

step6 : K12 • K12 • CX21 • Z0 ≈ CX21 • Z0
step6 = by-assoc-and (under (ε) (CX21 • Z0) (axiom r023)) Eq.refl Eq.refl

proved : Z0 • CX21 ≈ CX21 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
