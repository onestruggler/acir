{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel54 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; K01 ; K12 ; X2 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; r025 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_b as bifunct_Z_K_b
import Examples.Groups.CCX+HH-3qubit.Tietze.drel26 as drel26
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel63 as drel63
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64

step0 : Z2 • CCX12 ≈ K01 • K01 • Z2 • CCX12
step0 = by-assoc-and (under (ε) (Z2 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z2 • CCX12 ≈ K01 • Z2 • K01 • CCX12
step1 = by-assoc-and (under (K01) (CCX12) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

step2 : K01 • Z2 • K01 • CCX12 ≈ K01 • Z2 • CCX02 • K01
step2 = by-assoc-and (under (K01 • Z2) (ε) (drel63.proved)) Eq.refl Eq.refl

step3 : K01 • Z2 • CCX02 • K01 ≈ K01 • K12 • K12 • Z2 • CCX02 • K01
step3 = by-assoc-and (under (K01) (Z2 • CCX02 • K01) (sym (axiom r023))) Eq.refl Eq.refl

step4 : K01 • K12 • K12 • Z2 • CCX02 • K01 ≈ K01 • K12 • X2 • K12 • CCX02 • K01
step4 = by-assoc-and (under (K01 • K12) (CCX02 • K01) (sym (drel64.proved))) Eq.refl Eq.refl

step5 : K01 • K12 • X2 • K12 • CCX02 • K01 ≈ K01 • K12 • X2 • CCX01 • K12 • K01
step5 = by-assoc-and (under (K01 • K12 • X2) (K01) (sym (drel29.proved))) Eq.refl Eq.refl

step6 : K01 • K12 • X2 • CCX01 • K12 • K01 ≈ K01 • K12 • CCX01 • X2 • K12 • K01
step6 = by-assoc-and (under (K01 • K12) (K12 • K01) (drel26.proved)) Eq.refl Eq.refl

step7 : K01 • K12 • CCX01 • X2 • K12 • K01 ≈ K01 • K12 • CCX01 • K12 • Z2 • K01
step7 = by-assoc-and (under (K01 • K12 • CCX01) (K01) (drel64.proved)) Eq.refl Eq.refl

step8 : K01 • K12 • CCX01 • K12 • Z2 • K01 ≈ K01 • K12 • K12 • CCX02 • Z2 • K01
step8 = by-assoc-and (under (K01 • K12) (Z2 • K01) (drel29.proved)) Eq.refl Eq.refl

step9 : K01 • K12 • K12 • CCX02 • Z2 • K01 ≈ K01 • CCX02 • Z2 • K01
step9 = by-assoc-and (under (K01) (CCX02 • Z2 • K01) (axiom r023)) Eq.refl Eq.refl

step10 : K01 • CCX02 • Z2 • K01 ≈ K01 • CCX02 • K01 • Z2
step10 = by-assoc-and (under (K01 • CCX02) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

step11 : K01 • CCX02 • K01 • Z2 ≈ K01 • K01 • CCX12 • Z2
step11 = by-assoc-and (under (K01) (Z2) (sym (drel63.proved))) Eq.refl Eq.refl

step12 : K01 • K01 • CCX12 • Z2 ≈ CCX12 • Z2
step12 = by-assoc-and (under (ε) (CCX12 • Z2) (axiom r025)) Eq.refl Eq.refl

proved : Z2 • CCX12 ≈ CCX12 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))
