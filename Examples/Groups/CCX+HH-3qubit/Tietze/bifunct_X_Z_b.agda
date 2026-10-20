{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K01 ; X0 ; X1 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; r041 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_a as bifunct_X_Z_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel58 as drel58

step0 : X1 • Z0 ≈ K01 • K01 • X1 • Z0
step0 = by-assoc-and (under (ε) (X1 • Z0) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • X1 • Z0 ≈ K01 • Z1 • K01 • Z0
step1 = by-assoc-and (under (K01) (Z0) (sym (drel58.proved))) Eq.refl Eq.refl

step2 : K01 • Z1 • K01 • Z0 ≈ K01 • Z1 • X0 • K01
step2 = by-assoc-and (under (K01 • Z1) (ε) (axiom r041)) Eq.refl Eq.refl

step3 : K01 • Z1 • X0 • K01 ≈ K01 • X0 • Z1 • K01
step3 = by-assoc-and (under (K01) (K01) (sym (bifunct_X_Z_a.proved))) Eq.refl Eq.refl

step4 : K01 • X0 • Z1 • K01 ≈ K01 • X0 • K01 • X1
step4 = by-assoc-and (under (K01 • X0) (ε) (drel58.proved)) Eq.refl Eq.refl

step5 : K01 • X0 • K01 • X1 ≈ K01 • K01 • Z0 • X1
step5 = by-assoc-and (under (K01) (X1) (sym (axiom r041))) Eq.refl Eq.refl

step6 : K01 • K01 • Z0 • X1 ≈ Z0 • X1
step6 = by-assoc-and (under (ε) (Z0 • X1) (axiom r025)) Eq.refl Eq.refl

proved : X1 • Z0 ≈ Z0 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
