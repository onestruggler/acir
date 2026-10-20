{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_f where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K01 ; X0 ; X2 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; r041 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_K_b as bifunct_X_K_b
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_b as bifunct_X_b

step0 : X2 • Z0 ≈ X2 • K01 • K01 • Z0
step0 = by-assoc-and (under (X2) (Z0) (sym (axiom r025))) Eq.refl Eq.refl

step1 : X2 • K01 • K01 • Z0 ≈ X2 • K01 • X0 • K01
step1 = by-assoc-and (under (X2 • K01) (ε) (axiom r041)) Eq.refl Eq.refl

step2 : X2 • K01 • X0 • K01 ≈ K01 • X2 • X0 • K01
step2 = by-assoc-and (under (ε) (X0 • K01) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

step3 : K01 • X2 • X0 • K01 ≈ K01 • X0 • X2 • K01
step3 = by-assoc-and (under (K01) (K01) (sym (bifunct_X_b.proved))) Eq.refl Eq.refl

step4 : K01 • X0 • X2 • K01 ≈ K01 • X0 • K01 • X2
step4 = by-assoc-and (under (K01 • X0) (ε) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

step5 : K01 • X0 • K01 • X2 ≈ K01 • K01 • Z0 • X2
step5 = by-assoc-and (under (K01) (X2) (sym (axiom r041))) Eq.refl Eq.refl

step6 : K01 • K01 • Z0 • X2 ≈ Z0 • X2
step6 = by-assoc-and (under (ε) (Z0 • X2) (axiom r025)) Eq.refl Eq.refl

proved : X2 • Z0 ≈ Z0 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
