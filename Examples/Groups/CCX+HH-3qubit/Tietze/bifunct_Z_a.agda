{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K01 ; X0 ; X1 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; r041 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.drel59 as drel59

step0 : Z0 • Z1 ≈ K01 • K01 • Z0 • Z1
step0 = by-assoc-and (under (ε) (Z0 • Z1) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z0 • Z1 ≈ K01 • X0 • K01 • Z1
step1 = by-assoc-and (under (K01) (Z1) (axiom r041)) Eq.refl Eq.refl

step2 : K01 • X0 • K01 • Z1 ≈ K01 • X0 • X1 • K01
step2 = by-assoc-and (under (K01 • X0) (ε) (sym (drel59.proved))) Eq.refl Eq.refl

step3 : K01 • X0 • X1 • K01 ≈ K01 • X1 • X0 • K01
step3 = by-assoc-and (under (K01) (K01) (X0X1.proved)) Eq.refl Eq.refl

step4 : K01 • X1 • X0 • K01 ≈ K01 • X1 • K01 • Z0
step4 = by-assoc-and (under (K01 • X1) (ε) (sym (axiom r041))) Eq.refl Eq.refl

step5 : K01 • X1 • K01 • Z0 ≈ K01 • K01 • Z1 • Z0
step5 = by-assoc-and (under (K01) (Z0) (drel59.proved)) Eq.refl Eq.refl

step6 : K01 • K01 • Z1 • Z0 ≈ Z1 • Z0
step6 = by-assoc-and (under (ε) (Z1 • Z0) (axiom r025)) Eq.refl Eq.refl

proved : Z0 • Z1 ≈ Z1 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
