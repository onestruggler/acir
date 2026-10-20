{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K12 ; X0 ; X1 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; r027 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137

step0 : X0 • Z1 ≈ X0 • K12 • K12 • Z1
step0 = by-assoc-and (under (X0) (Z1) (sym (axiom r023))) Eq.refl Eq.refl

step1 : X0 • K12 • K12 • Z1 ≈ K12 • X0 • K12 • Z1
step1 = by-assoc-and (under (ε) (K12 • Z1) (axiom r027)) Eq.refl Eq.refl

step2 : K12 • X0 • K12 • Z1 ≈ K12 • X0 • X1 • K12
step2 = by-assoc-and (under (K12 • X0) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

step3 : K12 • X0 • X1 • K12 ≈ K12 • X1 • X0 • K12
step3 = by-assoc-and (under (K12) (K12) (X0X1.proved)) Eq.refl Eq.refl

step4 : K12 • X1 • X0 • K12 ≈ K12 • X1 • K12 • X0
step4 = by-assoc-and (under (K12 • X1) (ε) (axiom r027)) Eq.refl Eq.refl

step5 : K12 • X1 • K12 • X0 ≈ K12 • K12 • Z1 • X0
step5 = by-assoc-and (under (K12) (X0) (drel137.proved)) Eq.refl Eq.refl

step6 : K12 • K12 • Z1 • X0 ≈ Z1 • X0
step6 = by-assoc-and (under (ε) (Z1 • X0) (axiom r023)) Eq.refl Eq.refl

proved : X0 • Z1 ≈ Z1 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
