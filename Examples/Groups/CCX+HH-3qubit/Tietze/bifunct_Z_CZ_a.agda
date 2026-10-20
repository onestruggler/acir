{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CZ_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CZ02 ; K12 ; X1 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e as bifunct_X_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel48 as drel48
import Examples.Groups.CCX+HH-3qubit.Tietze.drel65 as drel65

step0 : CZ02 • Z1 ≈ K12 • K12 • CZ02 • Z1
step0 = by-assoc-and (under (ε) (CZ02 • Z1) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ02 • Z1 ≈ K12 • CX02 • K12 • Z1
step1 = by-assoc-and (under (K12) (Z1) (drel47.proved)) Eq.refl Eq.refl

step2 : K12 • CX02 • K12 • Z1 ≈ K12 • CX02 • X1 • K12
step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

step3 : K12 • CX02 • X1 • K12 ≈ K12 • X1 • CX02 • K12
step3 = by-assoc-and (under (K12) (K12) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

step4 : K12 • X1 • CX02 • K12 ≈ Z1 • K12 • CX02 • K12
step4 = by-assoc-and (under (ε) (CX02 • K12) (drel65.proved)) Eq.refl Eq.refl

step5 : Z1 • K12 • CX02 • K12 ≈ Z1 • CZ02 • K12 • K12
step5 = by-assoc-and (under (Z1) (K12) (sym (drel48.proved))) Eq.refl Eq.refl

step6 : Z1 • CZ02 • K12 • K12 ≈ Z1 • CZ02
step6 = by-assoc-and (under (Z1 • CZ02) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CZ02 • Z1 ≈ Z1 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
