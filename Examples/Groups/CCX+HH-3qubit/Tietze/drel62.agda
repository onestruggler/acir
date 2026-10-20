{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel62 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CZ02 ; K12 ; X2 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel61 as drel61
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64

step0 : CZ02 • Z2 ≈ K12 • K12 • CZ02 • Z2
step0 = by-assoc-and (under (ε) (CZ02 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ02 • Z2 ≈ K12 • CX02 • K12 • Z2
step1 = by-assoc-and (under (K12) (Z2) (drel47.proved)) Eq.refl Eq.refl

step2 : K12 • CX02 • K12 • Z2 ≈ K12 • CX02 • X2 • K12
step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

step3 : K12 • CX02 • X2 • K12 ≈ K12 • X2 • CX02 • K12
step3 = by-assoc-and (under (K12) (K12) (drel61.proved)) Eq.refl Eq.refl

step4 : K12 • X2 • CX02 • K12 ≈ K12 • X2 • K12 • CZ02
step4 = by-assoc-and (under (K12 • X2) (ε) (sym (drel47.proved))) Eq.refl Eq.refl

step5 : K12 • X2 • K12 • CZ02 ≈ K12 • K12 • Z2 • CZ02
step5 = by-assoc-and (under (K12) (CZ02) (drel64.proved)) Eq.refl Eq.refl

step6 : K12 • K12 • Z2 • CZ02 ≈ Z2 • CZ02
step6 = by-assoc-and (under (ε) (Z2 • CZ02) (axiom r023)) Eq.refl Eq.refl

proved : CZ02 • Z2 ≈ Z2 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
