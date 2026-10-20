{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel21 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX02 ; CZ02 ; K12 ; X1 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel96 as drel96

step0 : Z1 • CCX02 ≈ K12 • K12 • Z1 • CCX02
step0 = by-assoc-and (under (ε) (Z1 • CCX02) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • Z1 • CCX02 ≈ K12 • X1 • K12 • CCX02
step1 = by-assoc-and (under (K12) (CCX02) (sym (drel137.proved))) Eq.refl Eq.refl

step2 : K12 • X1 • K12 • CCX02 ≈ K12 • X1 • CCX01 • K12
step2 = by-assoc-and (under (K12 • X1) (ε) (sym (drel29.proved))) Eq.refl Eq.refl

step3 : K12 • X1 • CCX01 • K12 ≈ K12 • CCX01 • CX02 • X1 • K12
step3 = by-assoc-and (under (K12) (K12) (drel96.proved)) Eq.refl Eq.refl

step4 : K12 • CCX01 • CX02 • X1 • K12 ≈ K12 • CCX01 • CX02 • K12 • Z1
step4 = by-assoc-and (under (K12 • CCX01 • CX02) (ε) (drel137.proved)) Eq.refl Eq.refl

step5 : K12 • CCX01 • CX02 • K12 • Z1 ≈ K12 • CCX01 • K12 • CZ02 • Z1
step5 = by-assoc-and (under (K12 • CCX01) (Z1) (sym (drel47.proved))) Eq.refl Eq.refl

step6 : K12 • CCX01 • K12 • CZ02 • Z1 ≈ K12 • K12 • CCX02 • CZ02 • Z1
step6 = by-assoc-and (under (K12) (CZ02 • Z1) (drel29.proved)) Eq.refl Eq.refl

step7 : K12 • K12 • CCX02 • CZ02 • Z1 ≈ CCX02 • CZ02 • Z1
step7 = by-assoc-and (under (ε) (CCX02 • CZ02 • Z1) (axiom r023)) Eq.refl Eq.refl

proved : Z1 • CCX02 ≈ CCX02 • CZ02 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
