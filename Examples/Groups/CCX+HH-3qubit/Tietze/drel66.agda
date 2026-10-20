{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel66 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K12 ; X2 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as elim_X2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z2 as elim_Z2

step0 : K12 • X2 ≈ K12 • X2 • K12 • K12
step0 = by-assoc-and (under (K12 • X2) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • X2 • K12 • K12 ≈ K12 • X2 • K12 • Z2 • Z2 • K12
step1 = by-assoc-and (under (K12 • X2 • K12) (K12) (sym (elim_Z2.proved))) Eq.refl Eq.refl

step2 : K12 • X2 • K12 • Z2 • Z2 • K12 ≈ K12 • X2 • X2 • K12 • Z2 • K12
step2 = by-assoc-and (under (K12 • X2) (Z2 • K12) (sym (drel64.proved))) Eq.refl Eq.refl

step3 : K12 • X2 • X2 • K12 • Z2 • K12 ≈ K12 • K12 • Z2 • K12
step3 = by-assoc-and (under (K12) (K12 • Z2 • K12) (elim_X2.proved)) Eq.refl Eq.refl

step4 : K12 • K12 • Z2 • K12 ≈ Z2 • K12
step4 = by-assoc-and (under (ε) (Z2 • K12) (axiom r023)) Eq.refl Eq.refl

proved : K12 • X2 ≈ Z2 • K12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
