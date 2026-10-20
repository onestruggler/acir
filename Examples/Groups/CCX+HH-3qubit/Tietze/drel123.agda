{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel123 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; X0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r021 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel156 as drel156
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z2 as elim_Z2

step0 : X0 • Z2 • CZ02 ≈ X0 • Z2 • CZ02 • X0 • X0
step0 = by-assoc-and (under (X0 • Z2 • CZ02) (ε) (sym (axiom r021))) Eq.refl Eq.refl

step1 : X0 • Z2 • CZ02 • X0 • X0 ≈ X0 • Z2 • CZ02 • X0 • CZ02 • CZ02 • X0
step1 = by-assoc-and (under (X0 • Z2 • CZ02 • X0) (X0) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step2 : X0 • Z2 • CZ02 • X0 • CZ02 • CZ02 • X0 ≈ X0 • Z2 • CZ02 • CZ02 • Z2 • X0 • CZ02 • X0
step2 = by-assoc-and (under (X0 • Z2 • CZ02) (CZ02 • X0) (drel156.proved)) Eq.refl Eq.refl

step3 : X0 • Z2 • CZ02 • CZ02 • Z2 • X0 • CZ02 • X0 ≈ X0 • Z2 • Z2 • X0 • CZ02 • X0
step3 = by-assoc-and (under (X0 • Z2) (Z2 • X0 • CZ02 • X0) (elim_CZ02.proved)) Eq.refl Eq.refl

step4 : X0 • Z2 • Z2 • X0 • CZ02 • X0 ≈ X0 • X0 • CZ02 • X0
step4 = by-assoc-and (under (X0) (X0 • CZ02 • X0) (elim_Z2.proved)) Eq.refl Eq.refl

step5 : X0 • X0 • CZ02 • X0 ≈ CZ02 • X0
step5 = by-assoc-and (under (ε) (CZ02 • X0) (axiom r021)) Eq.refl Eq.refl

proved : X0 • Z2 • CZ02 ≈ CZ02 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
