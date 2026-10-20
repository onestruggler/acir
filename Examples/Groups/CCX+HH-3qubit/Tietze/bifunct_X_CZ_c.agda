{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CZ_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; K12 ; X2 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r001 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_e as bifunct_Z_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.drel66 as drel66

step0 : X2 • CZ01 ≈ X2 • K12 • CX01 • K12
step0 = by-assoc-and (under (X2) (ε) (axiom r001)) Eq.refl Eq.refl

step1 : X2 • K12 • CX01 • K12 ≈ K12 • Z2 • CX01 • K12
step1 = by-assoc-and (under (ε) (CX01 • K12) (drel64.proved)) Eq.refl Eq.refl

step2 : K12 • Z2 • CX01 • K12 ≈ K12 • CX01 • Z2 • K12
step2 = by-assoc-and (under (K12) (K12) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

step3 : K12 • CX01 • Z2 • K12 ≈ K12 • CX01 • K12 • X2
step3 = by-assoc-and (under (K12 • CX01) (ε) (sym (drel66.proved))) Eq.refl Eq.refl

step4 : K12 • CX01 • K12 • X2 ≈ CZ01 • X2
step4 = by-assoc-and (under (ε) (X2) (sym (axiom r001))) Eq.refl Eq.refl

proved : X2 • CZ01 ≈ CZ01 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
