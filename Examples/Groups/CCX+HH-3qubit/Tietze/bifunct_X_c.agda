{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r002 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_d as bifunct_X_CX_d
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_b as bifunct_X_b

step0 : X1 • X2 ≈ CX01 • X0 • CX01 • X0 • X2
step0 = by-assoc-and (under (ε) (X2) (axiom r002)) Eq.refl Eq.refl

step1 : CX01 • X0 • CX01 • X0 • X2 ≈ CX01 • X0 • CX01 • X2 • X0
step1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (bifunct_X_b.proved)) Eq.refl Eq.refl

step2 : CX01 • X0 • CX01 • X2 • X0 ≈ CX01 • X0 • X2 • CX01 • X0
step2 = by-assoc-and (under (CX01 • X0) (X0) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

step3 : CX01 • X0 • X2 • CX01 • X0 ≈ CX01 • X2 • X0 • CX01 • X0
step3 = by-assoc-and (under (CX01) (CX01 • X0) (bifunct_X_b.proved)) Eq.refl Eq.refl

step4 : CX01 • X2 • X0 • CX01 • X0 ≈ X2 • CX01 • X0 • CX01 • X0
step4 = by-assoc-and (under (ε) (X0 • CX01 • X0) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

step5 : X2 • CX01 • X0 • CX01 • X0 ≈ X2 • X1
step5 = by-assoc-and (under (X2) (ε) (sym (axiom r002))) Eq.refl Eq.refl

proved : X1 • X2 ≈ X2 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
