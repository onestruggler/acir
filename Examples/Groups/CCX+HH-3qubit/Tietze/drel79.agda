{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel79 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX21 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r002 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b as bifunct_X_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.drel41 as drel41

step0 : X1 • CX21 ≈ CX01 • X0 • CX01 • X0 • CX21
step0 = by-assoc-and (under (ε) (CX21) (axiom r002)) Eq.refl Eq.refl

step1 : CX01 • X0 • CX01 • X0 • CX21 ≈ CX01 • X0 • CX01 • CX21 • X0
step1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

step2 : CX01 • X0 • CX01 • CX21 • X0 ≈ CX01 • X0 • CX21 • CX01 • X0
step2 = by-assoc-and (under (CX01 • X0) (X0) (drel41.proved)) Eq.refl Eq.refl

step3 : CX01 • X0 • CX21 • CX01 • X0 ≈ CX01 • CX21 • X0 • CX01 • X0
step3 = by-assoc-and (under (CX01) (CX01 • X0) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

step4 : CX01 • CX21 • X0 • CX01 • X0 ≈ CX21 • CX01 • X0 • CX01 • X0
step4 = by-assoc-and (under (ε) (X0 • CX01 • X0) (drel41.proved)) Eq.refl Eq.refl

step5 : CX21 • CX01 • X0 • CX01 • X0 ≈ CX21 • X1
step5 = by-assoc-and (under (CX21) (ε) (sym (axiom r002))) Eq.refl Eq.refl

proved : X1 • CX21 ≈ CX21 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
