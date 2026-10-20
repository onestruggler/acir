{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd2 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r022 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e as bifunct_X_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.drel141 as drel141
import Examples.Groups.CCX+HH-3qubit.Tietze.drel96 as drel96
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1

step0 : CX01 • CCX01 • CX01 ≈ CCX01 • CX02 • CX01 • CX01
step0 = by-assoc-and (under (ε) (CX01) (drel141.proved)) Eq.refl Eq.refl

step1 : CCX01 • CX02 • CX01 • CX01 ≈ CCX01 • CX02
step1 = by-assoc-and (under (CCX01 • CX02) (ε) (axiom r022)) Eq.refl Eq.refl

step2 : CCX01 • CX02 ≈ X1 • X1 • CCX01 • CX02
step2 = by-assoc-and (under (ε) (CCX01 • CX02) (sym (elim_X1.proved))) Eq.refl Eq.refl

step3 : X1 • X1 • CCX01 • CX02 ≈ X1 • CCX01 • CX02 • X1 • CX02
step3 = by-assoc-and (under (X1) (CX02) (drel96.proved)) Eq.refl Eq.refl

step4 : X1 • CCX01 • CX02 • X1 • CX02 ≈ X1 • CCX01 • X1 • CX02 • CX02
step4 = by-assoc-and (under (X1 • CCX01) (CX02) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

step5 : X1 • CCX01 • X1 • CX02 • CX02 ≈ X1 • CCX01 • X1
step5 = by-assoc-and (under (X1 • CCX01 • X1) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

proved : CX01 • CCX01 • CX01 ≈ X1 • CCX01 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
