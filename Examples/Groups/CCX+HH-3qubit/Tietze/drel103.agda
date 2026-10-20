{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel103 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r022 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel141 as drel141
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as elim_CCX2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02

step0 : CCX01 • CX01 ≈ CCX01 • CX01 • CCX01 • CCX01
step0 = by-assoc-and (under (CCX01 • CX01) (ε) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

step1 : CCX01 • CX01 • CCX01 • CCX01 ≈ CCX01 • CX01 • CCX01 • CX02 • CX02 • CCX01
step1 = by-assoc-and (under (CCX01 • CX01 • CCX01) (CCX01) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step2 : CCX01 • CX01 • CCX01 • CX02 • CX02 • CCX01 ≈ CCX01 • CX01 • CCX01 • CX02 • CX01 • CX01 • CX02 • CCX01
step2 = by-assoc-and (under (CCX01 • CX01 • CCX01 • CX02) (CX02 • CCX01) (sym (axiom r022))) Eq.refl Eq.refl

step3 : CCX01 • CX01 • CCX01 • CX02 • CX01 • CX01 • CX02 • CCX01 ≈ CCX01 • CX01 • CX01 • CCX01 • CX01 • CX02 • CCX01
step3 = by-assoc-and (under (CCX01 • CX01) (CX01 • CX02 • CCX01) (sym (drel141.proved))) Eq.refl Eq.refl

step4 : CCX01 • CX01 • CX01 • CCX01 • CX01 • CX02 • CCX01 ≈ CCX01 • CCX01 • CX01 • CX02 • CCX01
step4 = by-assoc-and (under (CCX01) (CCX01 • CX01 • CX02 • CCX01) (axiom r022)) Eq.refl Eq.refl

step5 : CCX01 • CCX01 • CX01 • CX02 • CCX01 ≈ CX01 • CX02 • CCX01
step5 = by-assoc-and (under (ε) (CX01 • CX02 • CCX01) (elim_CCX2.proved)) Eq.refl Eq.refl

proved : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
