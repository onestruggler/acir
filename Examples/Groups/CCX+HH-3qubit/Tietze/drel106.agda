{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel106 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; X0 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r021 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel126 as drel126
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as elim_X2

step0 : X0 • X2 • CX02 ≈ CX02 • CX02 • X0 • X2 • CX02
step0 = by-assoc-and (under (ε) (X0 • X2 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step1 : CX02 • CX02 • X0 • X2 • CX02 ≈ CX02 • X0 • X0 • CX02 • X0 • X2 • CX02
step1 = by-assoc-and (under (CX02) (CX02 • X0 • X2 • CX02) (sym (axiom r021))) Eq.refl Eq.refl

step2 : CX02 • X0 • X0 • CX02 • X0 • X2 • CX02 ≈ CX02 • X0 • CX02 • X2 • X0 • X0 • X2 • CX02
step2 = by-assoc-and (under (CX02 • X0) (X0 • X2 • CX02) (drel126.proved)) Eq.refl Eq.refl

step3 : CX02 • X0 • CX02 • X2 • X0 • X0 • X2 • CX02 ≈ CX02 • X0 • CX02 • X2 • X2 • CX02
step3 = by-assoc-and (under (CX02 • X0 • CX02 • X2) (X2 • CX02) (axiom r021)) Eq.refl Eq.refl

step4 : CX02 • X0 • CX02 • X2 • X2 • CX02 ≈ CX02 • X0 • CX02 • CX02
step4 = by-assoc-and (under (CX02 • X0 • CX02) (CX02) (elim_X2.proved)) Eq.refl Eq.refl

step5 : CX02 • X0 • CX02 • CX02 ≈ CX02 • X0
step5 = by-assoc-and (under (CX02 • X0) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

proved : X0 • X2 • CX02 ≈ CX02 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
