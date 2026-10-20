{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel119 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ01 ; X1 ; Z0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel145 as drel145
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 as elim_Z0

step0 : X1 • Z0 • CZ01 ≈ X1 • Z0 • CZ01 • X1 • X1
step0 = by-assoc-and (under (X1 • Z0 • CZ01) (ε) (sym (elim_X1.proved))) Eq.refl Eq.refl

step1 : X1 • Z0 • CZ01 • X1 • X1 ≈ X1 • Z0 • CZ01 • X1 • CZ01 • CZ01 • X1
step1 = by-assoc-and (under (X1 • Z0 • CZ01 • X1) (X1) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : X1 • Z0 • CZ01 • X1 • CZ01 • CZ01 • X1 ≈ X1 • Z0 • CZ01 • CZ01 • Z0 • X1 • CZ01 • X1
step2 = by-assoc-and (under (X1 • Z0 • CZ01) (CZ01 • X1) (drel145.proved)) Eq.refl Eq.refl

step3 : X1 • Z0 • CZ01 • CZ01 • Z0 • X1 • CZ01 • X1 ≈ X1 • Z0 • Z0 • X1 • CZ01 • X1
step3 = by-assoc-and (under (X1 • Z0) (Z0 • X1 • CZ01 • X1) (elim_CZ01.proved)) Eq.refl Eq.refl

step4 : X1 • Z0 • Z0 • X1 • CZ01 • X1 ≈ X1 • X1 • CZ01 • X1
step4 = by-assoc-and (under (X1) (X1 • CZ01 • X1) (elim_Z0.proved)) Eq.refl Eq.refl

step5 : X1 • X1 • CZ01 • X1 ≈ CZ01 • X1
step5 = by-assoc-and (under (ε) (CZ01 • X1) (elim_X1.proved)) Eq.refl Eq.refl

proved : X1 • Z0 • CZ01 ≈ CZ01 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
