{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel59 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K01 ; X1 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel58 as drel58
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z1 as elim_Z1

step0 : X1 • K01 ≈ X1 • K01 • Z1 • Z1
step0 = by-assoc-and (under (X1 • K01) (ε) (sym (elim_Z1.proved))) Eq.refl Eq.refl

step1 : X1 • K01 • Z1 • Z1 ≈ X1 • K01 • Z1 • K01 • K01 • Z1
step1 = by-assoc-and (under (X1 • K01 • Z1) (Z1) (sym (axiom r025))) Eq.refl Eq.refl

step2 : X1 • K01 • Z1 • K01 • K01 • Z1 ≈ X1 • K01 • K01 • X1 • K01 • Z1
step2 = by-assoc-and (under (X1 • K01) (K01 • Z1) (drel58.proved)) Eq.refl Eq.refl

step3 : X1 • K01 • K01 • X1 • K01 • Z1 ≈ X1 • X1 • K01 • Z1
step3 = by-assoc-and (under (X1) (X1 • K01 • Z1) (axiom r025)) Eq.refl Eq.refl

step4 : X1 • X1 • K01 • Z1 ≈ K01 • Z1
step4 = by-assoc-and (under (ε) (K01 • Z1) (elim_X1.proved)) Eq.refl Eq.refl

proved : X1 • K01 ≈ K01 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
