{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel70 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel69 as drel69
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as elim_X2

step0 : CX12 • X1 ≈ CX12 • X1 • CX12 • CX12
step0 = by-assoc-and (under (CX12 • X1) (ε) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step1 : CX12 • X1 • CX12 • CX12 ≈ CX12 • X1 • CX12 • X2 • X2 • CX12
step1 = by-assoc-and (under (CX12 • X1 • CX12) (CX12) (sym (elim_X2.proved))) Eq.refl Eq.refl

step2 : CX12 • X1 • CX12 • X2 • X2 • CX12 ≈ CX12 • X1 • CX12 • X2 • X1 • X1 • X2 • CX12
step2 = by-assoc-and (under (CX12 • X1 • CX12 • X2) (X2 • CX12) (sym (elim_X1.proved))) Eq.refl Eq.refl

step3 : CX12 • X1 • CX12 • X2 • X1 • X1 • X2 • CX12 ≈ CX12 • X1 • X1 • CX12 • X1 • X2 • CX12
step3 = by-assoc-and (under (CX12 • X1) (X1 • X2 • CX12) (sym (drel69.proved))) Eq.refl Eq.refl

step4 : CX12 • X1 • X1 • CX12 • X1 • X2 • CX12 ≈ CX12 • CX12 • X1 • X2 • CX12
step4 = by-assoc-and (under (CX12) (CX12 • X1 • X2 • CX12) (elim_X1.proved)) Eq.refl Eq.refl

step5 : CX12 • CX12 • X1 • X2 • CX12 ≈ X1 • X2 • CX12
step5 = by-assoc-and (under (ε) (X1 • X2 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

proved : CX12 • X1 ≈ X1 • X2 • CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
