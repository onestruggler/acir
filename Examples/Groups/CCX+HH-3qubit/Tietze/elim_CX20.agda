{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX20 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX20 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r005 ; r024 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel131 as drel131
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1

step0 : CX20 • CX20 ≈ X1 • CCX12 • X1 • CCX12 • CX20
step0 = by-assoc-and (under (ε) (CX20) (axiom r005)) Eq.refl Eq.refl

step1 : X1 • CCX12 • X1 • CCX12 • CX20 ≈ X1 • CCX12 • X1 • CCX12 • CX20 • X1 • X1
step1 = by-assoc-and (under (X1 • CCX12 • X1 • CCX12 • CX20) (ε) (sym (elim_X1.proved))) Eq.refl Eq.refl

step2 : X1 • CCX12 • X1 • CCX12 • CX20 • X1 • X1 ≈ X1 • CCX12 • X1 • X1 • CCX12 • X1
step2 = by-assoc-and (under (X1 • CCX12 • X1) (X1) (sym (drel131.proved))) Eq.refl Eq.refl

step3 : X1 • CCX12 • X1 • X1 • CCX12 • X1 ≈ X1 • CCX12 • CCX12 • X1
step3 = by-assoc-and (under (X1 • CCX12) (CCX12 • X1) (elim_X1.proved)) Eq.refl Eq.refl

step4 : X1 • CCX12 • CCX12 • X1 ≈ X1 • X1
step4 = by-assoc-and (under (X1) (X1) (axiom r024)) Eq.refl Eq.refl

step5 : X1 • X1 ≈ ε
step5 = by-assoc-and (under (ε) (ε) (elim_X1.proved)) Eq.refl Eq.refl

proved : CX20 • CX20 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
