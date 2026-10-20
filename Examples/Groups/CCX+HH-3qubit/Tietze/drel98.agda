{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel98 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r021 ; r042 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as elim_CCX2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12

step0 : X0 • CX12 • CCX01 ≈ X0 • CX12 • CCX01 • X0 • X0
step0 = by-assoc-and (under (X0 • CX12 • CCX01) (ε) (sym (axiom r021))) Eq.refl Eq.refl

step1 : X0 • CX12 • CCX01 • X0 • X0 ≈ X0 • CX12 • CCX01 • X0 • CCX01 • CCX01 • X0
step1 = by-assoc-and (under (X0 • CX12 • CCX01 • X0) (X0) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

step2 : X0 • CX12 • CCX01 • X0 • CCX01 • CCX01 • X0 ≈ X0 • CX12 • CCX01 • CCX01 • CX12 • X0 • CCX01 • X0
step2 = by-assoc-and (under (X0 • CX12 • CCX01) (CCX01 • X0) (axiom r042)) Eq.refl Eq.refl

step3 : X0 • CX12 • CCX01 • CCX01 • CX12 • X0 • CCX01 • X0 ≈ X0 • CX12 • CX12 • X0 • CCX01 • X0
step3 = by-assoc-and (under (X0 • CX12) (CX12 • X0 • CCX01 • X0) (elim_CCX2.proved)) Eq.refl Eq.refl

step4 : X0 • CX12 • CX12 • X0 • CCX01 • X0 ≈ X0 • X0 • CCX01 • X0
step4 = by-assoc-and (under (X0) (X0 • CCX01 • X0) (elim_CX12.proved)) Eq.refl Eq.refl

step5 : X0 • X0 • CCX01 • X0 ≈ CCX01 • X0
step5 = by-assoc-and (under (ε) (CCX01 • X0) (axiom r021)) Eq.refl Eq.refl

proved : X0 • CX12 • CCX01 ≈ CCX01 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
