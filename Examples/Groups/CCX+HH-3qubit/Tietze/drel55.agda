{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel55 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel30 as drel30
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.drel86 as drel86
import Examples.Groups.CCX+HH-3qubit.Tietze.drel93 as drel93

step0 : CCX01 • CX12 ≈ K12 • K12 • CCX01 • CX12
step0 = by-assoc-and (under (ε) (CCX01 • CX12) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CCX01 • CX12 ≈ K12 • CCX02 • K12 • CX12
step1 = by-assoc-and (under (K12) (CX12) (drel86.proved)) Eq.refl Eq.refl

step2 : K12 • CCX02 • K12 • CX12 ≈ K12 • CCX02 • CX21 • K12
step2 = by-assoc-and (under (K12 • CCX02) (ε) (sym (drel30.proved))) Eq.refl Eq.refl

step3 : K12 • CCX02 • CX21 • K12 ≈ K12 • CX21 • CCX02 • K12
step3 = by-assoc-and (under (K12) (K12) (drel93.proved)) Eq.refl Eq.refl

step4 : K12 • CX21 • CCX02 • K12 ≈ CX12 • K12 • CCX02 • K12
step4 = by-assoc-and (under (ε) (CCX02 • K12) (drel46.proved)) Eq.refl Eq.refl

step5 : CX12 • K12 • CCX02 • K12 ≈ CX12 • CCX01 • K12 • K12
step5 = by-assoc-and (under (CX12) (K12) (sym (drel29.proved))) Eq.refl Eq.refl

step6 : CX12 • CCX01 • K12 • K12 ≈ CX12 • CCX01
step6 = by-assoc-and (under (CX12 • CCX01) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CCX01 • CX12 ≈ CX12 • CCX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
