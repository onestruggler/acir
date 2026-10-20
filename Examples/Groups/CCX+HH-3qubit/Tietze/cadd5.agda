{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd5 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r007 ; r017 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd4 as cadd4

step0 : CX12 • CCX02 • CX12 ≈ CX12 • CCX02 • K12 • CX21 • K12
step0 = by-assoc-and (under (CX12 • CCX02) (ε) (axiom r007)) Eq.refl Eq.refl

step1 : CX12 • CCX02 • K12 • CX21 • K12 ≈ K12 • CX21 • K12 • CCX02 • K12 • CX21 • K12
step1 = by-assoc-and (under (ε) (CCX02 • K12 • CX21 • K12) (axiom r007)) Eq.refl Eq.refl

step2 : K12 • CX21 • K12 • CCX02 • K12 • CX21 • K12 ≈ K12 • CX21 • CCX01 • CX21 • K12
step2 = by-assoc-and (under (K12 • CX21) (CX21 • K12) (sym (axiom r017))) Eq.refl Eq.refl

step3 : K12 • CX21 • CCX01 • CX21 • K12 ≈ K12 • CCX02 • CCX01 • CCX02 • K12
step3 = by-assoc-and (under (K12) (K12) (cadd4.proved)) Eq.refl Eq.refl

step4 : K12 • CCX02 • CCX01 • CCX02 • K12 ≈ K12 • CCX02 • K12 • CCX02 • K12 • CCX02 • K12
step4 = by-assoc-and (under (K12 • CCX02) (CCX02 • K12) (axiom r017)) Eq.refl Eq.refl

step5 : K12 • CCX02 • K12 • CCX02 • K12 • CCX02 • K12 ≈ K12 • CCX02 • K12 • CCX02 • CCX01
step5 = by-assoc-and (under (K12 • CCX02 • K12 • CCX02) (ε) (sym (axiom r017))) Eq.refl Eq.refl

step6 : K12 • CCX02 • K12 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01
step6 = by-assoc-and (under (ε) (CCX02 • CCX01) (sym (axiom r017))) Eq.refl Eq.refl

proved : CX12 • CCX02 • CX12 ≈ CCX01 • CCX02 • CCX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
