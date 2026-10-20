{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; X0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; r026 ; r027 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46

step0 : CX21 • X0 ≈ K12 • K12 • CX21 • X0
step0 = by-assoc-and (under (ε) (CX21 • X0) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CX21 • X0 ≈ K12 • CX12 • K12 • X0
step1 = by-assoc-and (under (K12) (X0) (drel46.proved)) Eq.refl Eq.refl

step2 : K12 • CX12 • K12 • X0 ≈ K12 • CX12 • X0 • K12
step2 = by-assoc-and (under (K12 • CX12) (ε) (sym (axiom r027))) Eq.refl Eq.refl

step3 : K12 • CX12 • X0 • K12 ≈ K12 • X0 • CX12 • K12
step3 = by-assoc-and (under (K12) (K12) (axiom r026)) Eq.refl Eq.refl

step4 : K12 • X0 • CX12 • K12 ≈ X0 • K12 • CX12 • K12
step4 = by-assoc-and (under (ε) (CX12 • K12) (sym (axiom r027))) Eq.refl Eq.refl

step5 : X0 • K12 • CX12 • K12 ≈ X0 • K12 • K12 • CX21
step5 = by-assoc-and (under (X0 • K12) (ε) (sym (drel46.proved))) Eq.refl Eq.refl

step6 : X0 • K12 • K12 • CX21 ≈ X0 • CX21
step6 = by-assoc-and (under (X0) (CX21) (axiom r023)) Eq.refl Eq.refl

proved : CX21 • X0 ≈ X0 • CX21
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
