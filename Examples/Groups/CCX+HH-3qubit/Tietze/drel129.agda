{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel129 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; K01 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r012 ; r025 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_K_b as bifunct_X_K_b
import Examples.Groups.CCX+HH-3qubit.Tietze.drel130 as drel130
import Examples.Groups.CCX+HH-3qubit.Tietze.drel63 as drel63

step0 : X2 • CCX02 ≈ X2 • CCX02 • K01 • K01
step0 = by-assoc-and (under (X2 • CCX02) (ε) (sym (axiom r025))) Eq.refl Eq.refl

step1 : X2 • CCX02 • K01 • K01 ≈ X2 • K01 • CCX12 • K01
step1 = by-assoc-and (under (X2) (K01) (sym (drel63.proved))) Eq.refl Eq.refl

step2 : X2 • K01 • CCX12 • K01 ≈ K01 • X2 • CCX12 • K01
step2 = by-assoc-and (under (ε) (CCX12 • K01) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

step3 : K01 • X2 • CCX12 • K01 ≈ K01 • CCX12 • CX10 • X2 • K01
step3 = by-assoc-and (under (K01) (K01) (drel130.proved)) Eq.refl Eq.refl

step4 : K01 • CCX12 • CX10 • X2 • K01 ≈ CCX02 • K01 • CX10 • X2 • K01
step4 = by-assoc-and (under (ε) (CX10 • X2 • K01) (drel63.proved)) Eq.refl Eq.refl

step5 : CCX02 • K01 • CX10 • X2 • K01 ≈ CCX02 • K01 • CX10 • K01 • X2
step5 = by-assoc-and (under (CCX02 • K01 • CX10) (ε) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

step6 : CCX02 • K01 • CX10 • K01 • X2 ≈ CCX02 • K01 • K01 • CX01 • K01 • K01 • X2
step6 = by-assoc-and (under (CCX02 • K01) (K01 • X2) (axiom r012)) Eq.refl Eq.refl

step7 : CCX02 • K01 • K01 • CX01 • K01 • K01 • X2 ≈ CCX02 • K01 • K01 • CX01 • X2
step7 = by-assoc-and (under (CCX02 • K01 • K01 • CX01) (X2) (axiom r025)) Eq.refl Eq.refl

step8 : CCX02 • K01 • K01 • CX01 • X2 ≈ CCX02 • CX01 • X2
step8 = by-assoc-and (under (CCX02) (CX01 • X2) (axiom r025)) Eq.refl Eq.refl

proved : X2 • CCX02 ≈ CCX02 • CX01 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
