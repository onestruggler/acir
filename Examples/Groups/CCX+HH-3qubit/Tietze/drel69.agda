{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel69 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; SWAP02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_c as bifunct_X_SWAP_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel67 as drel67
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

step0 : X1 • CX12 ≈ X1 • SWAP02 • CX10 • SWAP02
step0 = by-assoc-and (under (X1) (ε) (symmetry_CX_f.proved)) Eq.refl Eq.refl

step1 : X1 • SWAP02 • CX10 • SWAP02 ≈ SWAP02 • X1 • CX10 • SWAP02
step1 = by-assoc-and (under (ε) (CX10 • SWAP02) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

step2 : SWAP02 • X1 • CX10 • SWAP02 ≈ SWAP02 • CX10 • X0 • X1 • SWAP02
step2 = by-assoc-and (under (SWAP02) (SWAP02) (drel67.proved)) Eq.refl Eq.refl

step3 : SWAP02 • CX10 • X0 • X1 • SWAP02 ≈ SWAP02 • CX10 • X0 • SWAP02 • X1
step3 = by-assoc-and (under (SWAP02 • CX10 • X0) (ε) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX10 • X0 • SWAP02 • X1 ≈ SWAP02 • CX10 • SWAP02 • SWAP02 • X0 • SWAP02 • X1
step4 = by-assoc-and (under (SWAP02 • CX10) (X0 • SWAP02 • X1) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CX10 • SWAP02 • SWAP02 • X0 • SWAP02 • X1 ≈ SWAP02 • CX10 • SWAP02 • X2 • X1
step5 = by-assoc-and (under (SWAP02 • CX10 • SWAP02) (X1) (sym (axiom r015))) Eq.refl Eq.refl

step6 : SWAP02 • CX10 • SWAP02 • X2 • X1 ≈ CX12 • X2 • X1
step6 = by-assoc-and (under (ε) (X2 • X1) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

proved : X1 • CX12 ≈ CX12 • X2 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
