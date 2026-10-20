{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_j where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h as symmetry_CX_h
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01 as symmetry_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CX20 ≈ SWAP01 • CX21 • SWAP01
step0 = by-assoc-and (under (ε) (ε) (symmetry_CX_h.proved)) Eq.refl Eq.refl

step1 : SWAP01 • CX21 • SWAP01 ≈ SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01
step1 = by-assoc-and (under (SWAP01) (SWAP01) (symmetry_CX_g.proved)) Eq.refl Eq.refl

step2 : SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP02 • SWAP12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (symmetry_CX_f.proved)) Eq.refl Eq.refl

step3 : SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP02 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • SWAP01
step3 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP02 • SWAP12) (SWAP01) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step4 : SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP01 • SWAP02 • SWAP01
step4 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP02 • CX10) (SWAP02 • SWAP01) (sym (symmetry_SWAP01.proved))) Eq.refl Eq.refl

step5 : SWAP01 • SWAP12 • SWAP02 • CX10 • SWAP01 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • CX10 • SWAP01 • SWAP02 • SWAP01
step5 = by-assoc-and (under (SWAP01) (SWAP12 • SWAP02 • CX10 • SWAP01 • SWAP02 • SWAP01) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step6 : SWAP01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • CX10 • SWAP01 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP02 • SWAP01
step6 = by-assoc-and (under (SWAP01 • SWAP02) (CX10 • SWAP01 • SWAP02 • SWAP01) (sym (symmetry_SWAP01.proved))) Eq.refl Eq.refl

step7 : SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP01 • SWAP12 • SWAP01 • SWAP01
step7 = by-assoc-and (under (SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01) (SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step8 : SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP01 • SWAP12
step8 = by-assoc-and (under (SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP01 • SWAP12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step9 : SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP01 • SWAP01 • SWAP12 ≈ SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP12
step9 = by-assoc-and (under (SWAP01 • SWAP02 • SWAP01 • CX10) (SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step10 : SWAP01 • SWAP02 • SWAP01 • CX10 • SWAP12 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • SWAP01 • CX10 • SWAP12
step10 = by-assoc-and (under (SWAP01) (SWAP01 • CX10 • SWAP12) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step11 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • SWAP01 • CX10 • SWAP12 ≈ SWAP01 • SWAP01 • SWAP12 • CX10 • SWAP12
step11 = by-assoc-and (under (SWAP01 • SWAP01 • SWAP12) (CX10 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step12 : SWAP01 • SWAP01 • SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CX10 • SWAP12
step12 = by-assoc-and (under (ε) (SWAP12 • CX10 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CX20 ≈ SWAP12 • CX10 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))
