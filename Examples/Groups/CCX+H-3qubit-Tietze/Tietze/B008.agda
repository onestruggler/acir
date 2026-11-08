{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B008 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r009 ; r014 ; r021 ; r023 ; r029 ; r030 ; r032 ; r042 ; r044 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module drel46 ; module elim_CX12 ; module elim_SWAP01 ; module elim_SWAP02 ; module symmetry_CX_e)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module drel137 ; module drel65)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module bifunct_Z_SWAP_a ; module drel30)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module elim_CCX2)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B006 using (module drel78)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B007 using (module drel79 ; module drel94)

module drel80 where

  step0 : CX12 • Z1 ≈ K12 • K12 • CX12 • Z1
  step0 = by-assoc-and (under (ε) (CX12 • Z1) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CX12 • Z1 ≈ K12 • CX21 • K12 • Z1
  step1 = by-assoc-and (under (K12) (Z1) (sym (drel30.proved))) Eq.refl Eq.refl

  step2 : K12 • CX21 • K12 • Z1 ≈ K12 • CX21 • X1 • K12
  step2 = by-assoc-and (under (K12 • CX21) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

  step3 : K12 • CX21 • X1 • K12 ≈ K12 • X1 • CX21 • K12
  step3 = by-assoc-and (under (K12) (K12) (sym (drel79.proved))) Eq.refl Eq.refl

  step4 : K12 • X1 • CX21 • K12 ≈ Z1 • K12 • CX21 • K12
  step4 = by-assoc-and (under (ε) (CX21 • K12) (drel65.proved)) Eq.refl Eq.refl

  step5 : Z1 • K12 • CX21 • K12 ≈ Z1 • CX12 • K12 • K12
  step5 = by-assoc-and (under (Z1) (K12) (drel46.proved)) Eq.refl Eq.refl

  step6 : Z1 • CX12 • K12 • K12 ≈ Z1 • CX12
  step6 = by-assoc-and (under (Z1 • CX12) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CX12 • Z1 ≈ Z1 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel81 where

  step0 : CX02 • Z0 ≈ SWAP12 • CX01 • SWAP12 • Z0
  step0 = by-assoc-and (under (ε) (Z0) (axiom r009)) Eq.refl Eq.refl

  step1 : SWAP12 • CX01 • SWAP12 • Z0 ≈ SWAP12 • CX01 • Z0 • SWAP12
  step1 = by-assoc-and (under (SWAP12 • CX01) (ε) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • Z0 • SWAP12 ≈ SWAP12 • Z0 • CX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (drel78.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • Z0 • CX01 • SWAP12 ≈ Z0 • SWAP12 • CX01 • SWAP12
  step3 = by-assoc-and (under (ε) (CX01 • SWAP12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

  step4 : Z0 • SWAP12 • CX01 • SWAP12 ≈ Z0 • CX02
  step4 = by-assoc-and (under (Z0) (ε) (sym (axiom r009))) Eq.refl Eq.refl

  proved : CX02 • Z0 ≈ Z0 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel91 where

  step0 : CCX01 • CX02 ≈ SWAP02 • CCX12 • SWAP02 • CX02
  step0 = by-assoc-and (under (ε) (CX02) (axiom r032)) Eq.refl Eq.refl

  step1 : SWAP02 • CCX12 • SWAP02 • CX02 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (SWAP02 • CCX12 • SWAP02 • CX02) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • CCX12) (SWAP02) (sym (axiom r029))) Eq.refl Eq.refl

  step3 : SWAP02 • CCX12 • CX20 • SWAP02 ≈ SWAP02 • CX20 • CCX12 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel94.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CX20 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX02 • SWAP02 • CCX12 • SWAP02
  step4 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (axiom r029)) Eq.refl Eq.refl

  step5 : SWAP02 • SWAP02 • CX02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX02 • CCX01
  step5 = by-assoc-and (under (SWAP02 • SWAP02 • CX02) (ε) (sym (axiom r032))) Eq.refl Eq.refl

  step6 : SWAP02 • SWAP02 • CX02 • CCX01 ≈ CX02 • CCX01
  step6 = by-assoc-and (under (ε) (CX02 • CCX01) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : CCX01 • CX02 ≈ CX02 • CCX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel95 where

  step0 : CX02 • CCX02 ≈ CX02 • SWAP01 • CCX12 • SWAP01
  step0 = by-assoc-and (under (CX02) (ε) (axiom r014)) Eq.refl Eq.refl

  step1 : CX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • CCX12 • SWAP01
  step1 = by-assoc-and (under (ε) (CX02 • SWAP01 • CCX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CX12 • CCX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step3 : SWAP01 • CX12 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • CX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r044)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX12 • CX10 • CX12 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • SWAP01 • CX02 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX12 • CX10) (SWAP01) (axiom r030)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX12 • CX10 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • SWAP01 • CX02
  step5 = by-assoc-and (under (SWAP01 • CCX12 • CX10 • SWAP01 • CX02) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CCX12 • CX10 • SWAP01 • CX02 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01 • CX02
  step6 = by-assoc-and (under (SWAP01 • CCX12) (CX10 • SWAP01 • CX02) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step7 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01 • CX02 ≈ SWAP01 • CCX12 • SWAP01 • CX01 • CX02
  step7 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01) (CX02) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  step8 : SWAP01 • CCX12 • SWAP01 • CX01 • CX02 ≈ CCX02 • CX01 • CX02
  step8 = by-assoc-and (under (ε) (CX01 • CX02) (sym (axiom r014))) Eq.refl Eq.refl

  proved : CX02 • CCX02 ≈ CCX02 • CX01 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel98 where

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
