{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B003 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r001 ; r008 ; r009 ; r010 ; r013 ; r014 ; r018 ; r019 ; r021 ; r022 ; r023 ; r025 ; r026 ; r029 ; r032 ; r033 ; r034 ; r041 ; r042 ; r044 ; r045 ; refl ; sym ; trans ; under ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_d ; module bifunct_X_CX_e ; module drel131 ; module drel154 ; module drel46 ; module elim_CX02 ; module elim_CX10 ; module elim_CX12 ; module elim_CX21 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module elim_X1 ; module symmetry_CX_f ; module symmetry_CX_g ; module symmetry_CX_i ; module symmetry_SWAP02)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module bifunct_Z_CX_b ; module bifunct_Z_K_b ; module drel64 ; module drel66 ; module elim_CZ02 ; module symmetry_CX_b ; module symmetry_CX_j ; module symmetry_SWAP01 ; module symmetry_SWAP01_alt)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_SWAP_c ; module bifunct_X_Z_e ; module bifunct_X_c ; module bifunct_Z_CX_d ; module bifunct_Z_CX_e ; module bifunct_Z_CX_f ; module drel137 ; module drel58 ; module drel65 ; module elim_Z1)

module drel30 where

  step0 : CX21 • K12 ≈ CX21 • K12 • CX12 • CX12
  step0 = by-assoc-and (under (CX21 • K12) (ε) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step1 : CX21 • K12 • CX12 • CX12 ≈ CX21 • K12 • CX12 • K12 • K12 • CX12
  step1 = by-assoc-and (under (CX21 • K12 • CX12) (CX12) (sym (axiom r023))) Eq.refl Eq.refl

  step2 : CX21 • K12 • CX12 • K12 • K12 • CX12 ≈ CX21 • K12 • K12 • CX21 • K12 • CX12
  step2 = by-assoc-and (under (CX21 • K12) (K12 • CX12) (sym (drel46.proved))) Eq.refl Eq.refl

  step3 : CX21 • K12 • K12 • CX21 • K12 • CX12 ≈ CX21 • CX21 • K12 • CX12
  step3 = by-assoc-and (under (CX21) (CX21 • K12 • CX12) (axiom r023)) Eq.refl Eq.refl

  step4 : CX21 • CX21 • K12 • CX12 ≈ K12 • CX12
  step4 = by-assoc-and (under (ε) (K12 • CX12) (elim_CX21.proved)) Eq.refl Eq.refl

  proved : CX21 • K12 ≈ K12 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module symmetry_K_a where

  step0 : K12 ≈ K12 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (K12) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : K12 • SWAP12 • SWAP12 ≈ K12 • CX12 • CX21 • CX12 • SWAP12
  step1 = by-assoc-and (under (K12) (SWAP12) (axiom r008)) Eq.refl Eq.refl

  step2 : K12 • CX12 • CX21 • CX12 • SWAP12 ≈ CX21 • K12 • CX21 • CX12 • SWAP12
  step2 = by-assoc-and (under (ε) (CX21 • CX12 • SWAP12) (sym (drel30.proved))) Eq.refl Eq.refl

  step3 : CX21 • K12 • CX21 • CX12 • SWAP12 ≈ CX21 • CX12 • K12 • CX12 • SWAP12
  step3 = by-assoc-and (under (CX21) (CX12 • SWAP12) (drel46.proved)) Eq.refl Eq.refl

  step4 : CX21 • CX12 • K12 • CX12 • SWAP12 ≈ CX21 • CX12 • CX21 • K12 • SWAP12
  step4 = by-assoc-and (under (CX21 • CX12) (SWAP12) (sym (drel30.proved))) Eq.refl Eq.refl

  step5 : CX21 • CX12 • CX21 • K12 • SWAP12 ≈ CX21 • CX21 • SWAP12 • K12 • SWAP12
  step5 = by-assoc-and (under (CX21) (K12 • SWAP12) (drel154.proved)) Eq.refl Eq.refl

  step6 : CX21 • CX21 • SWAP12 • K12 • SWAP12 ≈ SWAP12 • K12 • SWAP12
  step6 = by-assoc-and (under (ε) (SWAP12 • K12 • SWAP12) (elim_CX21.proved)) Eq.refl Eq.refl

  proved : K12 ≈ SWAP12 • K12 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel47 where

  step0 : K12 • CZ02 ≈ K12 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (K12) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : K12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • K12 • SWAP12 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (K12 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • K12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • K12 • CZ01 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (symmetry_K_a.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • K12 • CZ01 • SWAP12 ≈ SWAP12 • K12 • K12 • CX01 • K12 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • K12) (SWAP12) (axiom r001)) Eq.refl Eq.refl

  step4 : SWAP12 • K12 • K12 • CX01 • K12 • SWAP12 ≈ SWAP12 • CX01 • K12 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CX01 • K12 • SWAP12) (axiom r023)) Eq.refl Eq.refl

  step5 : SWAP12 • CX01 • K12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • K12 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • CX01) (K12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CX01 • SWAP12 • SWAP12 • K12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • K12
  step6 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (ε) (sym (symmetry_K_a.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • CX01 • SWAP12 • K12 ≈ CX02 • K12
  step7 = by-assoc-and (under (ε) (K12) (sym (axiom r009))) Eq.refl Eq.refl

  proved : K12 • CZ02 ≈ CX02 • K12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel48 where

  step0 : CZ02 • K12 ≈ CZ02 • K12 • CX02 • CX02
  step0 = by-assoc-and (under (CZ02 • K12) (ε) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step1 : CZ02 • K12 • CX02 • CX02 ≈ CZ02 • K12 • CX02 • K12 • K12 • CX02
  step1 = by-assoc-and (under (CZ02 • K12 • CX02) (CX02) (sym (axiom r023))) Eq.refl Eq.refl

  step2 : CZ02 • K12 • CX02 • K12 • K12 • CX02 ≈ CZ02 • K12 • K12 • CZ02 • K12 • CX02
  step2 = by-assoc-and (under (CZ02 • K12) (K12 • CX02) (sym (drel47.proved))) Eq.refl Eq.refl

  step3 : CZ02 • K12 • K12 • CZ02 • K12 • CX02 ≈ CZ02 • CZ02 • K12 • CX02
  step3 = by-assoc-and (under (CZ02) (CZ02 • K12 • CX02) (axiom r023)) Eq.refl Eq.refl

  step4 : CZ02 • CZ02 • K12 • CX02 ≈ K12 • CX02
  step4 = by-assoc-and (under (ε) (K12 • CX02) (elim_CZ02.proved)) Eq.refl Eq.refl

  proved : CZ02 • K12 ≈ K12 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_Z_CZ_a where

  step0 : CZ02 • Z1 ≈ K12 • K12 • CZ02 • Z1
  step0 = by-assoc-and (under (ε) (CZ02 • Z1) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ02 • Z1 ≈ K12 • CX02 • K12 • Z1
  step1 = by-assoc-and (under (K12) (Z1) (drel47.proved)) Eq.refl Eq.refl

  step2 : K12 • CX02 • K12 • Z1 ≈ K12 • CX02 • X1 • K12
  step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

  step3 : K12 • CX02 • X1 • K12 ≈ K12 • X1 • CX02 • K12
  step3 = by-assoc-and (under (K12) (K12) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

  step4 : K12 • X1 • CX02 • K12 ≈ Z1 • K12 • CX02 • K12
  step4 = by-assoc-and (under (ε) (CX02 • K12) (drel65.proved)) Eq.refl Eq.refl

  step5 : Z1 • K12 • CX02 • K12 ≈ Z1 • CZ02 • K12 • K12
  step5 = by-assoc-and (under (Z1) (K12) (sym (drel48.proved))) Eq.refl Eq.refl

  step6 : Z1 • CZ02 • K12 • K12 ≈ Z1 • CZ02
  step6 = by-assoc-and (under (Z1 • CZ02) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CZ02 • Z1 ≈ Z1 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_CZ_b where

  step0 : CZ12 • Z0 ≈ SWAP01 • CZ02 • SWAP01 • Z0
  step0 = by-assoc-and (under (ε) (Z0) (axiom r019)) Eq.refl Eq.refl

  step1 : SWAP01 • CZ02 • SWAP01 • Z0 ≈ SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01 • Z0) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • Z1 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

  step3 : SWAP01 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • K12 • K12 • CZ02 • Z1 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (CZ02 • Z1 • SWAP01) (sym (axiom r023))) Eq.refl Eq.refl

  step4 : SWAP01 • K12 • K12 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • K12 • CX02 • K12 • Z1 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • K12) (Z1 • SWAP01) (drel47.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • K12 • CX02 • K12 • Z1 • SWAP01 ≈ SWAP01 • K12 • CX02 • X1 • K12 • SWAP01
  step5 = by-assoc-and (under (SWAP01 • K12 • CX02) (SWAP01) (sym (drel137.proved))) Eq.refl Eq.refl

  step6 : SWAP01 • K12 • CX02 • X1 • K12 • SWAP01 ≈ SWAP01 • K12 • X1 • CX02 • K12 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • K12) (K12 • SWAP01) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

  step7 : SWAP01 • K12 • X1 • CX02 • K12 • SWAP01 ≈ SWAP01 • Z1 • K12 • CX02 • K12 • SWAP01
  step7 = by-assoc-and (under (SWAP01) (CX02 • K12 • SWAP01) (drel65.proved)) Eq.refl Eq.refl

  step8 : SWAP01 • Z1 • K12 • CX02 • K12 • SWAP01 ≈ SWAP01 • Z1 • CZ02 • K12 • K12 • SWAP01
  step8 = by-assoc-and (under (SWAP01 • Z1) (K12 • SWAP01) (sym (drel48.proved))) Eq.refl Eq.refl

  step9 : SWAP01 • Z1 • CZ02 • K12 • K12 • SWAP01 ≈ SWAP01 • Z1 • CZ02 • SWAP01
  step9 = by-assoc-and (under (SWAP01 • Z1 • CZ02) (SWAP01) (axiom r023)) Eq.refl Eq.refl

  step10 : SWAP01 • Z1 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CZ02 • SWAP01
  step10 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step11 : SWAP01 • SWAP01 • Z0 • SWAP01 • CZ02 • SWAP01 ≈ Z0 • SWAP01 • CZ02 • SWAP01
  step11 = by-assoc-and (under (ε) (Z0 • SWAP01 • CZ02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step12 : Z0 • SWAP01 • CZ02 • SWAP01 ≈ Z0 • CZ12
  step12 = by-assoc-and (under (Z0) (ε) (sym (axiom r019))) Eq.refl Eq.refl

  proved : CZ12 • Z0 ≈ Z0 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))

module bifunct_Z_CZ_c where

  step0 : CZ01 • Z2 ≈ K12 • CX01 • K12 • Z2
  step0 = by-assoc-and (under (ε) (Z2) (axiom r001)) Eq.refl Eq.refl

  step1 : K12 • CX01 • K12 • Z2 ≈ K12 • CX01 • X2 • K12
  step1 = by-assoc-and (under (K12 • CX01) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

  step2 : K12 • CX01 • X2 • K12 ≈ K12 • X2 • CX01 • K12
  step2 = by-assoc-and (under (K12) (K12) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

  step3 : K12 • X2 • CX01 • K12 ≈ Z2 • K12 • CX01 • K12
  step3 = by-assoc-and (under (ε) (CX01 • K12) (drel66.proved)) Eq.refl Eq.refl

  step4 : Z2 • K12 • CX01 • K12 ≈ Z2 • CZ01
  step4 = by-assoc-and (under (Z2) (ε) (sym (axiom r001))) Eq.refl Eq.refl

  proved : CZ01 • Z2 ≈ Z2 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_Z_SWAP_a where

  step0 : Z0 • SWAP12 ≈ Z0 • CX12 • CX21 • CX12
  step0 = by-assoc-and (under (Z0) (ε) (axiom r008)) Eq.refl Eq.refl

  step1 : Z0 • CX12 • CX21 • CX12 ≈ CX12 • Z0 • CX21 • CX12
  step1 = by-assoc-and (under (ε) (CX21 • CX12) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

  step2 : CX12 • Z0 • CX21 • CX12 ≈ CX12 • CX21 • Z0 • CX12
  step2 = by-assoc-and (under (CX12) (CX12) (bifunct_Z_CX_d.proved)) Eq.refl Eq.refl

  step3 : CX12 • CX21 • Z0 • CX12 ≈ CX12 • CX21 • CX12 • Z0
  step3 = by-assoc-and (under (CX12 • CX21) (ε) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

  step4 : CX12 • CX21 • CX12 • Z0 ≈ SWAP12 • Z0
  step4 = by-assoc-and (under (ε) (Z0) (sym (axiom r008))) Eq.refl Eq.refl

  proved : Z0 • SWAP12 ≈ SWAP12 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_Z_SWAP_c where

  step0 : Z2 • SWAP01 ≈ Z2 • CX01 • CX10 • CX01
  step0 = by-assoc-and (under (Z2) (ε) (axiom r013)) Eq.refl Eq.refl

  step1 : Z2 • CX01 • CX10 • CX01 ≈ CX01 • Z2 • CX10 • CX01
  step1 = by-assoc-and (under (ε) (CX10 • CX01) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

  step2 : CX01 • Z2 • CX10 • CX01 ≈ CX01 • CX10 • Z2 • CX01
  step2 = by-assoc-and (under (CX01) (CX01) (bifunct_Z_CX_f.proved)) Eq.refl Eq.refl

  step3 : CX01 • CX10 • Z2 • CX01 ≈ CX01 • CX10 • CX01 • Z2
  step3 = by-assoc-and (under (CX01 • CX10) (ε) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

  step4 : CX01 • CX10 • CX01 • Z2 ≈ SWAP01 • Z2
  step4 = by-assoc-and (under (ε) (Z2) (sym (axiom r013))) Eq.refl Eq.refl

  proved : Z2 • SWAP01 ≈ SWAP01 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel59 where

  step0 : X1 • K01 ≈ X1 • K01 • Z1 • Z1
  step0 = by-assoc-and (under (X1 • K01) (ε) (sym (elim_Z1.proved))) Eq.refl Eq.refl

  step1 : X1 • K01 • Z1 • Z1 ≈ X1 • K01 • Z1 • K01 • K01 • Z1
  step1 = by-assoc-and (under (X1 • K01 • Z1) (Z1) (sym (axiom r025))) Eq.refl Eq.refl

  step2 : X1 • K01 • Z1 • K01 • K01 • Z1 ≈ X1 • K01 • K01 • X1 • K01 • Z1
  step2 = by-assoc-and (under (X1 • K01) (K01 • Z1) (drel58.proved)) Eq.refl Eq.refl

  step3 : X1 • K01 • K01 • X1 • K01 • Z1 ≈ X1 • X1 • K01 • Z1
  step3 = by-assoc-and (under (X1) (X1 • K01 • Z1) (axiom r025)) Eq.refl Eq.refl

  step4 : X1 • X1 • K01 • Z1 ≈ K01 • Z1
  step4 = by-assoc-and (under (ε) (K01 • Z1) (elim_X1.proved)) Eq.refl Eq.refl

  proved : X1 • K01 ≈ K01 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_Z_a where

  step0 : Z0 • Z1 ≈ K01 • K01 • Z0 • Z1
  step0 = by-assoc-and (under (ε) (Z0 • Z1) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z0 • Z1 ≈ K01 • X0 • K01 • Z1
  step1 = by-assoc-and (under (K01) (Z1) (axiom r041)) Eq.refl Eq.refl

  step2 : K01 • X0 • K01 • Z1 ≈ K01 • X0 • X1 • K01
  step2 = by-assoc-and (under (K01 • X0) (ε) (sym (drel59.proved))) Eq.refl Eq.refl

  step3 : K01 • X0 • X1 • K01 ≈ K01 • X1 • X0 • K01
  step3 = by-assoc-and (under (K01) (K01) (X0X1.proved)) Eq.refl Eq.refl

  step4 : K01 • X1 • X0 • K01 ≈ K01 • X1 • K01 • Z0
  step4 = by-assoc-and (under (K01 • X1) (ε) (sym (axiom r041))) Eq.refl Eq.refl

  step5 : K01 • X1 • K01 • Z0 ≈ K01 • K01 • Z1 • Z0
  step5 = by-assoc-and (under (K01) (Z0) (drel59.proved)) Eq.refl Eq.refl

  step6 : K01 • K01 • Z1 • Z0 ≈ Z1 • Z0
  step6 = by-assoc-and (under (ε) (Z1 • Z0) (axiom r025)) Eq.refl Eq.refl

  proved : Z0 • Z1 ≈ Z1 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_b where

  step0 : Z0 • Z2 ≈ K01 • K01 • Z0 • Z2
  step0 = by-assoc-and (under (ε) (Z0 • Z2) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z0 • Z2 ≈ K01 • X0 • K01 • Z2
  step1 = by-assoc-and (under (K01) (Z2) (axiom r041)) Eq.refl Eq.refl

  step2 : K01 • X0 • K01 • Z2 ≈ K01 • X0 • Z2 • K01
  step2 = by-assoc-and (under (K01 • X0) (ε) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

  step3 : K01 • X0 • Z2 • K01 ≈ K01 • Z2 • X0 • K01
  step3 = by-assoc-and (under (K01) (K01) (bifunct_X_Z_e.proved)) Eq.refl Eq.refl

  step4 : K01 • Z2 • X0 • K01 ≈ Z2 • K01 • X0 • K01
  step4 = by-assoc-and (under (ε) (X0 • K01) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

  step5 : Z2 • K01 • X0 • K01 ≈ Z2 • K01 • K01 • Z0
  step5 = by-assoc-and (under (Z2 • K01) (ε) (sym (axiom r041))) Eq.refl Eq.refl

  step6 : Z2 • K01 • K01 • Z0 ≈ Z2 • Z0
  step6 = by-assoc-and (under (Z2) (Z0) (axiom r025)) Eq.refl Eq.refl

  proved : Z0 • Z2 ≈ Z2 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_c where

  step0 : Z1 • Z2 ≈ K12 • K12 • Z1 • Z2
  step0 = by-assoc-and (under (ε) (Z1 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • Z1 • Z2 ≈ K12 • X1 • K12 • Z2
  step1 = by-assoc-and (under (K12) (Z2) (sym (drel137.proved))) Eq.refl Eq.refl

  step2 : K12 • X1 • K12 • Z2 ≈ K12 • X1 • X2 • K12
  step2 = by-assoc-and (under (K12 • X1) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

  step3 : K12 • X1 • X2 • K12 ≈ K12 • X2 • X1 • K12
  step3 = by-assoc-and (under (K12) (K12) (bifunct_X_c.proved)) Eq.refl Eq.refl

  step4 : K12 • X2 • X1 • K12 ≈ K12 • X2 • K12 • Z1
  step4 = by-assoc-and (under (K12 • X2) (ε) (drel137.proved)) Eq.refl Eq.refl

  step5 : K12 • X2 • K12 • Z1 ≈ K12 • K12 • Z2 • Z1
  step5 = by-assoc-and (under (K12) (Z1) (drel64.proved)) Eq.refl Eq.refl

  step6 : K12 • K12 • Z2 • Z1 ≈ Z2 • Z1
  step6 = by-assoc-and (under (ε) (Z2 • Z1) (axiom r023)) Eq.refl Eq.refl

  proved : Z1 • Z2 ≈ Z2 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module cadd7 where

  step0 : CX01 • CCX12 • CX01 ≈ CX01 • CX01 • CCX02 • CCX12 • CCX02
  step0 = by-assoc-and (under (CX01) (ε) (axiom r045)) Eq.refl Eq.refl

  step1 : CX01 • CX01 • CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02
  step1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CCX02) (axiom r022)) Eq.refl Eq.refl

  proved : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
  proved = trans step0 (trans step1 (refl))

module symmetry_CCX_c where

  step0 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
  step0 = by-assoc-and (under (ε) (ε) (axiom r033)) Eq.refl Eq.refl

  step1 : SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • SWAP01 • CCX12 • SWAP01 • SWAP12
  step1 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r014)) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP01 • CCX12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • SWAP01 • CCX12) (SWAP01 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • SWAP01 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • SWAP01) (CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP01 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP02) (SWAP02 • SWAP01 • SWAP12) (sym (axiom r032))) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02) (SWAP12) (symmetry_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12
  step6 = by-assoc-and (under (SWAP12) (SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12) (symmetry_SWAP01.proved)) Eq.refl Eq.refl

  step7 : SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP12 • SWAP02 • SWAP12
  step7 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01) (SWAP12 • SWAP02 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step8 : SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP12 • SWAP02 • SWAP12
  step8 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12) (CCX01 • SWAP12 • SWAP02 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step9 : SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP01
  step9 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • CCX01) (ε) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

  step10 : SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01
  step10 = by-assoc-and (under (ε) (CCX01 • SWAP01) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

  proved : CCX01 ≈ SWAP01 • CCX01 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module symmetry_SWAP02_alt where

  step0 : SWAP02 ≈ CX02 • CX20 • CX02
  step0 = by-assoc-and (under (ε) (ε) (axiom r010)) Eq.refl Eq.refl

  step1 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • SWAP12 • CX01 • SWAP12
  step1 = by-assoc-and (under (CX02 • CX20) (ε) (axiom r009)) Eq.refl Eq.refl

  step2 : CX02 • CX20 • SWAP12 • CX01 • SWAP12 ≈ CX02 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12
  step2 = by-assoc-and (under (CX02) (SWAP12 • CX01 • SWAP12) (symmetry_CX_j.proved)) Eq.refl Eq.refl

  step3 : CX02 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12
  step3 = by-assoc-and (under (ε) (SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step4 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • CX01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CX01 • SWAP12 • SWAP12 • CX10) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step5 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CX10 • CX01 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • CX01) (CX10 • CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • CX01 • CX10 • CX01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12
  step6 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r013))) Eq.refl Eq.refl

  proved : SWAP02 ≈ SWAP12 • SWAP01 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_CCX_f where

  step0 : CCX02 ≈ CCX02 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (ε) (CCX02 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CCX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

  step3 : SWAP12 • CCX01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX01 • SWAP01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP01 • CCX01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP12 • SWAP01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (axiom r033)) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP02
  step5 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP12 • CCX02) (ε) (sym (symmetry_SWAP02_alt.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02
  step6 = by-assoc-and (under (ε) (CCX02 • SWAP02) (sym (symmetry_SWAP02_alt.proved))) Eq.refl Eq.refl

  proved : CCX02 ≈ SWAP02 • CCX02 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_CCX_g where

  step0 : CCX12 ≈ CCX12 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CCX02 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step3 : SWAP01 • CCX02 • SWAP01 ≈ SWAP01 • SWAP02 • CCX02 • SWAP02 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (symmetry_CCX_f.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP02 • CCX02 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • SWAP02 • CCX02) (SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP02 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12
  step6 = by-assoc-and (under (SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12
  step7 = by-assoc-and (under (ε) (SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 • SWAP12
  step8 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (axiom r014)) Eq.refl Eq.refl

  step9 : SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP12
  step9 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP01 • CCX12) (SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step10 : SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12
  step10 = by-assoc-and (under (SWAP12) (CCX12 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CCX12 ≈ SWAP12 • CCX12 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module cadd0 where

  step0 : CX02 • CCX12 • CX02 ≈ CX02 • CCX12 • SWAP12 • CX01 • SWAP12
  step0 = by-assoc-and (under (CX02 • CCX12) (ε) (axiom r009)) Eq.refl Eq.refl

  step1 : CX02 • CCX12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CCX12 • SWAP12 • CX01 • SWAP12
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP12 • CX01 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • SWAP12 • CCX12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CCX12 • CX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX01) (CX01 • SWAP12) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • CCX12 • CX01 • SWAP12 ≈ SWAP12 • CCX02 • CCX12 • CCX02 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (cadd7.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX02 • CCX12 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CCX02) (CCX02 • SWAP12) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

  step5 : SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01
  step5 = by-assoc-and (under (SWAP12 • CCX02 • SWAP12 • CCX12) (ε) (sym (axiom r033))) Eq.refl Eq.refl

  step6 : SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CCX01
  step6 = by-assoc-and (under (ε) (CCX12 • CCX01) (sym (axiom r033))) Eq.refl Eq.refl

  proved : CX02 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel90 where

  step0 : CX10 • CCX01 ≈ CX10 • SWAP02 • CCX12 • SWAP02
  step0 = by-assoc-and (under (CX10) (ε) (axiom r032)) Eq.refl Eq.refl

  step1 : CX10 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX10 • SWAP02 • CCX12 • SWAP02
  step1 = by-assoc-and (under (ε) (CX10 • SWAP02 • CCX12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP02 • CX10 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CX12 • CCX12 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • CX12 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX10 • CX12 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r044)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX12 • CX10 • CX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • CX12 • SWAP02 • CX12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CCX12) (CX12 • SWAP02) (symmetry_CX_b.proved)) Eq.refl Eq.refl

  step5 : SWAP02 • CCX12 • SWAP02 • CX12 • SWAP02 • CX12 • SWAP02 ≈ CCX01 • CX12 • SWAP02 • CX12 • SWAP02
  step5 = by-assoc-and (under (ε) (CX12 • SWAP02 • CX12 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

  step6 : CCX01 • CX12 • SWAP02 • CX12 • SWAP02 ≈ CCX01 • CX12 • CX10
  step6 = by-assoc-and (under (CCX01 • CX12) (ε) (sym (symmetry_CX_b.proved))) Eq.refl Eq.refl

  proved : CX10 • CCX01 ≈ CCX01 • CX12 • CX10
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module cadd1 where

  step0 : CX10 • CCX01 • CX10 ≈ CCX01 • CX12 • CX10 • CX10
  step0 = by-assoc-and (under (ε) (CX10) (drel90.proved)) Eq.refl Eq.refl

  step1 : CCX01 • CX12 • CX10 • CX10 ≈ CCX01 • CX12
  step1 = by-assoc-and (under (CCX01 • CX12) (ε) (elim_CX10.proved)) Eq.refl Eq.refl

  step2 : CCX01 • CX12 ≈ X0 • X0 • CCX01 • CX12
  step2 = by-assoc-and (under (ε) (CCX01 • CX12) (sym (axiom r021))) Eq.refl Eq.refl

  step3 : X0 • X0 • CCX01 • CX12 ≈ X0 • CCX01 • CX12 • X0 • CX12
  step3 = by-assoc-and (under (X0) (CX12) (axiom r042)) Eq.refl Eq.refl

  step4 : X0 • CCX01 • CX12 • X0 • CX12 ≈ X0 • CCX01 • X0 • CX12 • CX12
  step4 = by-assoc-and (under (X0 • CCX01) (CX12) (axiom r026)) Eq.refl Eq.refl

  step5 : X0 • CCX01 • X0 • CX12 • CX12 ≈ X0 • CCX01 • X0
  step5 = by-assoc-and (under (X0 • CCX01 • X0) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

  proved : CX10 • CCX01 • CX10 ≈ X0 • CCX01 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel155 where

  step0 : CX21 • CCX12 ≈ SWAP12 • CX12 • SWAP12 • CCX12
  step0 = by-assoc-and (under (ε) (CCX12) (symmetry_CX_g.proved)) Eq.refl Eq.refl

  step1 : SWAP12 • CX12 • SWAP12 • CCX12 ≈ SWAP12 • CX12 • SWAP12 • CCX12 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (SWAP12 • CX12 • SWAP12 • CCX12) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • CX12 • SWAP12 • CCX12 • SWAP12 • SWAP12 ≈ SWAP12 • CX12 • CCX12 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX12) (SWAP12) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • CX12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • CX12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r044)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX12 • CX10 • CX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12 • SWAP12 • CX12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CCX12 • CX10) (CX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CCX12 • CX10 • SWAP12 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12 • CX21
  step5 = by-assoc-and (under (SWAP12 • CCX12 • CX10 • SWAP12) (ε) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CCX12 • CX10 • SWAP12 • CX21 ≈ SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX21
  step6 = by-assoc-and (under (SWAP12 • CCX12) (CX10 • SWAP12 • CX21) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX21 ≈ SWAP12 • CCX12 • SWAP12 • CX20 • CX21
  step7 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12) (CX21) (sym (symmetry_CX_j.proved))) Eq.refl Eq.refl

  step8 : SWAP12 • CCX12 • SWAP12 • CX20 • CX21 ≈ CCX12 • CX20 • CX21
  step8 = by-assoc-and (under (ε) (CX20 • CX21) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  proved : CX21 • CCX12 ≈ CCX12 • CX20 • CX21
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel141 where

  step0 : CX01 • CCX01 ≈ CX01 • SWAP02 • CCX12 • SWAP02
  step0 = by-assoc-and (under (CX01) (ε) (axiom r032)) Eq.refl Eq.refl

  step1 : CX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX01 • SWAP02 • CCX12 • SWAP02
  step1 = by-assoc-and (under (ε) (CX01 • SWAP02 • CCX12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP02 • CX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CX21 • CCX12 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • CX21 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • CX21 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel155.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX12 • CX20 • CX21 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • CX21 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CCX12) (CX21 • SWAP02) (axiom r029)) Eq.refl Eq.refl

  step5 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • CX21 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • CX21 • SWAP02
  step5 = by-assoc-and (under (ε) (CX02 • SWAP02 • CX21 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

  step6 : CCX01 • CX02 • SWAP02 • CX21 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02
  step6 = by-assoc-and (under (CCX01 • CX02 • SWAP02) (SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step7 : CCX01 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • SWAP02 • CX01
  step7 = by-assoc-and (under (CCX01 • CX02 • SWAP02 • SWAP02 • CX01) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step8 : CCX01 • CX02 • SWAP02 • SWAP02 • CX01 ≈ CCX01 • CX02 • CX01
  step8 = by-assoc-and (under (CCX01 • CX02) (CX01) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : CX01 • CCX01 ≈ CCX01 • CX02 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel96 where

  step0 : X1 • CCX01 ≈ X1 • SWAP02 • CCX12 • SWAP02
  step0 = by-assoc-and (under (X1) (ε) (axiom r032)) Eq.refl Eq.refl

  step1 : X1 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X1 • CCX12 • SWAP02
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP02) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

  step2 : SWAP02 • X1 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • X1 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (SWAP02) (drel131.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • CCX12 • CX20 • X1 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • SWAP02 • X1
  step3 = by-assoc-and (under (SWAP02 • CCX12 • CX20) (ε) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX12 • CX20 • SWAP02 • X1 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 • X1
  step4 = by-assoc-and (under (SWAP02 • CCX12) (SWAP02 • X1) (axiom r029)) Eq.refl Eq.refl

  step5 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 • X1 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • X1
  step5 = by-assoc-and (under (SWAP02 • CCX12 • SWAP02 • CX02) (X1) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step6 : SWAP02 • CCX12 • SWAP02 • CX02 • X1 ≈ CCX01 • CX02 • X1
  step6 = by-assoc-and (under (ε) (CX02 • X1) (sym (axiom r032))) Eq.refl Eq.refl

  proved : X1 • CCX01 ≈ CCX01 • CX02 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module cadd2 where

  step0 : CX01 • CCX01 • CX01 ≈ CCX01 • CX02 • CX01 • CX01
  step0 = by-assoc-and (under (ε) (CX01) (drel141.proved)) Eq.refl Eq.refl

  step1 : CCX01 • CX02 • CX01 • CX01 ≈ CCX01 • CX02
  step1 = by-assoc-and (under (CCX01 • CX02) (ε) (axiom r022)) Eq.refl Eq.refl

  step2 : CCX01 • CX02 ≈ X1 • X1 • CCX01 • CX02
  step2 = by-assoc-and (under (ε) (CCX01 • CX02) (sym (elim_X1.proved))) Eq.refl Eq.refl

  step3 : X1 • X1 • CCX01 • CX02 ≈ X1 • CCX01 • CX02 • X1 • CX02
  step3 = by-assoc-and (under (X1) (CX02) (drel96.proved)) Eq.refl Eq.refl

  step4 : X1 • CCX01 • CX02 • X1 • CX02 ≈ X1 • CCX01 • X1 • CX02 • CX02
  step4 = by-assoc-and (under (X1 • CCX01) (CX02) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

  step5 : X1 • CCX01 • X1 • CX02 • CX02 ≈ X1 • CCX01 • X1
  step5 = by-assoc-and (under (X1 • CCX01 • X1) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : CX01 • CCX01 • CX01 ≈ X1 • CCX01 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module cadd3 where

  step0 : CX20 • CCX01 • CX20 ≈ CX20 • CCX01 • SWAP02 • CX02 • SWAP02
  step0 = by-assoc-and (under (CX20 • CCX01) (ε) (axiom r029)) Eq.refl Eq.refl

  step1 : CX20 • CCX01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • CCX01 • SWAP02 • CX02 • SWAP02
  step1 = by-assoc-and (under (ε) (CCX01 • SWAP02 • CX02 • SWAP02) (axiom r029)) Eq.refl Eq.refl

  step2 : SWAP02 • CX02 • SWAP02 • CCX01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • CX02 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • CX02 • SWAP02) (SWAP02 • CX02 • SWAP02) (axiom r032)) Eq.refl Eq.refl

  step3 : SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • CX02 • SWAP02
  step3 = by-assoc-and (under (SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • CX02 • SWAP02 ≈ SWAP02 • CX02 • CCX12 • CX02 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CX02) (CCX12 • CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step5 : SWAP02 • CX02 • CCX12 • CX02 • SWAP02 ≈ SWAP02 • CCX01 • CCX12 • CCX01 • SWAP02
  step5 = by-assoc-and (under (SWAP02) (SWAP02) (cadd0.proved)) Eq.refl Eq.refl

  step6 : SWAP02 • CCX01 • CCX12 • CCX01 • SWAP02 ≈ SWAP02 • CCX01 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02
  step6 = by-assoc-and (under (SWAP02 • CCX01 • CCX12) (SWAP02) (axiom r032)) Eq.refl Eq.refl

  step7 : SWAP02 • CCX01 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02
  step7 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02) (axiom r032)) Eq.refl Eq.refl

  step8 : SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12
  step8 = by-assoc-and (under (SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step9 : SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12
  step9 = by-assoc-and (under (ε) (CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step10 : CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • CCX01 • CCX12
  step10 = by-assoc-and (under (CCX12) (CCX12) (sym (axiom r032))) Eq.refl Eq.refl

  proved : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
