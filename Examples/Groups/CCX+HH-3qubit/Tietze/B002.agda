{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B002 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r001 ; r002 ; r004 ; r008 ; r010 ; r012 ; r013 ; r015 ; r016 ; r018 ; r019 ; r023 ; r025 ; r026 ; r027 ; r028 ; r030 ; r034 ; r035 ; r038 ; r039 ; r041 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Proofs.B000 using (module X0X1)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_b ; module bifunct_X_CX_c ; module bifunct_X_CX_d ; module bifunct_X_CX_e ; module bifunct_X_CX_f ; module bifunct_X_K_b ; module drel162 ; module drel46 ; module elim_CX12 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module elim_X1 ; module symmetry_CX_e ; module symmetry_CX_f ; module symmetry_CX_h ; module symmetry_CX_i)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module bifunct_Z_CX_b ; module bifunct_Z_K_b ; module drel64 ; module drel66 ; module elim_X2 ; module elim_Z0)

module bifunct_Z_CX_e where

  step0 : Z2 • CX01 ≈ Z2 • CX01 • K01 • K01
  step0 = by-assoc-and (under (Z2 • CX01) (ε) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : Z2 • CX01 • K01 • K01 ≈ Z2 • K01 • K01 • CX01 • K01 • K01
  step1 = by-assoc-and (under (Z2) (CX01 • K01 • K01) (sym (axiom r025))) Eq.refl Eq.refl

  step2 : Z2 • K01 • K01 • CX01 • K01 • K01 ≈ Z2 • K01 • CX10 • K01
  step2 = by-assoc-and (under (Z2 • K01) (K01) (sym (axiom r012))) Eq.refl Eq.refl

  step3 : Z2 • K01 • CX10 • K01 ≈ K01 • Z2 • CX10 • K01
  step3 = by-assoc-and (under (ε) (CX10 • K01) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

  step4 : K01 • Z2 • CX10 • K01 ≈ K01 • SWAP02 • Z0 • SWAP02 • CX10 • K01
  step4 = by-assoc-and (under (K01) (CX10 • K01) (axiom r016)) Eq.refl Eq.refl

  step5 : K01 • SWAP02 • Z0 • SWAP02 • CX10 • K01 ≈ K01 • SWAP02 • Z0 • SWAP02 • CX10 • SWAP02 • SWAP02 • K01
  step5 = by-assoc-and (under (K01 • SWAP02 • Z0 • SWAP02 • CX10) (K01) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step6 : K01 • SWAP02 • Z0 • SWAP02 • CX10 • SWAP02 • SWAP02 • K01 ≈ K01 • SWAP02 • Z0 • CX12 • SWAP02 • K01
  step6 = by-assoc-and (under (K01 • SWAP02 • Z0) (SWAP02 • K01) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

  step7 : K01 • SWAP02 • Z0 • CX12 • SWAP02 • K01 ≈ K01 • SWAP02 • CX12 • Z0 • SWAP02 • K01
  step7 = by-assoc-and (under (K01 • SWAP02) (SWAP02 • K01) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

  step8 : K01 • SWAP02 • CX12 • Z0 • SWAP02 • K01 ≈ K01 • SWAP02 • SWAP02 • CX10 • SWAP02 • Z0 • SWAP02 • K01
  step8 = by-assoc-and (under (K01 • SWAP02) (Z0 • SWAP02 • K01) (symmetry_CX_f.proved)) Eq.refl Eq.refl

  step9 : K01 • SWAP02 • SWAP02 • CX10 • SWAP02 • Z0 • SWAP02 • K01 ≈ K01 • CX10 • SWAP02 • Z0 • SWAP02 • K01
  step9 = by-assoc-and (under (K01) (CX10 • SWAP02 • Z0 • SWAP02 • K01) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step10 : K01 • CX10 • SWAP02 • Z0 • SWAP02 • K01 ≈ K01 • CX10 • Z2 • K01
  step10 = by-assoc-and (under (K01 • CX10) (K01) (sym (axiom r016))) Eq.refl Eq.refl

  step11 : K01 • CX10 • Z2 • K01 ≈ K01 • K01 • CX01 • K01 • Z2 • K01
  step11 = by-assoc-and (under (K01) (Z2 • K01) (axiom r012)) Eq.refl Eq.refl

  step12 : K01 • K01 • CX01 • K01 • Z2 • K01 ≈ CX01 • K01 • Z2 • K01
  step12 = by-assoc-and (under (ε) (CX01 • K01 • Z2 • K01) (axiom r025)) Eq.refl Eq.refl

  step13 : CX01 • K01 • Z2 • K01 ≈ CX01 • K01 • K01 • Z2
  step13 = by-assoc-and (under (CX01 • K01) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

  step14 : CX01 • K01 • K01 • Z2 ≈ CX01 • Z2
  step14 = by-assoc-and (under (CX01) (Z2) (axiom r025)) Eq.refl Eq.refl

  proved : Z2 • CX01 ≈ CX01 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (refl)))))))))))))))

module bifunct_X_SWAP_c where

  step0 : X1 • SWAP02 ≈ X1 • CX02 • CX20 • CX02
  step0 = by-assoc-and (under (X1) (ε) (axiom r010)) Eq.refl Eq.refl

  step1 : X1 • CX02 • CX20 • CX02 ≈ CX02 • X1 • CX20 • CX02
  step1 = by-assoc-and (under (ε) (CX20 • CX02) (sym (bifunct_X_CX_e.proved))) Eq.refl Eq.refl

  step2 : CX02 • X1 • CX20 • CX02 ≈ CX02 • CX20 • X1 • CX02
  step2 = by-assoc-and (under (CX02) (CX02) (sym (bifunct_X_CX_f.proved))) Eq.refl Eq.refl

  step3 : CX02 • CX20 • X1 • CX02 ≈ CX02 • CX20 • CX02 • X1
  step3 = by-assoc-and (under (CX02 • CX20) (ε) (sym (bifunct_X_CX_e.proved))) Eq.refl Eq.refl

  step4 : CX02 • CX20 • CX02 • X1 ≈ SWAP02 • X1
  step4 = by-assoc-and (under (ε) (X1) (sym (axiom r010))) Eq.refl Eq.refl

  proved : X1 • SWAP02 ≈ SWAP02 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel133 where

  step0 : X2 • CX21 ≈ X2 • SWAP02 • CX01 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CX01 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CX01 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • X0 • CX01 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (CX01 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • CX01 • SWAP02 ≈ SWAP02 • CX01 • X1 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel162.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CX01 • X1 • X0 • SWAP02 ≈ SWAP02 • CX01 • X1 • SWAP02 • SWAP02 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CX01 • X1) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CX01 • X1 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CX01 • X1 • SWAP02 • X2
  step5 = by-assoc-and (under (SWAP02 • CX01 • X1 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  step6 : SWAP02 • CX01 • X1 • SWAP02 • X2 ≈ SWAP02 • CX01 • SWAP02 • X1 • X2
  step6 = by-assoc-and (under (SWAP02 • CX01) (X2) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

  step7 : SWAP02 • CX01 • SWAP02 • X1 • X2 ≈ CX21 • X1 • X2
  step7 = by-assoc-and (under (ε) (X1 • X2) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

  proved : X2 • CX21 ≈ CX21 • X1 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel67 where

  step0 : X1 • CX10 ≈ SWAP01 • X0 • SWAP01 • CX10
  step0 = by-assoc-and (under (ε) (CX10) (axiom r028)) Eq.refl Eq.refl

  step1 : SWAP01 • X0 • SWAP01 • CX10 ≈ SWAP01 • X0 • SWAP01 • CX10 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • X0 • SWAP01 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • X0 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • CX01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  step3 : SWAP01 • X0 • CX01 • SWAP01 ≈ SWAP01 • CX01 • X1 • X0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel162.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX01 • X1 • X0 • SWAP01 ≈ SWAP01 • CX01 • SWAP01 • X0 • SWAP01 • X0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CX01) (X0 • SWAP01) (axiom r028)) Eq.refl Eq.refl

  step5 : SWAP01 • CX01 • SWAP01 • X0 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX01 • SWAP01 • X0 • X1
  step5 = by-assoc-and (under (SWAP01 • CX01 • SWAP01 • X0) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  step6 : SWAP01 • CX01 • SWAP01 • X0 • X1 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • X1
  step6 = by-assoc-and (under (SWAP01) (SWAP01 • X0 • X1) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • X1 ≈ SWAP01 • SWAP01 • CX10 • X0 • X1
  step7 = by-assoc-and (under (SWAP01 • SWAP01 • CX10) (X0 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : SWAP01 • SWAP01 • CX10 • X0 • X1 ≈ CX10 • X0 • X1
  step8 = by-assoc-and (under (ε) (CX10 • X0 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : X1 • CX10 ≈ CX10 • X0 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel69 where

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

module drel70 where

  step0 : CX12 • X1 ≈ CX12 • X1 • CX12 • CX12
  step0 = by-assoc-and (under (CX12 • X1) (ε) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step1 : CX12 • X1 • CX12 • CX12 ≈ CX12 • X1 • CX12 • X2 • X2 • CX12
  step1 = by-assoc-and (under (CX12 • X1 • CX12) (CX12) (sym (elim_X2.proved))) Eq.refl Eq.refl

  step2 : CX12 • X1 • CX12 • X2 • X2 • CX12 ≈ CX12 • X1 • CX12 • X2 • X1 • X1 • X2 • CX12
  step2 = by-assoc-and (under (CX12 • X1 • CX12 • X2) (X2 • CX12) (sym (elim_X1.proved))) Eq.refl Eq.refl

  step3 : CX12 • X1 • CX12 • X2 • X1 • X1 • X2 • CX12 ≈ CX12 • X1 • X1 • CX12 • X1 • X2 • CX12
  step3 = by-assoc-and (under (CX12 • X1) (X1 • X2 • CX12) (sym (drel69.proved))) Eq.refl Eq.refl

  step4 : CX12 • X1 • X1 • CX12 • X1 • X2 • CX12 ≈ CX12 • CX12 • X1 • X2 • CX12
  step4 = by-assoc-and (under (CX12) (CX12 • X1 • X2 • CX12) (elim_X1.proved)) Eq.refl Eq.refl

  step5 : CX12 • CX12 • X1 • X2 • CX12 ≈ X1 • X2 • CX12
  step5 = by-assoc-and (under (ε) (X1 • X2 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

  proved : CX12 • X1 ≈ X1 • X2 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel84 where

  step0 : X2 • CX12 ≈ X2 • SWAP02 • CX10 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (symmetry_CX_f.proved)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • CX10 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CX10 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CX10 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CX10 • SWAP02 ≈ SWAP02 • X0 • CX10 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (CX10 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • CX10 • SWAP02 ≈ SWAP02 • CX10 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r038)) Eq.refl Eq.refl

  step4 : SWAP02 • CX10 • X0 • SWAP02 ≈ SWAP02 • CX10 • SWAP02 • SWAP02 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CX10) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CX10 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CX10 • SWAP02 • X2
  step5 = by-assoc-and (under (SWAP02 • CX10 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  step6 : SWAP02 • CX10 • SWAP02 • X2 ≈ CX12 • X2
  step6 = by-assoc-and (under (ε) (X2) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

  proved : X2 • CX12 ≈ CX12 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_X_c where

  step0 : X2 ≈ X2 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (X2) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : X2 • SWAP12 • SWAP12 ≈ X2 • CX12 • CX21 • CX12 • SWAP12
  step1 = by-assoc-and (under (X2) (SWAP12) (axiom r008)) Eq.refl Eq.refl

  step2 : X2 • CX12 • CX21 • CX12 • SWAP12 ≈ CX12 • X2 • CX21 • CX12 • SWAP12
  step2 = by-assoc-and (under (ε) (CX21 • CX12 • SWAP12) (drel84.proved)) Eq.refl Eq.refl

  step3 : CX12 • X2 • CX21 • CX12 • SWAP12 ≈ CX12 • CX21 • X1 • X2 • CX12 • SWAP12
  step3 = by-assoc-and (under (CX12) (CX12 • SWAP12) (drel133.proved)) Eq.refl Eq.refl

  step4 : CX12 • CX21 • X1 • X2 • CX12 • SWAP12 ≈ CX12 • CX21 • CX12 • X1 • SWAP12
  step4 = by-assoc-and (under (CX12 • CX21) (SWAP12) (sym (drel70.proved))) Eq.refl Eq.refl

  step5 : CX12 • CX21 • CX12 • X1 • SWAP12 ≈ SWAP12 • X1 • SWAP12
  step5 = by-assoc-and (under (ε) (X1 • SWAP12) (sym (axiom r008))) Eq.refl Eq.refl

  proved : X2 ≈ SWAP12 • X1 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module bifunct_X_CZ_a where

  step0 : X1 • CZ02 ≈ X1 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (X1) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : X1 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • X1 • SWAP12 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (X1 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • X1 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • X2 • CZ01 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • X2 • CZ01 • SWAP12 ≈ SWAP12 • X2 • K12 • CX01 • K12 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • X2) (SWAP12) (axiom r001)) Eq.refl Eq.refl

  step4 : SWAP12 • X2 • K12 • CX01 • K12 • SWAP12 ≈ SWAP12 • K12 • Z2 • CX01 • K12 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CX01 • K12 • SWAP12) (drel64.proved)) Eq.refl Eq.refl

  step5 : SWAP12 • K12 • Z2 • CX01 • K12 • SWAP12 ≈ SWAP12 • K12 • CX01 • Z2 • K12 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • K12) (K12 • SWAP12) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • K12 • CX01 • Z2 • K12 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • X2 • SWAP12
  step6 = by-assoc-and (under (SWAP12 • K12 • CX01) (SWAP12) (sym (drel66.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • K12 • CX01 • K12 • X2 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 • SWAP12 • SWAP12
  step7 = by-assoc-and (under (SWAP12 • K12 • CX01 • K12) (SWAP12) (symmetry_X_c.proved)) Eq.refl Eq.refl

  step8 : SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 • SWAP12 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • SWAP12 • X1
  step8 = by-assoc-and (under (SWAP12 • K12 • CX01 • K12 • SWAP12 • X1) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step9 : SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 ≈ SWAP12 • CZ01 • SWAP12 • X1
  step9 = by-assoc-and (under (SWAP12) (SWAP12 • X1) (sym (axiom r001))) Eq.refl Eq.refl

  step10 : SWAP12 • CZ01 • SWAP12 • X1 ≈ CZ02 • X1
  step10 = by-assoc-and (under (ε) (X1) (sym (axiom r018))) Eq.refl Eq.refl

  proved : X1 • CZ02 ≈ CZ02 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module bifunct_X_CZ_b where

  step0 : X0 • CZ12 ≈ X0 • SWAP01 • CZ02 • SWAP01
  step0 = by-assoc-and (under (X0) (ε) (axiom r019)) Eq.refl Eq.refl

  step1 : X0 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • X0 • SWAP01 • CZ02 • SWAP01
  step1 = by-assoc-and (under (ε) (X0 • SWAP01 • CZ02 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • X0 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • X1 • CZ02 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (sym (axiom r028))) Eq.refl Eq.refl

  step3 : SWAP01 • X1 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • X1 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_X_CZ_a.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CZ02 • X1 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • X0 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (axiom r028)) Eq.refl Eq.refl

  step5 : SWAP01 • CZ02 • SWAP01 • X0 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • X0
  step5 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01 • X0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CZ02 • SWAP01 • X0 ≈ CZ12 • X0
  step6 = by-assoc-and (under (ε) (X0) (sym (axiom r019))) Eq.refl Eq.refl

  proved : X0 • CZ12 ≈ CZ12 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_CZ_c where

  step0 : X2 • CZ01 ≈ X2 • K12 • CX01 • K12
  step0 = by-assoc-and (under (X2) (ε) (axiom r001)) Eq.refl Eq.refl

  step1 : X2 • K12 • CX01 • K12 ≈ K12 • Z2 • CX01 • K12
  step1 = by-assoc-and (under (ε) (CX01 • K12) (drel64.proved)) Eq.refl Eq.refl

  step2 : K12 • Z2 • CX01 • K12 ≈ K12 • CX01 • Z2 • K12
  step2 = by-assoc-and (under (K12) (K12) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

  step3 : K12 • CX01 • Z2 • K12 ≈ K12 • CX01 • K12 • X2
  step3 = by-assoc-and (under (K12 • CX01) (ε) (sym (drel66.proved))) Eq.refl Eq.refl

  step4 : K12 • CX01 • K12 • X2 ≈ CZ01 • X2
  step4 = by-assoc-and (under (ε) (X2) (sym (axiom r001))) Eq.refl Eq.refl

  proved : X2 • CZ01 ≈ CZ01 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_SWAP_a where

  step0 : X0 • SWAP12 ≈ X0 • CX12 • CX21 • CX12
  step0 = by-assoc-and (under (X0) (ε) (axiom r008)) Eq.refl Eq.refl

  step1 : X0 • CX12 • CX21 • CX12 ≈ CX12 • X0 • CX21 • CX12
  step1 = by-assoc-and (under (ε) (CX21 • CX12) (sym (axiom r026))) Eq.refl Eq.refl

  step2 : CX12 • X0 • CX21 • CX12 ≈ CX12 • CX21 • X0 • CX12
  step2 = by-assoc-and (under (CX12) (CX12) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

  step3 : CX12 • CX21 • X0 • CX12 ≈ CX12 • CX21 • CX12 • X0
  step3 = by-assoc-and (under (CX12 • CX21) (ε) (sym (axiom r026))) Eq.refl Eq.refl

  step4 : CX12 • CX21 • CX12 • X0 ≈ SWAP12 • X0
  step4 = by-assoc-and (under (ε) (X0) (sym (axiom r008))) Eq.refl Eq.refl

  proved : X0 • SWAP12 ≈ SWAP12 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_SWAP_b where

  step0 : X2 • SWAP01 ≈ X2 • CX01 • CX10 • CX01
  step0 = by-assoc-and (under (X2) (ε) (axiom r013)) Eq.refl Eq.refl

  step1 : X2 • CX01 • CX10 • CX01 ≈ CX01 • X2 • CX10 • CX01
  step1 = by-assoc-and (under (ε) (CX10 • CX01) (sym (bifunct_X_CX_d.proved))) Eq.refl Eq.refl

  step2 : CX01 • X2 • CX10 • CX01 ≈ CX01 • CX10 • X2 • CX01
  step2 = by-assoc-and (under (CX01) (CX01) (sym (bifunct_X_CX_c.proved))) Eq.refl Eq.refl

  step3 : CX01 • CX10 • X2 • CX01 ≈ CX01 • CX10 • CX01 • X2
  step3 = by-assoc-and (under (CX01 • CX10) (ε) (sym (bifunct_X_CX_d.proved))) Eq.refl Eq.refl

  step4 : CX01 • CX10 • CX01 • X2 ≈ SWAP01 • X2
  step4 = by-assoc-and (under (ε) (X2) (sym (axiom r013))) Eq.refl Eq.refl

  proved : X2 • SWAP01 ≈ SWAP01 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel137 where

  step0 : X1 • K12 ≈ K12 • K12 • X1 • K12
  step0 = by-assoc-and (under (ε) (X1 • K12) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • X1 • K12 ≈ K12 • Z1
  step1 = by-assoc-and (under (K12) (ε) (sym (axiom r004))) Eq.refl Eq.refl

  proved : X1 • K12 ≈ K12 • Z1
  proved = trans step0 (trans step1 (refl))

module bifunct_X_Z_a where

  step0 : X0 • Z1 ≈ X0 • K12 • K12 • Z1
  step0 = by-assoc-and (under (X0) (Z1) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : X0 • K12 • K12 • Z1 ≈ K12 • X0 • K12 • Z1
  step1 = by-assoc-and (under (ε) (K12 • Z1) (axiom r027)) Eq.refl Eq.refl

  step2 : K12 • X0 • K12 • Z1 ≈ K12 • X0 • X1 • K12
  step2 = by-assoc-and (under (K12 • X0) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

  step3 : K12 • X0 • X1 • K12 ≈ K12 • X1 • X0 • K12
  step3 = by-assoc-and (under (K12) (K12) (X0X1.proved)) Eq.refl Eq.refl

  step4 : K12 • X1 • X0 • K12 ≈ K12 • X1 • K12 • X0
  step4 = by-assoc-and (under (K12 • X1) (ε) (axiom r027)) Eq.refl Eq.refl

  step5 : K12 • X1 • K12 • X0 ≈ K12 • K12 • Z1 • X0
  step5 = by-assoc-and (under (K12) (X0) (drel137.proved)) Eq.refl Eq.refl

  step6 : K12 • K12 • Z1 • X0 ≈ Z1 • X0
  step6 = by-assoc-and (under (ε) (Z1 • X0) (axiom r023)) Eq.refl Eq.refl

  proved : X0 • Z1 ≈ Z1 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel58 where

  step0 : Z1 • K01 ≈ SWAP01 • Z0 • SWAP01 • K01
  step0 = by-assoc-and (under (ε) (K01) (axiom r034)) Eq.refl Eq.refl

  step1 : SWAP01 • Z0 • SWAP01 • K01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • K01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01) (ε) (axiom r035)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • K01 • SWAP01 ≈ SWAP01 • Z0 • K01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (K01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • K01 • SWAP01 ≈ SWAP01 • K01 • K01 • Z0 • K01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (Z0 • K01 • SWAP01) (sym (axiom r025))) Eq.refl Eq.refl

  step4 : SWAP01 • K01 • K01 • Z0 • K01 • SWAP01 ≈ SWAP01 • K01 • X0 • K01 • K01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • K01) (K01 • SWAP01) (axiom r041)) Eq.refl Eq.refl

  step5 : SWAP01 • K01 • X0 • K01 • K01 • SWAP01 ≈ SWAP01 • K01 • X0 • SWAP01
  step5 = by-assoc-and (under (SWAP01 • K01 • X0) (SWAP01) (axiom r025)) Eq.refl Eq.refl

  step6 : SWAP01 • K01 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • K01 • SWAP01 • X0 • SWAP01
  step6 = by-assoc-and (under (SWAP01) (X0 • SWAP01) (axiom r035)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • K01 • SWAP01 • X0 • SWAP01 ≈ K01 • SWAP01 • X0 • SWAP01
  step7 = by-assoc-and (under (ε) (K01 • SWAP01 • X0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : K01 • SWAP01 • X0 • SWAP01 ≈ K01 • X1
  step8 = by-assoc-and (under (K01) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  proved : Z1 • K01 ≈ K01 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module bifunct_X_Z_b where

  step0 : X1 • Z0 ≈ K01 • K01 • X1 • Z0
  step0 = by-assoc-and (under (ε) (X1 • Z0) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • X1 • Z0 ≈ K01 • Z1 • K01 • Z0
  step1 = by-assoc-and (under (K01) (Z0) (sym (drel58.proved))) Eq.refl Eq.refl

  step2 : K01 • Z1 • K01 • Z0 ≈ K01 • Z1 • X0 • K01
  step2 = by-assoc-and (under (K01 • Z1) (ε) (axiom r041)) Eq.refl Eq.refl

  step3 : K01 • Z1 • X0 • K01 ≈ K01 • X0 • Z1 • K01
  step3 = by-assoc-and (under (K01) (K01) (sym (bifunct_X_Z_a.proved))) Eq.refl Eq.refl

  step4 : K01 • X0 • Z1 • K01 ≈ K01 • X0 • K01 • X1
  step4 = by-assoc-and (under (K01 • X0) (ε) (drel58.proved)) Eq.refl Eq.refl

  step5 : K01 • X0 • K01 • X1 ≈ K01 • K01 • Z0 • X1
  step5 = by-assoc-and (under (K01) (X1) (sym (axiom r041))) Eq.refl Eq.refl

  step6 : K01 • K01 • Z0 • X1 ≈ Z0 • X1
  step6 = by-assoc-and (under (ε) (Z0 • X1) (axiom r025)) Eq.refl Eq.refl

  proved : X1 • Z0 ≈ Z0 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_b where

  step0 : X0 • X2 ≈ X0 • SWAP12 • X1 • SWAP12
  step0 = by-assoc-and (under (X0) (ε) (symmetry_X_c.proved)) Eq.refl Eq.refl

  step1 : X0 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • X0 • X1 • SWAP12
  step1 = by-assoc-and (under (ε) (X1 • SWAP12) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • X0 • X1 • SWAP12 ≈ SWAP12 • X1 • X0 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (X0X1.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • X1 • X0 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • X0
  step3 = by-assoc-and (under (SWAP12 • X1) (ε) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • X1 • SWAP12 • X0 ≈ X2 • X0
  step4 = by-assoc-and (under (ε) (X0) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

  proved : X0 • X2 ≈ X2 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_Z_f where

  step0 : X2 • Z0 ≈ X2 • K01 • K01 • Z0
  step0 = by-assoc-and (under (X2) (Z0) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : X2 • K01 • K01 • Z0 ≈ X2 • K01 • X0 • K01
  step1 = by-assoc-and (under (X2 • K01) (ε) (axiom r041)) Eq.refl Eq.refl

  step2 : X2 • K01 • X0 • K01 ≈ K01 • X2 • X0 • K01
  step2 = by-assoc-and (under (ε) (X0 • K01) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

  step3 : K01 • X2 • X0 • K01 ≈ K01 • X0 • X2 • K01
  step3 = by-assoc-and (under (K01) (K01) (sym (bifunct_X_b.proved))) Eq.refl Eq.refl

  step4 : K01 • X0 • X2 • K01 ≈ K01 • X0 • K01 • X2
  step4 = by-assoc-and (under (K01 • X0) (ε) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

  step5 : K01 • X0 • K01 • X2 ≈ K01 • K01 • Z0 • X2
  step5 = by-assoc-and (under (K01) (X2) (sym (axiom r041))) Eq.refl Eq.refl

  step6 : K01 • K01 • Z0 • X2 ≈ Z0 • X2
  step6 = by-assoc-and (under (ε) (Z0 • X2) (axiom r025)) Eq.refl Eq.refl

  proved : X2 • Z0 ≈ Z0 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_Z_c where

  step0 : X2 • Z1 ≈ X2 • SWAP01 • Z0 • SWAP01
  step0 = by-assoc-and (under (X2) (ε) (axiom r034)) Eq.refl Eq.refl

  step1 : X2 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • X2 • Z0 • SWAP01
  step1 = by-assoc-and (under (ε) (Z0 • SWAP01) (bifunct_X_SWAP_b.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • X2 • Z0 • SWAP01 ≈ SWAP01 • Z0 • X2 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_X_Z_f.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • X2 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • X2
  step3 = by-assoc-and (under (SWAP01 • Z0) (ε) (bifunct_X_SWAP_b.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • Z0 • SWAP01 • X2 ≈ Z1 • X2
  step4 = by-assoc-and (under (ε) (X2) (sym (axiom r034))) Eq.refl Eq.refl

  proved : X2 • Z1 ≈ Z1 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_Z1 where

  step0 : Z1 • Z1 ≈ Z1 • SWAP01 • Z0 • SWAP01
  step0 = by-assoc-and (under (Z1) (ε) (axiom r034)) Eq.refl Eq.refl

  step1 : Z1 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • Z0 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • Z0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • Z0 • Z0 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (Z0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • Z0 • SWAP01 ≈ SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (elim_Z0.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : Z1 • Z1 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel65 where

  step0 : K12 • X1 ≈ K12 • X1 • K12 • K12
  step0 = by-assoc-and (under (K12 • X1) (ε) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • X1 • K12 • K12 ≈ K12 • X1 • K12 • Z1 • Z1 • K12
  step1 = by-assoc-and (under (K12 • X1 • K12) (K12) (sym (elim_Z1.proved))) Eq.refl Eq.refl

  step2 : K12 • X1 • K12 • Z1 • Z1 • K12 ≈ K12 • X1 • X1 • K12 • Z1 • K12
  step2 = by-assoc-and (under (K12 • X1) (Z1 • K12) (sym (drel137.proved))) Eq.refl Eq.refl

  step3 : K12 • X1 • X1 • K12 • Z1 • K12 ≈ K12 • K12 • Z1 • K12
  step3 = by-assoc-and (under (K12) (K12 • Z1 • K12) (elim_X1.proved)) Eq.refl Eq.refl

  step4 : K12 • K12 • Z1 • K12 ≈ Z1 • K12
  step4 = by-assoc-and (under (ε) (Z1 • K12) (axiom r023)) Eq.refl Eq.refl

  proved : K12 • X1 ≈ Z1 • K12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_Z_d where

  step0 : X1 • Z2 ≈ K12 • K12 • X1 • Z2
  step0 = by-assoc-and (under (ε) (X1 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • X1 • Z2 ≈ K12 • Z1 • K12 • Z2
  step1 = by-assoc-and (under (K12) (Z2) (drel65.proved)) Eq.refl Eq.refl

  step2 : K12 • Z1 • K12 • Z2 ≈ K12 • Z1 • X2 • K12
  step2 = by-assoc-and (under (K12 • Z1) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

  step3 : K12 • Z1 • X2 • K12 ≈ K12 • X2 • Z1 • K12
  step3 = by-assoc-and (under (K12) (K12) (sym (bifunct_X_Z_c.proved))) Eq.refl Eq.refl

  step4 : K12 • X2 • Z1 • K12 ≈ Z2 • K12 • Z1 • K12
  step4 = by-assoc-and (under (ε) (Z1 • K12) (drel66.proved)) Eq.refl Eq.refl

  step5 : Z2 • K12 • Z1 • K12 ≈ Z2 • X1 • K12 • K12
  step5 = by-assoc-and (under (Z2) (K12) (sym (drel137.proved))) Eq.refl Eq.refl

  step6 : Z2 • X1 • K12 • K12 ≈ Z2 • X1
  step6 = by-assoc-and (under (Z2 • X1) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : X1 • Z2 ≈ Z2 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_Z_e where

  step0 : X0 • Z2 ≈ X0 • SWAP02 • Z0 • SWAP02
  step0 = by-assoc-and (under (X0) (ε) (axiom r016)) Eq.refl Eq.refl

  step1 : X0 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • SWAP02 • X0 • SWAP02 • Z0 • SWAP02
  step1 = by-assoc-and (under (ε) (X0 • SWAP02 • Z0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP02 • X0 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • X2 • Z0 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (Z0 • SWAP02) (sym (axiom r015))) Eq.refl Eq.refl

  step3 : SWAP02 • X2 • Z0 • SWAP02 ≈ SWAP02 • Z0 • X2 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (bifunct_X_Z_f.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • Z0 • X2 • SWAP02 ≈ SWAP02 • Z0 • SWAP02 • X0 • SWAP02 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • Z0) (SWAP02) (axiom r015)) Eq.refl Eq.refl

  step5 : SWAP02 • Z0 • SWAP02 • X0 • SWAP02 • SWAP02 ≈ Z2 • X0 • SWAP02 • SWAP02
  step5 = by-assoc-and (under (ε) (X0 • SWAP02 • SWAP02) (sym (axiom r016))) Eq.refl Eq.refl

  step6 : Z2 • X0 • SWAP02 • SWAP02 ≈ Z2 • X0
  step6 = by-assoc-and (under (Z2 • X0) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : X0 • Z2 ≈ Z2 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_c where

  step0 : X1 • X2 ≈ CX01 • X0 • CX01 • X0 • X2
  step0 = by-assoc-and (under (ε) (X2) (axiom r002)) Eq.refl Eq.refl

  step1 : CX01 • X0 • CX01 • X0 • X2 ≈ CX01 • X0 • CX01 • X2 • X0
  step1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (bifunct_X_b.proved)) Eq.refl Eq.refl

  step2 : CX01 • X0 • CX01 • X2 • X0 ≈ CX01 • X0 • X2 • CX01 • X0
  step2 = by-assoc-and (under (CX01 • X0) (X0) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

  step3 : CX01 • X0 • X2 • CX01 • X0 ≈ CX01 • X2 • X0 • CX01 • X0
  step3 = by-assoc-and (under (CX01) (CX01 • X0) (bifunct_X_b.proved)) Eq.refl Eq.refl

  step4 : CX01 • X2 • X0 • CX01 • X0 ≈ X2 • CX01 • X0 • CX01 • X0
  step4 = by-assoc-and (under (ε) (X0 • CX01 • X0) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

  step5 : X2 • CX01 • X0 • CX01 • X0 ≈ X2 • X1
  step5 = by-assoc-and (under (X2) (ε) (sym (axiom r002))) Eq.refl Eq.refl

  proved : X1 • X2 ≈ X2 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module bifunct_Z_K_a where

  step0 : Z0 • K12 ≈ K01 • K01 • Z0 • K12
  step0 = by-assoc-and (under (ε) (Z0 • K12) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z0 • K12 ≈ K01 • X0 • K01 • K12
  step1 = by-assoc-and (under (K01) (K12) (axiom r041)) Eq.refl Eq.refl

  step2 : K01 • X0 • K01 • K12 ≈ K01 • X0 • K12 • K01
  step2 = by-assoc-and (under (K01 • X0) (ε) (axiom r039)) Eq.refl Eq.refl

  step3 : K01 • X0 • K12 • K01 ≈ K01 • K12 • X0 • K01
  step3 = by-assoc-and (under (K01) (K01) (axiom r027)) Eq.refl Eq.refl

  step4 : K01 • K12 • X0 • K01 ≈ K12 • K01 • X0 • K01
  step4 = by-assoc-and (under (ε) (X0 • K01) (axiom r039)) Eq.refl Eq.refl

  step5 : K12 • K01 • X0 • K01 ≈ K12 • K01 • K01 • Z0
  step5 = by-assoc-and (under (K12 • K01) (ε) (sym (axiom r041))) Eq.refl Eq.refl

  step6 : K12 • K01 • K01 • Z0 ≈ K12 • Z0
  step6 = by-assoc-and (under (K12) (Z0) (axiom r025)) Eq.refl Eq.refl

  proved : Z0 • K12 ≈ K12 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_CX_d where

  step0 : Z0 • CX21 ≈ Z0 • K12 • K12 • CX21
  step0 = by-assoc-and (under (Z0) (CX21) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : Z0 • K12 • K12 • CX21 ≈ Z0 • K12 • CX12 • K12
  step1 = by-assoc-and (under (Z0 • K12) (ε) (drel46.proved)) Eq.refl Eq.refl

  step2 : Z0 • K12 • CX12 • K12 ≈ K12 • Z0 • CX12 • K12
  step2 = by-assoc-and (under (ε) (CX12 • K12) (bifunct_Z_K_a.proved)) Eq.refl Eq.refl

  step3 : K12 • Z0 • CX12 • K12 ≈ K12 • CX12 • Z0 • K12
  step3 = by-assoc-and (under (K12) (K12) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

  step4 : K12 • CX12 • Z0 • K12 ≈ K12 • CX12 • K12 • Z0
  step4 = by-assoc-and (under (K12 • CX12) (ε) (bifunct_Z_K_a.proved)) Eq.refl Eq.refl

  step5 : K12 • CX12 • K12 • Z0 ≈ K12 • K12 • CX21 • Z0
  step5 = by-assoc-and (under (K12) (Z0) (sym (drel46.proved))) Eq.refl Eq.refl

  step6 : K12 • K12 • CX21 • Z0 ≈ CX21 • Z0
  step6 = by-assoc-and (under (ε) (CX21 • Z0) (axiom r023)) Eq.refl Eq.refl

  proved : Z0 • CX21 ≈ CX21 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_CX_a where

  step0 : Z1 • CX20 ≈ SWAP01 • Z0 • SWAP01 • CX20
  step0 = by-assoc-and (under (ε) (CX20) (axiom r034)) Eq.refl Eq.refl

  step1 : SWAP01 • Z0 • SWAP01 • CX20 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • CX21 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01) (ε) (symmetry_CX_h.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • CX21 • SWAP01 ≈ SWAP01 • Z0 • CX21 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (CX21 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • CX21 • SWAP01 ≈ SWAP01 • CX21 • Z0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_Z_CX_d.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX21 • Z0 • SWAP01 ≈ SWAP01 • CX21 • SWAP01 • SWAP01 • Z0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CX21) (Z0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CX21 • SWAP01 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • CX21 • SWAP01 • Z1
  step5 = by-assoc-and (under (SWAP01 • CX21 • SWAP01) (ε) (sym (axiom r034))) Eq.refl Eq.refl

  step6 : SWAP01 • CX21 • SWAP01 • Z1 ≈ CX20 • Z1
  step6 = by-assoc-and (under (ε) (Z1) (sym (symmetry_CX_h.proved))) Eq.refl Eq.refl

  proved : Z1 • CX20 ≈ CX20 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_CX_c where

  step0 : Z1 • CX02 ≈ SWAP01 • Z0 • SWAP01 • CX02
  step0 = by-assoc-and (under (ε) (CX02) (axiom r034)) Eq.refl Eq.refl

  step1 : SWAP01 • Z0 • SWAP01 • CX02 ≈ SWAP01 • Z0 • SWAP01 • CX02 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01 • CX02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • CX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • CX12 • SWAP01 ≈ SWAP01 • CX12 • Z0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX12 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • Z0 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (Z0 • SWAP01) (axiom r030)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CX02 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • Z1
  step5 = by-assoc-and (under (SWAP01 • SWAP01 • CX02) (ε) (sym (axiom r034))) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP01 • CX02 • Z1 ≈ CX02 • Z1
  step6 = by-assoc-and (under (ε) (CX02 • Z1) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : Z1 • CX02 ≈ CX02 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_Z_CX_f where

  step0 : Z2 • CX10 ≈ Z2 • K01 • CX01 • K01
  step0 = by-assoc-and (under (Z2) (ε) (axiom r012)) Eq.refl Eq.refl

  step1 : Z2 • K01 • CX01 • K01 ≈ K01 • Z2 • CX01 • K01
  step1 = by-assoc-and (under (ε) (CX01 • K01) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

  step2 : K01 • Z2 • CX01 • K01 ≈ K01 • CX01 • Z2 • K01
  step2 = by-assoc-and (under (K01) (K01) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

  step3 : K01 • CX01 • Z2 • K01 ≈ K01 • CX01 • K01 • Z2
  step3 = by-assoc-and (under (K01 • CX01) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

  step4 : K01 • CX01 • K01 • Z2 ≈ CX10 • Z2
  step4 = by-assoc-and (under (ε) (Z2) (sym (axiom r012))) Eq.refl Eq.refl

  proved : Z2 • CX10 ≈ CX10 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
