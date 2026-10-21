{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B006 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r009 ; r010 ; r012 ; r014 ; r016 ; r018 ; r019 ; r023 ; r028 ; r029 ; r030 ; r031 ; r033 ; r034 ; r038 ; r043 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module drel46 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module symmetry_CX_e ; module symmetry_CX_f ; module symmetry_CX_g)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel165 ; module drel64 ; module drel66 ; module elim_Z0 ; module elim_Z2 ; module symmetry_CX_b ; module symmetry_CZ_b ; module symmetry_CZ_e)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_c ; module bifunct_Z_CX_a ; module bifunct_Z_CX_c ; module bifunct_Z_K_a ; module drel133 ; module drel137 ; module drel58 ; module drel65)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module bifunct_Z_SWAP_a ; module bifunct_Z_c ; module drel155 ; module drel30 ; module drel47 ; module drel59 ; module drel96 ; module symmetry_CCX_c ; module symmetry_CCX_g)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module drel108 ; module drel109 ; module drel168)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B005 using (module drel151 ; module drel159 ; module drel29 ; module drel71 ; module symmetry_CZ_d ; module symmetry_Z_c)

module drel138 where

  step0 : CX20 • CZ01 ≈ SWAP02 • CX02 • SWAP02 • CZ01
  step0 = by-assoc-and (under (ε) (CZ01) (axiom r029)) Eq.refl Eq.refl

  step1 : SWAP02 • CX02 • SWAP02 • CZ01 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01
  step1 = by-assoc-and (under (SWAP02) (SWAP02 • CZ01) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP12 • SWAP12 • SWAP02
  step3 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02) (SWAP02) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step4 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • CZ12 • SWAP12 • SWAP12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12) (SWAP12 • SWAP12 • SWAP02) (sym (symmetry_CZ_d.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • SWAP12 • CX01 • SWAP12 • CZ12 • SWAP12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP02
  step5 = by-assoc-and (under (SWAP02 • SWAP12 • CX01) (SWAP12 • SWAP02) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

  step6 : SWAP02 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP02
  step6 = by-assoc-and (under (SWAP02 • SWAP12) (SWAP12 • SWAP02) (axiom r043)) Eq.refl Eq.refl

  step7 : SWAP02 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP02
  step7 = by-assoc-and (under (SWAP02 • SWAP12 • CZ12) (CX01 • SWAP12 • SWAP02) (axiom r018)) Eq.refl Eq.refl

  step8 : SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP02
  step8 = by-assoc-and (under (SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01) (SWAP02) (sym (axiom r009))) Eq.refl Eq.refl

  step9 : SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • CX02 • SWAP02
  step9 = by-assoc-and (under (SWAP02) (CZ01 • CX02 • SWAP02) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

  step10 : SWAP02 • CZ12 • CZ01 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • SWAP02 • SWAP02 • CX02 • SWAP02
  step10 = by-assoc-and (under (SWAP02 • CZ12 • CZ01) (CX02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step11 : SWAP02 • CZ12 • CZ01 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • SWAP02 • CX20
  step11 = by-assoc-and (under (SWAP02 • CZ12 • CZ01 • SWAP02) (ε) (sym (axiom r029))) Eq.refl Eq.refl

  step12 : SWAP02 • CZ12 • CZ01 • SWAP02 • CX20 ≈ SWAP02 • SWAP02 • CZ01 • SWAP02 • CZ01 • SWAP02 • CX20
  step12 = by-assoc-and (under (SWAP02) (CZ01 • SWAP02 • CX20) (symmetry_CZ_d.proved)) Eq.refl Eq.refl

  step13 : SWAP02 • SWAP02 • CZ01 • SWAP02 • CZ01 • SWAP02 • CX20 ≈ CZ01 • SWAP02 • CZ01 • SWAP02 • CX20
  step13 = by-assoc-and (under (ε) (CZ01 • SWAP02 • CZ01 • SWAP02 • CX20) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step14 : CZ01 • SWAP02 • CZ01 • SWAP02 • CX20 ≈ CZ01 • CZ12 • CX20
  step14 = by-assoc-and (under (CZ01) (CX20) (sym (symmetry_CZ_d.proved))) Eq.refl Eq.refl

  proved : CX20 • CZ01 ≈ CZ01 • CZ12 • CX20
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (refl)))))))))))))))

module drel140 where

  step0 : CX20 • CCX02 ≈ CX20 • SWAP01 • CCX12 • SWAP01
  step0 = by-assoc-and (under (CX20) (ε) (axiom r014)) Eq.refl Eq.refl

  step1 : CX20 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX20 • SWAP01 • CCX12 • SWAP01
  step1 = by-assoc-and (under (ε) (CX20 • SWAP01 • CCX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CX20 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CX21 • CCX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

  step3 : SWAP01 • CX21 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • CX21 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel155.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX12 • CX20 • CX21 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01 • CX20 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX12 • CX20) (SWAP01) (axiom r031)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX12 • CX20 • SWAP01 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01 • CX20
  step5 = by-assoc-and (under (SWAP01 • CCX12 • CX20 • SWAP01 • CX20) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CCX12 • CX20 • SWAP01 • CX20 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX20
  step6 = by-assoc-and (under (SWAP01 • CCX12) (CX20 • SWAP01 • CX20) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step7 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX20 ≈ SWAP01 • CCX12 • SWAP01 • CX21 • CX20
  step7 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01) (CX20) (sym (axiom r031))) Eq.refl Eq.refl

  step8 : SWAP01 • CCX12 • SWAP01 • CX21 • CX20 ≈ CCX02 • CX21 • CX20
  step8 = by-assoc-and (under (ε) (CX21 • CX20) (sym (axiom r014))) Eq.refl Eq.refl

  proved : CX20 • CCX02 ≈ CCX02 • CX21 • CX20
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel150 where

  step0 : CZ02 • CCX12 ≈ CZ02 • SWAP12 • CCX12 • SWAP12
  step0 = by-assoc-and (under (CZ02) (ε) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

  step1 : CZ02 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX12 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CCX12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CZ01 • CCX12 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01) (CCX12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • CZ12 • CZ01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel159.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX12 • CZ12 • CZ01 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CCX12) (CZ01 • SWAP12) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

  step5 : SWAP12 • CCX12 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CZ12 • CZ02
  step5 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12 • CZ12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

  step6 : SWAP12 • CCX12 • SWAP12 • CZ12 • CZ02 ≈ CCX12 • CZ12 • CZ02
  step6 = by-assoc-and (under (ε) (CZ12 • CZ02) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  proved : CZ02 • CCX12 ≈ CCX12 • CZ12 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel157 where

  step0 : CZ01 • Z1 • CX10 ≈ CZ01 • SWAP01 • Z0 • SWAP01 • CX10
  step0 = by-assoc-and (under (CZ01) (CX10) (axiom r034)) Eq.refl Eq.refl

  step1 : CZ01 • SWAP01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • SWAP01 • SWAP01 • Z0 • SWAP01 • CX10
  step1 = by-assoc-and (under (ε) (SWAP01 • Z0 • SWAP01 • CX10) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ01 • SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • Z0 • SWAP01 • CX10
  step2 = by-assoc-and (under (SWAP01 • CZ01) (Z0 • SWAP01 • CX10) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CZ01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • Z0 • SWAP01 • CX10 • SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01 • CZ01 • Z0 • SWAP01 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • CZ01 • Z0 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • CZ01 • Z0 • CX01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CZ01 • Z0) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CZ01 • Z0 • CX01 • SWAP01 ≈ SWAP01 • CX01 • CZ01 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (SWAP01) (sym (drel168.proved))) Eq.refl Eq.refl

  step6 : SWAP01 • CX01 • CZ01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CZ01 • SWAP01
  step6 = by-assoc-and (under (SWAP01) (CZ01 • SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • CX10 • SWAP01 • CZ01 • SWAP01 ≈ CX10 • SWAP01 • CZ01 • SWAP01
  step7 = by-assoc-and (under (ε) (CX10 • SWAP01 • CZ01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : CX10 • SWAP01 • CZ01 • SWAP01 ≈ CX10 • CZ01
  step8 = by-assoc-and (under (CX10) (ε) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

  proved : CZ01 • Z1 • CX10 ≈ CX10 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel173 where

  step0 : CZ02 • Z0 • CX02 ≈ CZ02 • Z0 • SWAP12 • CX01 • SWAP12
  step0 = by-assoc-and (under (CZ02 • Z0) (ε) (axiom r009)) Eq.refl Eq.refl

  step1 : CZ02 • Z0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • Z0 • SWAP12 • CX01 • SWAP12
  step1 = by-assoc-and (under (ε) (Z0 • SWAP12 • CX01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • Z0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • Z0 • CX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12) (CX01 • SWAP12) (bifunct_Z_SWAP_a.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • SWAP12 • SWAP12 • Z0 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • Z0 • CX01 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • CZ01) (Z0 • CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ01 • Z0 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CZ01 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (SWAP12) (sym (drel168.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CX01 • CZ01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CZ01 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • CX01) (CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CX01 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ02
  step6 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

  step7 : SWAP12 • CX01 • SWAP12 • CZ02 ≈ CX02 • CZ02
  step7 = by-assoc-and (under (ε) (CZ02) (sym (axiom r009))) Eq.refl Eq.refl

  proved : CZ02 • Z0 • CX02 ≈ CX02 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel158 where

  step0 : CZ12 • Z1 • CX12 ≈ CZ12 • Z1 • SWAP01 • CX02 • SWAP01
  step0 = by-assoc-and (under (CZ12 • Z1) (ε) (axiom r030)) Eq.refl Eq.refl

  step1 : CZ12 • Z1 • SWAP01 • CX02 • SWAP01 ≈ CZ12 • SWAP01 • Z0 • SWAP01 • SWAP01 • CX02 • SWAP01
  step1 = by-assoc-and (under (CZ12) (SWAP01 • CX02 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step2 : CZ12 • SWAP01 • Z0 • SWAP01 • SWAP01 • CX02 • SWAP01 ≈ CZ12 • SWAP01 • Z0 • CX02 • SWAP01
  step2 = by-assoc-and (under (CZ12 • SWAP01 • Z0) (CX02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : CZ12 • SWAP01 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • CX02 • SWAP01
  step3 = by-assoc-and (under (ε) (SWAP01 • Z0 • CX02 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step4 : SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CZ02 • Z0 • CX02 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CZ02) (Z0 • CX02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • CZ02 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CX02 • CZ02 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (SWAP01) (drel173.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CX02 • CZ02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • SWAP01 • CZ02 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • CX02) (CZ02 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step7 : SWAP01 • CX02 • SWAP01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • CZ12
  step7 = by-assoc-and (under (SWAP01 • CX02 • SWAP01) (ε) (sym (axiom r019))) Eq.refl Eq.refl

  step8 : SWAP01 • CX02 • SWAP01 • CZ12 ≈ CX12 • CZ12
  step8 = by-assoc-and (under (ε) (CZ12) (sym (axiom r030))) Eq.refl Eq.refl

  proved : CZ12 • Z1 • CX12 ≈ CX12 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel170 where

  step0 : CZ12 • CCX01 ≈ CZ12 • SWAP01 • CCX01 • SWAP01
  step0 = by-assoc-and (under (CZ12) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step1 : CZ12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • CCX01 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CCX01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CZ02 • CCX01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ02) (CCX01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CZ02 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • CZ01 • CZ02 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel151.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX01 • CZ01 • CZ02 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CZ01 • SWAP01 • CZ02 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX01) (CZ02 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX01 • SWAP01 • CZ01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CZ01 • CZ12
  step5 = by-assoc-and (under (SWAP01 • CCX01 • SWAP01 • CZ01) (ε) (sym (axiom r019))) Eq.refl Eq.refl

  step6 : SWAP01 • CCX01 • SWAP01 • CZ01 • CZ12 ≈ CCX01 • CZ01 • CZ12
  step6 = by-assoc-and (under (ε) (CZ01 • CZ12) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

  proved : CZ12 • CCX01 ≈ CCX01 • CZ01 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel19 where

  step0 : Z2 • CX12 ≈ K12 • K12 • Z2 • CX12
  step0 = by-assoc-and (under (ε) (Z2 • CX12) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • Z2 • CX12 ≈ K12 • X2 • K12 • CX12
  step1 = by-assoc-and (under (K12) (CX12) (sym (drel64.proved))) Eq.refl Eq.refl

  step2 : K12 • X2 • K12 • CX12 ≈ K12 • X2 • CX21 • K12
  step2 = by-assoc-and (under (K12 • X2) (ε) (sym (drel30.proved))) Eq.refl Eq.refl

  step3 : K12 • X2 • CX21 • K12 ≈ K12 • CX21 • X1 • X2 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel133.proved)) Eq.refl Eq.refl

  step4 : K12 • CX21 • X1 • X2 • K12 ≈ K12 • CX21 • X2 • X1 • K12
  step4 = by-assoc-and (under (K12 • CX21) (K12) (bifunct_X_c.proved)) Eq.refl Eq.refl

  step5 : K12 • CX21 • X2 • X1 • K12 ≈ CX12 • K12 • X2 • X1 • K12
  step5 = by-assoc-and (under (ε) (X2 • X1 • K12) (drel46.proved)) Eq.refl Eq.refl

  step6 : CX12 • K12 • X2 • X1 • K12 ≈ CX12 • Z2 • K12 • X1 • K12
  step6 = by-assoc-and (under (CX12) (X1 • K12) (drel66.proved)) Eq.refl Eq.refl

  step7 : CX12 • Z2 • K12 • X1 • K12 ≈ CX12 • Z2 • Z1 • K12 • K12
  step7 = by-assoc-and (under (CX12 • Z2) (K12) (drel65.proved)) Eq.refl Eq.refl

  step8 : CX12 • Z2 • Z1 • K12 • K12 ≈ CX12 • Z2 • Z1
  step8 = by-assoc-and (under (CX12 • Z2 • Z1) (ε) (axiom r023)) Eq.refl Eq.refl

  step9 : CX12 • Z2 • Z1 ≈ CX12 • Z1 • Z2
  step9 = by-assoc-and (under (CX12) (ε) (sym (bifunct_Z_c.proved))) Eq.refl Eq.refl

  proved : Z2 • CX12 ≈ CX12 • Z1 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))

module symmetry_Z_a where

  step0 : Z1 ≈ SWAP02 • SWAP02 • Z1
  step0 = by-assoc-and (under (ε) (Z1) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step1 : SWAP02 • SWAP02 • Z1 ≈ SWAP02 • CX02 • CX20 • CX02 • Z1
  step1 = by-assoc-and (under (SWAP02) (Z1) (axiom r010)) Eq.refl Eq.refl

  step2 : SWAP02 • CX02 • CX20 • CX02 • Z1 ≈ SWAP02 • CX02 • CX20 • Z1 • CX02
  step2 = by-assoc-and (under (SWAP02 • CX02 • CX20) (ε) (sym (bifunct_Z_CX_c.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • CX02 • CX20 • Z1 • CX02 ≈ SWAP02 • CX02 • Z1 • CX20 • CX02
  step3 = by-assoc-and (under (SWAP02 • CX02) (CX02) (sym (bifunct_Z_CX_a.proved))) Eq.refl Eq.refl

  step4 : SWAP02 • CX02 • Z1 • CX20 • CX02 ≈ SWAP02 • Z1 • CX02 • CX20 • CX02
  step4 = by-assoc-and (under (SWAP02) (CX20 • CX02) (sym (bifunct_Z_CX_c.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • Z1 • CX02 • CX20 • CX02 ≈ SWAP02 • Z1 • SWAP02
  step5 = by-assoc-and (under (SWAP02 • Z1) (ε) (sym (axiom r010))) Eq.refl Eq.refl

  proved : Z1 ≈ SWAP02 • Z1 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_Z_b where

  step0 : Z0 ≈ Z0 • SWAP02 • SWAP02
  step0 = by-assoc-and (under (Z0) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step1 : Z0 • SWAP02 • SWAP02 ≈ Z0 • SWAP02 • Z2 • Z2 • SWAP02
  step1 = by-assoc-and (under (Z0 • SWAP02) (SWAP02) (sym (elim_Z2.proved))) Eq.refl Eq.refl

  step2 : Z0 • SWAP02 • Z2 • Z2 • SWAP02 ≈ Z0 • SWAP02 • Z2 • SWAP02 • SWAP02 • Z2 • SWAP02
  step2 = by-assoc-and (under (Z0 • SWAP02 • Z2) (Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step3 : Z0 • SWAP02 • Z2 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ Z0 • SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
  step3 = by-assoc-and (under (Z0 • SWAP02) (SWAP02 • SWAP02 • Z2 • SWAP02) (axiom r016)) Eq.refl Eq.refl

  step4 : Z0 • SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ Z0 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
  step4 = by-assoc-and (under (Z0) (Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step5 : Z0 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
  step5 = by-assoc-and (under (ε) (SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02) (elim_Z0.proved)) Eq.refl Eq.refl

  step6 : SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • Z2 • SWAP02
  step6 = by-assoc-and (under (ε) (SWAP02 • Z2 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : Z0 ≈ SWAP02 • Z2 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel42 where

  step0 : Z0 • CX10 ≈ Z0 • CX10 • SWAP02 • SWAP02
  step0 = by-assoc-and (under (Z0 • CX10) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step1 : Z0 • CX10 • SWAP02 • SWAP02 ≈ Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (Z0) (CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
  step2 = by-assoc-and (under (ε) (Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • Z2 • SWAP02 • CX10 • SWAP02 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02 • CX10 • SWAP02 • SWAP02) (sym (axiom r016))) Eq.refl Eq.refl

  step4 : SWAP02 • Z2 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • Z2 • CX12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • Z2) (SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • Z2 • CX12 • SWAP02 ≈ SWAP02 • CX12 • Z1 • Z2 • SWAP02
  step5 = by-assoc-and (under (SWAP02) (SWAP02) (drel19.proved)) Eq.refl Eq.refl

  step6 : SWAP02 • CX12 • Z1 • Z2 • SWAP02 ≈ SWAP02 • CX12 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02
  step6 = by-assoc-and (under (SWAP02 • CX12 • Z1) (Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step7 : SWAP02 • CX12 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • SWAP02 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02
  step7 = by-assoc-and (under (SWAP02 • CX12) (Z1 • SWAP02 • SWAP02 • Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step8 : SWAP02 • CX12 • SWAP02 • SWAP02 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • Z1 • SWAP02 • Z2 • SWAP02
  step8 = by-assoc-and (under (SWAP02 • CX12 • SWAP02) (SWAP02 • Z2 • SWAP02) (sym (symmetry_Z_a.proved))) Eq.refl Eq.refl

  step9 : SWAP02 • CX12 • SWAP02 • Z1 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • Z1 • Z0
  step9 = by-assoc-and (under (SWAP02 • CX12 • SWAP02 • Z1) (ε) (sym (symmetry_Z_b.proved))) Eq.refl Eq.refl

  step10 : SWAP02 • CX12 • SWAP02 • Z1 • Z0 ≈ CX10 • Z1 • Z0
  step10 = by-assoc-and (under (ε) (Z1 • Z0) (sym (symmetry_CX_b.proved))) Eq.refl Eq.refl

  proved : Z0 • CX10 ≈ CX10 • Z1 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module drel171 where

  step0 : Z1 • CX01 ≈ Z1 • SWAP01 • CX10 • SWAP01
  step0 = by-assoc-and (under (Z1) (ε) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step1 : Z1 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • CX10 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CX10 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • Z0 • CX10 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • CX10 • SWAP01 ≈ SWAP01 • CX10 • Z1 • Z0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel42.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX10 • Z1 • Z0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • Z0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CX10) (Z0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step5 : SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • Z1
  step5 = by-assoc-and (under (SWAP01 • CX10 • SWAP01 • Z0) (ε) (sym (axiom r034))) Eq.refl Eq.refl

  step6 : SWAP01 • CX10 • SWAP01 • Z0 • Z1 ≈ CX01 • Z0 • Z1
  step6 = by-assoc-and (under (ε) (Z0 • Z1) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  proved : Z1 • CX01 ≈ CX01 • Z0 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel172 where

  step0 : CZ12 • CX02 ≈ CZ12 • SWAP12 • CX01 • SWAP12
  step0 = by-assoc-and (under (CZ12) (ε) (axiom r009)) Eq.refl Eq.refl

  step1 : CZ12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ12 • SWAP12 • SWAP12 • CX01 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ12 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ12 • CX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ12) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CZ02 • CZ12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel109.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CX01 • CZ02 • CZ12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • CZ12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CX01) (CZ12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step5 : SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • CZ12
  step5 = by-assoc-and (under (SWAP12 • CX01 • SWAP12 • CZ01) (ε) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CX01 • SWAP12 • CZ01 • CZ12 ≈ CX02 • CZ01 • CZ12
  step6 = by-assoc-and (under (ε) (CZ01 • CZ12) (sym (axiom r009))) Eq.refl Eq.refl

  proved : CZ12 • CX02 ≈ CX02 • CZ01 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel175 where

  step0 : CZ01 • CX21 ≈ CZ01 • SWAP12 • CX12 • SWAP12
  step0 = by-assoc-and (under (CZ01) (ε) (symmetry_CX_g.proved)) Eq.refl Eq.refl

  step1 : CZ01 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • SWAP12 • CX12 • SWAP12
  step1 = by-assoc-and (under (ε) (CZ01 • SWAP12 • CX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • CZ01 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CZ02 • CX12 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (CX12 • SWAP12) (sym (axiom r018))) Eq.refl Eq.refl

  step3 : SWAP12 • CZ02 • CX12 • SWAP12 ≈ SWAP12 • CX12 • CZ01 • CZ02 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel108.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CX12 • CZ01 • CZ02 • SWAP12 ≈ SWAP12 • CX12 • CZ02 • CZ01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CX12) (SWAP12) (drel71.proved)) Eq.refl Eq.refl

  step5 : SWAP12 • CX12 • CZ02 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12 • CZ01 • SWAP12 • CZ01 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • CX12) (CZ01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step6 : SWAP12 • CX12 • SWAP12 • CZ01 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12 • CZ01 • CZ02
  step6 = by-assoc-and (under (SWAP12 • CX12 • SWAP12 • CZ01) (ε) (sym (axiom r018))) Eq.refl Eq.refl

  step7 : SWAP12 • CX12 • SWAP12 • CZ01 • CZ02 ≈ CX21 • CZ01 • CZ02
  step7 = by-assoc-and (under (ε) (CZ01 • CZ02) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

  proved : CZ01 • CX21 ≈ CX21 • CZ01 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel176 where

  step0 : CX21 • CZ02 ≈ CX21 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (CX21) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : CX21 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12 • SWAP12 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (symmetry_CX_g.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • CX12 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • CZ01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX12) (CZ01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CX12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • CX12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel165.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ01 • CX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CX12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CZ01) (CX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX21
  step5 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12) (ε) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CZ01 • SWAP12 • CX21 ≈ CZ02 • CX21
  step6 = by-assoc-and (under (ε) (CX21) (sym (axiom r018))) Eq.refl Eq.refl

  proved : CX21 • CZ02 ≈ CZ02 • CX21
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel82 where

  step0 : X1 • CX01 ≈ X1 • SWAP01 • CX10 • SWAP01
  step0 = by-assoc-and (under (X1) (ε) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step1 : X1 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CX10 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CX10 • SWAP01) (axiom r028)) Eq.refl Eq.refl

  step2 : SWAP01 • X0 • SWAP01 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • X0 • CX10 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • X0) (CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • X0 • CX10 • SWAP01 ≈ SWAP01 • CX10 • X0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r038)) Eq.refl Eq.refl

  step4 : SWAP01 • CX10 • X0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CX10) (X0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • X1
  step5 = by-assoc-and (under (SWAP01 • CX10 • SWAP01) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  step6 : SWAP01 • CX10 • SWAP01 • X1 ≈ CX01 • X1
  step6 = by-assoc-and (under (ε) (X1) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  proved : X1 • CX01 ≈ CX01 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel77 where

  step0 : CX10 • Z1 ≈ K01 • CX01 • K01 • Z1
  step0 = by-assoc-and (under (ε) (Z1) (axiom r012)) Eq.refl Eq.refl

  step1 : K01 • CX01 • K01 • Z1 ≈ K01 • CX01 • X1 • K01
  step1 = by-assoc-and (under (K01 • CX01) (ε) (sym (drel59.proved))) Eq.refl Eq.refl

  step2 : K01 • CX01 • X1 • K01 ≈ K01 • X1 • CX01 • K01
  step2 = by-assoc-and (under (K01) (K01) (sym (drel82.proved))) Eq.refl Eq.refl

  step3 : K01 • X1 • CX01 • K01 ≈ Z1 • K01 • CX01 • K01
  step3 = by-assoc-and (under (ε) (CX01 • K01) (sym (drel58.proved))) Eq.refl Eq.refl

  step4 : Z1 • K01 • CX01 • K01 ≈ Z1 • CX10
  step4 = by-assoc-and (under (Z1) (ε) (sym (axiom r012))) Eq.refl Eq.refl

  proved : CX10 • Z1 ≈ Z1 • CX10
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel78 where

  step0 : CX01 • Z0 ≈ CX01 • Z0 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CX01 • Z0) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CX01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (Z0 • SWAP01 • SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CX10 • Z1 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CX10) (SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

  step3 : SWAP01 • CX10 • Z1 • SWAP01 ≈ SWAP01 • Z1 • CX10 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel77.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • Z1 • CX10 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CX10 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 • SWAP01 ≈ Z0 • SWAP01 • CX10 • SWAP01
  step5 = by-assoc-and (under (ε) (Z0 • SWAP01 • CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : Z0 • SWAP01 • CX10 • SWAP01 ≈ Z0 • CX01
  step6 = by-assoc-and (under (Z0) (ε) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  proved : CX01 • Z0 ≈ Z0 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel44 where

  step0 : CZ02 • Z0 ≈ K12 • K12 • CZ02 • Z0
  step0 = by-assoc-and (under (ε) (CZ02 • Z0) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ02 • Z0 ≈ K12 • CX02 • K12 • Z0
  step1 = by-assoc-and (under (K12) (Z0) (drel47.proved)) Eq.refl Eq.refl

  step2 : K12 • CX02 • K12 • Z0 ≈ K12 • CX02 • Z0 • K12
  step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

  step3 : K12 • CX02 • Z0 • K12 ≈ K12 • SWAP12 • CX01 • SWAP12 • Z0 • K12
  step3 = by-assoc-and (under (K12) (Z0 • K12) (axiom r009)) Eq.refl Eq.refl

  step4 : K12 • SWAP12 • CX01 • SWAP12 • Z0 • K12 ≈ K12 • SWAP12 • CX01 • Z0 • SWAP12 • K12
  step4 = by-assoc-and (under (K12 • SWAP12 • CX01) (K12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

  step5 : K12 • SWAP12 • CX01 • Z0 • SWAP12 • K12 ≈ K12 • SWAP12 • Z0 • CX01 • SWAP12 • K12
  step5 = by-assoc-and (under (K12 • SWAP12) (SWAP12 • K12) (drel78.proved)) Eq.refl Eq.refl

  step6 : K12 • SWAP12 • Z0 • CX01 • SWAP12 • K12 ≈ K12 • Z0 • SWAP12 • CX01 • SWAP12 • K12
  step6 = by-assoc-and (under (K12) (CX01 • SWAP12 • K12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

  step7 : K12 • Z0 • SWAP12 • CX01 • SWAP12 • K12 ≈ Z0 • K12 • SWAP12 • CX01 • SWAP12 • K12
  step7 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12 • K12) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

  step8 : Z0 • K12 • SWAP12 • CX01 • SWAP12 • K12 ≈ Z0 • K12 • CX02 • K12
  step8 = by-assoc-and (under (Z0 • K12) (K12) (sym (axiom r009))) Eq.refl Eq.refl

  step9 : Z0 • K12 • CX02 • K12 ≈ Z0 • K12 • K12 • CZ02
  step9 = by-assoc-and (under (Z0 • K12) (ε) (sym (drel47.proved))) Eq.refl Eq.refl

  step10 : Z0 • K12 • K12 • CZ02 ≈ Z0 • CZ02
  step10 = by-assoc-and (under (Z0) (CZ02) (axiom r023)) Eq.refl Eq.refl

  proved : CZ02 • Z0 ≈ Z0 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module drel179 where

  step0 : Z1 • CZ12 ≈ Z1 • SWAP01 • CZ02 • SWAP01
  step0 = by-assoc-and (under (Z1) (ε) (axiom r019)) Eq.refl Eq.refl

  step1 : Z1 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • CZ02 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CZ02 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • Z0 • CZ02 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (CZ02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • Z0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (sym (drel44.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • CZ02 • Z0 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CZ02) (Z0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • Z1
  step5 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01) (ε) (sym (axiom r034))) Eq.refl Eq.refl

  step6 : SWAP01 • CZ02 • SWAP01 • Z1 ≈ CZ12 • Z1
  step6 = by-assoc-and (under (ε) (Z1) (sym (axiom r019))) Eq.refl Eq.refl

  proved : Z1 • CZ12 ≈ CZ12 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel21 where

  step0 : Z1 • CCX02 ≈ K12 • K12 • Z1 • CCX02
  step0 = by-assoc-and (under (ε) (Z1 • CCX02) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • Z1 • CCX02 ≈ K12 • X1 • K12 • CCX02
  step1 = by-assoc-and (under (K12) (CCX02) (sym (drel137.proved))) Eq.refl Eq.refl

  step2 : K12 • X1 • K12 • CCX02 ≈ K12 • X1 • CCX01 • K12
  step2 = by-assoc-and (under (K12 • X1) (ε) (sym (drel29.proved))) Eq.refl Eq.refl

  step3 : K12 • X1 • CCX01 • K12 ≈ K12 • CCX01 • CX02 • X1 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel96.proved)) Eq.refl Eq.refl

  step4 : K12 • CCX01 • CX02 • X1 • K12 ≈ K12 • CCX01 • CX02 • K12 • Z1
  step4 = by-assoc-and (under (K12 • CCX01 • CX02) (ε) (drel137.proved)) Eq.refl Eq.refl

  step5 : K12 • CCX01 • CX02 • K12 • Z1 ≈ K12 • CCX01 • K12 • CZ02 • Z1
  step5 = by-assoc-and (under (K12 • CCX01) (Z1) (sym (drel47.proved))) Eq.refl Eq.refl

  step6 : K12 • CCX01 • K12 • CZ02 • Z1 ≈ K12 • K12 • CCX02 • CZ02 • Z1
  step6 = by-assoc-and (under (K12) (CZ02 • Z1) (drel29.proved)) Eq.refl Eq.refl

  step7 : K12 • K12 • CCX02 • CZ02 • Z1 ≈ CCX02 • CZ02 • Z1
  step7 = by-assoc-and (under (ε) (CCX02 • CZ02 • Z1) (axiom r023)) Eq.refl Eq.refl

  proved : Z1 • CCX02 ≈ CCX02 • CZ02 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel182 where

  step0 : Z2 • CCX01 ≈ Z2 • SWAP12 • CCX02 • SWAP12
  step0 = by-assoc-and (under (Z2) (ε) (axiom r033)) Eq.refl Eq.refl

  step1 : Z2 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • Z1 • SWAP12 • SWAP12 • CCX02 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CCX02 • SWAP12) (symmetry_Z_c.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • Z1 • SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • Z1 • CCX02 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • Z1) (CCX02 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • Z1 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • Z1 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel21.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX02 • CZ02 • Z1 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • SWAP12 • SWAP12 • Z1 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CCX02 • CZ02) (Z1 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CCX02 • CZ02 • SWAP12 • SWAP12 • Z1 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • SWAP12 • Z2
  step5 = by-assoc-and (under (SWAP12 • CCX02 • CZ02 • SWAP12) (ε) (sym (symmetry_Z_c.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CCX02 • CZ02 • SWAP12 • Z2 ≈ SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 • SWAP12 • Z2
  step6 = by-assoc-and (under (SWAP12 • CCX02) (SWAP12 • Z2) (axiom r018)) Eq.refl Eq.refl

  step7 : SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 • SWAP12 • Z2 ≈ SWAP12 • CCX02 • SWAP12 • CZ01 • Z2
  step7 = by-assoc-and (under (SWAP12 • CCX02 • SWAP12 • CZ01) (Z2) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step8 : SWAP12 • CCX02 • SWAP12 • CZ01 • Z2 ≈ CCX01 • CZ01 • Z2
  step8 = by-assoc-and (under (ε) (CZ01 • Z2) (sym (axiom r033))) Eq.refl Eq.refl

  proved : Z2 • CCX01 ≈ CCX01 • CZ01 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
