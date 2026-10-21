{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B007 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r001 ; r002 ; r004 ; r009 ; r012 ; r014 ; r015 ; r018 ; r019 ; r023 ; r024 ; r025 ; r028 ; r029 ; r032 ; r033 ; r034 ; r036 ; r037 ; r041 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_b ; module drel128 ; module drel46 ; module elim_CX02 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module symmetry_CX_e ; module symmetry_CX_h ; module symmetry_CX_i)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module bifunct_Z_K_b ; module drel110 ; module drel41 ; module drel64 ; module drel9 ; module elim_CZ01 ; module elim_CZ02 ; module elim_CZ12 ; module elim_Z0 ; module symmetry_CX_j)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_Z_K_a ; module drel137 ; module drel65 ; module symmetry_X_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module bifunct_Z_SWAP_c ; module drel30 ; module drel47 ; module symmetry_CCX_c ; module symmetry_CCX_g)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module drel63 ; module elim_CCX2)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B005 using (module drel29 ; module drel49 ; module drel50 ; module drel85 ; module drel86)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B006 using (module drel150 ; module drel170 ; module drel172 ; module drel21 ; module drel78 ; module drel82)

module drel183 where

  step0 : CX21 • CX20 ≈ CX21 • SWAP02 • CX02 • SWAP02
  step0 = by-assoc-and (under (CX21) (ε) (axiom r029)) Eq.refl Eq.refl

  step1 : CX21 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX01 • SWAP02 • SWAP02 • CX02 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CX02 • SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step2 : SWAP02 • CX01 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX01 • CX02 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • CX01) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • CX01 • CX02 • SWAP02 ≈ SWAP02 • CX02 • CX01 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel9.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CX02 • CX01 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CX02) (CX01 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • CX21
  step5 = by-assoc-and (under (SWAP02 • CX02 • SWAP02) (ε) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

  step6 : SWAP02 • CX02 • SWAP02 • CX21 ≈ CX20 • CX21
  step6 = by-assoc-and (under (ε) (CX21) (sym (axiom r029))) Eq.refl Eq.refl

  proved : CX21 • CX20 ≈ CX20 • CX21
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel184 where

  step0 : CX21 • CX01 • CX02 ≈ CX02 • CX02 • CX21 • CX01 • CX02
  step0 = by-assoc-and (under (ε) (CX21 • CX01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step1 : CX02 • CX02 • CX21 • CX01 • CX02 ≈ CX02 • CX21 • CX02 • CX02
  step1 = by-assoc-and (under (CX02) (CX02) (sym (drel110.proved))) Eq.refl Eq.refl

  step2 : CX02 • CX21 • CX02 • CX02 ≈ CX02 • CX21
  step2 = by-assoc-and (under (CX02 • CX21) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : CX21 • CX01 • CX02 ≈ CX02 • CX21
  proved = trans step0 (trans step1 (trans step2 (refl)))

module drel186 where

  step0 : CZ12 • CZ01 • CX02 ≈ CX02 • CX02 • CZ12 • CZ01 • CX02
  step0 = by-assoc-and (under (ε) (CZ12 • CZ01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step1 : CX02 • CX02 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CZ12 • CX02 • CZ12 • CZ01 • CX02
  step1 = by-assoc-and (under (CX02) (CX02 • CZ12 • CZ01 • CX02) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

  step2 : CX02 • CZ12 • CZ12 • CX02 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CZ01 • CZ12 • CZ12 • CZ01 • CX02
  step2 = by-assoc-and (under (CX02 • CZ12) (CZ12 • CZ01 • CX02) (drel172.proved)) Eq.refl Eq.refl

  step3 : CX02 • CZ12 • CX02 • CZ01 • CZ12 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CZ01 • CZ01 • CX02
  step3 = by-assoc-and (under (CX02 • CZ12 • CX02 • CZ01) (CZ01 • CX02) (elim_CZ12.proved)) Eq.refl Eq.refl

  step4 : CX02 • CZ12 • CX02 • CZ01 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CX02
  step4 = by-assoc-and (under (CX02 • CZ12 • CX02) (CX02) (elim_CZ01.proved)) Eq.refl Eq.refl

  step5 : CX02 • CZ12 • CX02 • CX02 ≈ CX02 • CZ12
  step5 = by-assoc-and (under (CX02 • CZ12) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : CZ12 • CZ01 • CX02 ≈ CX02 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel187 where

  step0 : CZ12 • CZ01 • CCX01 ≈ CCX01 • CCX01 • CZ12 • CZ01 • CCX01
  step0 = by-assoc-and (under (ε) (CZ12 • CZ01 • CCX01) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

  step1 : CCX01 • CCX01 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CZ12 • CCX01 • CZ12 • CZ01 • CCX01
  step1 = by-assoc-and (under (CCX01) (CCX01 • CZ12 • CZ01 • CCX01) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

  step2 : CCX01 • CZ12 • CZ12 • CCX01 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CZ01 • CZ12 • CZ12 • CZ01 • CCX01
  step2 = by-assoc-and (under (CCX01 • CZ12) (CZ12 • CZ01 • CCX01) (drel170.proved)) Eq.refl Eq.refl

  step3 : CCX01 • CZ12 • CCX01 • CZ01 • CZ12 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CZ01 • CZ01 • CCX01
  step3 = by-assoc-and (under (CCX01 • CZ12 • CCX01 • CZ01) (CZ01 • CCX01) (elim_CZ12.proved)) Eq.refl Eq.refl

  step4 : CCX01 • CZ12 • CCX01 • CZ01 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CCX01
  step4 = by-assoc-and (under (CCX01 • CZ12 • CCX01) (CCX01) (elim_CZ01.proved)) Eq.refl Eq.refl

  step5 : CCX01 • CZ12 • CCX01 • CCX01 ≈ CCX01 • CZ12
  step5 = by-assoc-and (under (CCX01 • CZ12) (ε) (elim_CCX2.proved)) Eq.refl Eq.refl

  proved : CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel23 where

  step0 : Z0 • CCX12 ≈ Z0 • CCX12 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (Z0 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : Z0 • CCX12 • SWAP01 • SWAP01 ≈ Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (Z0) (CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step2 = by-assoc-and (under (ε) (Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP01 • Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z1 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01 • CCX12 • SWAP01 • SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

  step4 : SWAP01 • Z1 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z1 • CCX02 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • Z1) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step5 : SWAP01 • Z1 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CZ02 • Z1 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (SWAP01) (drel21.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CCX02 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • Z1 • SWAP01
  step6 = by-assoc-and (under (SWAP01) (CZ02 • Z1 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • Z1 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • Z1 • SWAP01
  step7 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CZ02 • Z1 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : CCX12 • SWAP01 • CZ02 • Z1 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01
  step8 = by-assoc-and (under (CCX12 • SWAP01 • CZ02) (SWAP01) (axiom r034)) Eq.refl Eq.refl

  step9 : CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • SWAP01 • Z0
  step9 = by-assoc-and (under (CCX12 • SWAP01 • CZ02 • SWAP01 • Z0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step10 : CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 ≈ CCX12 • CZ12 • Z0
  step10 = by-assoc-and (under (CCX12) (Z0) (sym (axiom r019))) Eq.refl Eq.refl

  proved : Z0 • CCX12 ≈ CCX12 • CZ12 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module drel24 where

  step0 : CCX12 • Z0 ≈ CCX12 • Z0 • CCX12 • CCX12
  step0 = by-assoc-and (under (CCX12 • Z0) (ε) (sym (axiom r024))) Eq.refl Eq.refl

  step1 : CCX12 • Z0 • CCX12 • CCX12 ≈ CCX12 • Z0 • CCX12 • CZ12 • CZ12 • CCX12
  step1 = by-assoc-and (under (CCX12 • Z0 • CCX12) (CCX12) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

  step2 : CCX12 • Z0 • CCX12 • CZ12 • CZ12 • CCX12 ≈ CCX12 • Z0 • CCX12 • CZ12 • Z0 • Z0 • CZ12 • CCX12
  step2 = by-assoc-and (under (CCX12 • Z0 • CCX12 • CZ12) (CZ12 • CCX12) (sym (elim_Z0.proved))) Eq.refl Eq.refl

  step3 : CCX12 • Z0 • CCX12 • CZ12 • Z0 • Z0 • CZ12 • CCX12 ≈ CCX12 • Z0 • Z0 • CCX12 • Z0 • CZ12 • CCX12
  step3 = by-assoc-and (under (CCX12 • Z0) (Z0 • CZ12 • CCX12) (sym (drel23.proved))) Eq.refl Eq.refl

  step4 : CCX12 • Z0 • Z0 • CCX12 • Z0 • CZ12 • CCX12 ≈ CCX12 • CCX12 • Z0 • CZ12 • CCX12
  step4 = by-assoc-and (under (CCX12) (CCX12 • Z0 • CZ12 • CCX12) (elim_Z0.proved)) Eq.refl Eq.refl

  step5 : CCX12 • CCX12 • Z0 • CZ12 • CCX12 ≈ Z0 • CZ12 • CCX12
  step5 = by-assoc-and (under (ε) (Z0 • CZ12 • CCX12) (axiom r024)) Eq.refl Eq.refl

  proved : CCX12 • Z0 ≈ Z0 • CZ12 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel25 where

  step0 : X1 • CCX02 ≈ X1 • SWAP01 • CCX12 • SWAP01
  step0 = by-assoc-and (under (X1) (ε) (axiom r014)) Eq.refl Eq.refl

  step1 : X1 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CCX12 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (axiom r028)) Eq.refl Eq.refl

  step2 : SWAP01 • X0 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • X0 • CCX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • X0) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • X0 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • X0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r037)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX12 • X0 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • X0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX12) (X0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CCX12 • SWAP01 • SWAP01 • X0 • SWAP01 ≈ CCX02 • SWAP01 • X0 • SWAP01
  step5 = by-assoc-and (under (ε) (SWAP01 • X0 • SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step6 : CCX02 • SWAP01 • X0 • SWAP01 ≈ CCX02 • X1
  step6 = by-assoc-and (under (CCX02) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  proved : X1 • CCX02 ≈ CCX02 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel26 where

  step0 : X2 • CCX01 ≈ X2 • SWAP02 • CCX12 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (axiom r032)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CCX12 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CCX12 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X0 • CCX12 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (CCX12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r037)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX12 • X0 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • SWAP02 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CCX12) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CCX12 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ CCX01 • SWAP02 • X0 • SWAP02
  step5 = by-assoc-and (under (ε) (SWAP02 • X0 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

  step6 : CCX01 • SWAP02 • X0 • SWAP02 ≈ CCX01 • X2
  step6 = by-assoc-and (under (CCX01) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  proved : X2 • CCX01 ≈ CCX01 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel92 where

  step0 : CCX02 • CX01 ≈ CCX02 • SWAP01 • CX10 • SWAP01
  step0 = by-assoc-and (under (CCX02) (ε) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step1 : CCX02 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CX10 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step2 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CCX12) (CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CCX12 • CX10 • SWAP01 ≈ SWAP01 • CX10 • CCX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r036)) Eq.refl Eq.refl

  step4 : SWAP01 • CX10 • CCX12 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • SWAP01 • CCX12 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CX10) (CCX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CX10 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • CCX02
  step5 = by-assoc-and (under (SWAP01 • CX10 • SWAP01) (ε) (sym (axiom r014))) Eq.refl Eq.refl

  step6 : SWAP01 • CX10 • SWAP01 • CCX02 ≈ CX01 • CCX02
  step6 = by-assoc-and (under (ε) (CCX02) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  proved : CCX02 • CX01 ≈ CX01 • CCX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel36 where

  step0 : CZ01 • CCX01 ≈ K12 • CX01 • K12 • CCX01
  step0 = by-assoc-and (under (ε) (CCX01) (axiom r001)) Eq.refl Eq.refl

  step1 : K12 • CX01 • K12 • CCX01 ≈ K12 • CX01 • CCX02 • K12
  step1 = by-assoc-and (under (K12 • CX01) (ε) (drel128.proved)) Eq.refl Eq.refl

  step2 : K12 • CX01 • CCX02 • K12 ≈ K12 • CCX02 • CX01 • K12
  step2 = by-assoc-and (under (K12) (K12) (sym (drel92.proved))) Eq.refl Eq.refl

  step3 : K12 • CCX02 • CX01 • K12 ≈ CCX01 • K12 • CX01 • K12
  step3 = by-assoc-and (under (ε) (CX01 • K12) (sym (drel29.proved))) Eq.refl Eq.refl

  step4 : CCX01 • K12 • CX01 • K12 ≈ CCX01 • CZ01
  step4 = by-assoc-and (under (CCX01) (ε) (sym (axiom r001))) Eq.refl Eq.refl

  proved : CZ01 • CCX01 ≈ CCX01 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel37 where

  step0 : CZ02 • CCX02 ≈ SWAP12 • CZ01 • SWAP12 • CCX02
  step0 = by-assoc-and (under (ε) (CCX02) (axiom r018)) Eq.refl Eq.refl

  step1 : SWAP12 • CZ01 • SWAP12 • CCX02 ≈ SWAP12 • CZ01 • SWAP12 • CCX02 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12 • CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CZ01 • CCX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • CCX01 • SWAP12 ≈ SWAP12 • CCX01 • CZ01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel36.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX01 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (axiom r033)) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • CZ02
  step5 = by-assoc-and (under (SWAP12 • SWAP12 • CCX02) (ε) (sym (axiom r018))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP12 • CCX02 • CZ02 ≈ CCX02 • CZ02
  step6 = by-assoc-and (under (ε) (CCX02 • CZ02) (elim_SWAP12.proved)) Eq.refl Eq.refl

  proved : CZ02 • CCX02 ≈ CCX02 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel38 where

  step0 : CZ12 • CCX12 ≈ CZ12 • CCX12 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CZ12 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CZ12 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • CCX02 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step3 : SWAP01 • CZ02 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CZ02 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel37.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX02 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CZ12
  step5 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (ε) (sym (axiom r019))) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP01 • CCX12 • CZ12 ≈ CCX12 • CZ12
  step6 = by-assoc-and (under (ε) (CCX12 • CZ12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CZ12 • CCX12 ≈ CCX12 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel51 where

  step0 : Z1 • CCX01 ≈ K12 • X1 • K12 • CCX01
  step0 = by-assoc-and (under (ε) (CCX01) (axiom r004)) Eq.refl Eq.refl

  step1 : K12 • X1 • K12 • CCX01 ≈ K12 • X1 • CCX02 • K12
  step1 = by-assoc-and (under (K12 • X1) (ε) (drel86.proved)) Eq.refl Eq.refl

  step2 : K12 • X1 • CCX02 • K12 ≈ K12 • CCX02 • X1 • K12
  step2 = by-assoc-and (under (K12) (K12) (drel25.proved)) Eq.refl Eq.refl

  step3 : K12 • CCX02 • X1 • K12 ≈ CCX01 • K12 • X1 • K12
  step3 = by-assoc-and (under (ε) (X1 • K12) (sym (drel29.proved))) Eq.refl Eq.refl

  step4 : CCX01 • K12 • X1 • K12 ≈ CCX01 • Z1
  step4 = by-assoc-and (under (CCX01) (ε) (sym (axiom r004))) Eq.refl Eq.refl

  proved : Z1 • CCX01 ≈ CCX01 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel40 where

  step0 : Z0 • CCX01 ≈ Z0 • SWAP01 • CCX01 • SWAP01
  step0 = by-assoc-and (under (Z0) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step1 : Z0 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CCX01 • SWAP01
  step1 = by-assoc-and (under (ε) (Z0 • SWAP01 • CCX01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • Z0 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • Z1 • CCX01 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (CCX01 • SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

  step3 : SWAP01 • Z1 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • Z1 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel51.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX01 • Z1 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • Z0 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX01) (SWAP01) (axiom r034)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX01 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • Z0
  step5 = by-assoc-and (under (SWAP01 • CCX01 • SWAP01 • Z0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CCX01 • SWAP01 • Z0 ≈ CCX01 • Z0
  step6 = by-assoc-and (under (ε) (Z0) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

  proved : Z0 • CCX01 ≈ CCX01 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel43 where

  step0 : CZ01 • Z0 ≈ K12 • K12 • CZ01 • Z0
  step0 = by-assoc-and (under (ε) (CZ01 • Z0) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ01 • Z0 ≈ K12 • CX01 • K12 • Z0
  step1 = by-assoc-and (under (K12) (Z0) (drel49.proved)) Eq.refl Eq.refl

  step2 : K12 • CX01 • K12 • Z0 ≈ K12 • CX01 • Z0 • K12
  step2 = by-assoc-and (under (K12 • CX01) (ε) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

  step3 : K12 • CX01 • Z0 • K12 ≈ K12 • Z0 • CX01 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel78.proved)) Eq.refl Eq.refl

  step4 : K12 • Z0 • CX01 • K12 ≈ Z0 • K12 • CX01 • K12
  step4 = by-assoc-and (under (ε) (CX01 • K12) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

  step5 : Z0 • K12 • CX01 • K12 ≈ Z0 • CZ01 • K12 • K12
  step5 = by-assoc-and (under (Z0) (K12) (sym (drel50.proved))) Eq.refl Eq.refl

  step6 : Z0 • CZ01 • K12 • K12 ≈ Z0 • CZ01
  step6 = by-assoc-and (under (Z0 • CZ01) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CZ01 • Z0 ≈ Z0 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel45 where

  step0 : CZ01 • Z1 ≈ K12 • K12 • CZ01 • Z1
  step0 = by-assoc-and (under (ε) (CZ01 • Z1) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ01 • Z1 ≈ K12 • CX01 • K12 • Z1
  step1 = by-assoc-and (under (K12) (Z1) (drel49.proved)) Eq.refl Eq.refl

  step2 : K12 • CX01 • K12 • Z1 ≈ K12 • CX01 • X1 • K12
  step2 = by-assoc-and (under (K12 • CX01) (ε) (sym (drel137.proved))) Eq.refl Eq.refl

  step3 : K12 • CX01 • X1 • K12 ≈ K12 • X1 • CX01 • K12
  step3 = by-assoc-and (under (K12) (K12) (sym (drel82.proved))) Eq.refl Eq.refl

  step4 : K12 • X1 • CX01 • K12 ≈ Z1 • K12 • CX01 • K12
  step4 = by-assoc-and (under (ε) (CX01 • K12) (drel65.proved)) Eq.refl Eq.refl

  step5 : Z1 • K12 • CX01 • K12 ≈ Z1 • CZ01 • K12 • K12
  step5 = by-assoc-and (under (Z1) (K12) (sym (drel50.proved))) Eq.refl Eq.refl

  step6 : Z1 • CZ01 • K12 • K12 ≈ Z1 • CZ01
  step6 = by-assoc-and (under (Z1 • CZ01) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CZ01 • Z1 ≈ Z1 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel52 where

  step0 : Z0 • CCX02 ≈ K01 • K01 • Z0 • CCX02
  step0 = by-assoc-and (under (ε) (Z0 • CCX02) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z0 • CCX02 ≈ K01 • X0 • K01 • CCX02
  step1 = by-assoc-and (under (K01) (CCX02) (axiom r041)) Eq.refl Eq.refl

  step2 : K01 • X0 • K01 • CCX02 ≈ K01 • X0 • CCX12 • K01
  step2 = by-assoc-and (under (K01 • X0) (ε) (sym (drel85.proved))) Eq.refl Eq.refl

  step3 : K01 • X0 • CCX12 • K01 ≈ K01 • CCX12 • X0 • K01
  step3 = by-assoc-and (under (K01) (K01) (axiom r037)) Eq.refl Eq.refl

  step4 : K01 • CCX12 • X0 • K01 ≈ K01 • CCX12 • K01 • Z0
  step4 = by-assoc-and (under (K01 • CCX12) (ε) (sym (axiom r041))) Eq.refl Eq.refl

  step5 : K01 • CCX12 • K01 • Z0 ≈ K01 • K01 • CCX02 • Z0
  step5 = by-assoc-and (under (K01) (Z0) (drel85.proved)) Eq.refl Eq.refl

  step6 : K01 • K01 • CCX02 • Z0 ≈ CCX02 • Z0
  step6 = by-assoc-and (under (ε) (CCX02 • Z0) (axiom r025)) Eq.refl Eq.refl

  proved : Z0 • CCX02 ≈ CCX02 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel53 where

  step0 : Z1 • CCX12 ≈ Z1 • CCX12 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (Z1 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : Z1 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step2 : SWAP01 • Z0 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • CCX02 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • Z0) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step3 : SWAP01 • Z0 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • Z0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel52.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX02 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • Z0 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (Z0 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • Z1
  step5 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (ε) (sym (axiom r034))) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP01 • CCX12 • Z1 ≈ CCX12 • Z1
  step6 = by-assoc-and (under (ε) (CCX12 • Z1) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : Z1 • CCX12 ≈ CCX12 • Z1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel54 where

  step0 : Z2 • CCX12 ≈ K01 • K01 • Z2 • CCX12
  step0 = by-assoc-and (under (ε) (Z2 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z2 • CCX12 ≈ K01 • Z2 • K01 • CCX12
  step1 = by-assoc-and (under (K01) (CCX12) (sym (bifunct_Z_K_b.proved))) Eq.refl Eq.refl

  step2 : K01 • Z2 • K01 • CCX12 ≈ K01 • Z2 • CCX02 • K01
  step2 = by-assoc-and (under (K01 • Z2) (ε) (drel63.proved)) Eq.refl Eq.refl

  step3 : K01 • Z2 • CCX02 • K01 ≈ K01 • K12 • K12 • Z2 • CCX02 • K01
  step3 = by-assoc-and (under (K01) (Z2 • CCX02 • K01) (sym (axiom r023))) Eq.refl Eq.refl

  step4 : K01 • K12 • K12 • Z2 • CCX02 • K01 ≈ K01 • K12 • X2 • K12 • CCX02 • K01
  step4 = by-assoc-and (under (K01 • K12) (CCX02 • K01) (sym (drel64.proved))) Eq.refl Eq.refl

  step5 : K01 • K12 • X2 • K12 • CCX02 • K01 ≈ K01 • K12 • X2 • CCX01 • K12 • K01
  step5 = by-assoc-and (under (K01 • K12 • X2) (K01) (sym (drel29.proved))) Eq.refl Eq.refl

  step6 : K01 • K12 • X2 • CCX01 • K12 • K01 ≈ K01 • K12 • CCX01 • X2 • K12 • K01
  step6 = by-assoc-and (under (K01 • K12) (K12 • K01) (drel26.proved)) Eq.refl Eq.refl

  step7 : K01 • K12 • CCX01 • X2 • K12 • K01 ≈ K01 • K12 • CCX01 • K12 • Z2 • K01
  step7 = by-assoc-and (under (K01 • K12 • CCX01) (K01) (drel64.proved)) Eq.refl Eq.refl

  step8 : K01 • K12 • CCX01 • K12 • Z2 • K01 ≈ K01 • K12 • K12 • CCX02 • Z2 • K01
  step8 = by-assoc-and (under (K01 • K12) (Z2 • K01) (drel29.proved)) Eq.refl Eq.refl

  step9 : K01 • K12 • K12 • CCX02 • Z2 • K01 ≈ K01 • CCX02 • Z2 • K01
  step9 = by-assoc-and (under (K01) (CCX02 • Z2 • K01) (axiom r023)) Eq.refl Eq.refl

  step10 : K01 • CCX02 • Z2 • K01 ≈ K01 • CCX02 • K01 • Z2
  step10 = by-assoc-and (under (K01 • CCX02) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

  step11 : K01 • CCX02 • K01 • Z2 ≈ K01 • K01 • CCX12 • Z2
  step11 = by-assoc-and (under (K01) (Z2) (sym (drel63.proved))) Eq.refl Eq.refl

  step12 : K01 • K01 • CCX12 • Z2 ≈ CCX12 • Z2
  step12 = by-assoc-and (under (ε) (CCX12 • Z2) (axiom r025)) Eq.refl Eq.refl

  proved : Z2 • CCX12 ≈ CCX12 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))

module drel94 where

  step0 : CCX12 • CX20 ≈ CCX12 • SWAP12 • CX10 • SWAP12
  step0 = by-assoc-and (under (CCX12) (ε) (symmetry_CX_j.proved)) Eq.refl Eq.refl

  step1 : CCX12 • SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CX10 • SWAP12) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CCX12) (CX10 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CCX12 • CX10 • SWAP12 ≈ SWAP12 • CX10 • CCX12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r036)) Eq.refl Eq.refl

  step4 : SWAP12 • CX10 • CCX12 • SWAP12 ≈ SWAP12 • CX10 • SWAP12 • SWAP12 • CCX12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CX10) (CCX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CX10 • SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CX10 • SWAP12 • CCX12
  step5 = by-assoc-and (under (SWAP12 • CX10 • SWAP12) (ε) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CX10 • SWAP12 • CCX12 ≈ CX20 • CCX12
  step6 = by-assoc-and (under (ε) (CCX12) (sym (symmetry_CX_j.proved))) Eq.refl Eq.refl

  proved : CCX12 • CX20 ≈ CX20 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel93 where

  step0 : CCX02 • CX21 ≈ CCX02 • CX21 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CCX02 • CX21) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CCX02 • CX21 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CX21 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CX21 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step2 : SWAP01 • CCX12 • SWAP01 • CX21 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CCX12) (SWAP01) (sym (symmetry_CX_h.proved))) Eq.refl Eq.refl

  step3 : SWAP01 • CCX12 • CX20 • SWAP01 ≈ SWAP01 • CX20 • CCX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel94.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX20 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX21 • SWAP01 • CCX12 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (symmetry_CX_h.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CX21 • SWAP01 • CCX12 • SWAP01 ≈ CX21 • SWAP01 • CCX12 • SWAP01
  step5 = by-assoc-and (under (ε) (CX21 • SWAP01 • CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : CX21 • SWAP01 • CCX12 • SWAP01 ≈ CX21 • CCX02
  step6 = by-assoc-and (under (CX21) (ε) (sym (axiom r014))) Eq.refl Eq.refl

  proved : CCX02 • CX21 ≈ CX21 • CCX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel55 where

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

module drel56 where

  step0 : CCX12 • CX10 ≈ K01 • K01 • CCX12 • CX10
  step0 = by-assoc-and (under (ε) (CCX12 • CX10) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • CCX12 • CX10 ≈ K01 • CCX02 • K01 • CX10
  step1 = by-assoc-and (under (K01) (CX10) (drel63.proved)) Eq.refl Eq.refl

  step2 : K01 • CCX02 • K01 • CX10 ≈ K01 • CCX02 • K01 • K01 • CX01 • K01
  step2 = by-assoc-and (under (K01 • CCX02 • K01) (ε) (axiom r012)) Eq.refl Eq.refl

  step3 : K01 • CCX02 • K01 • K01 • CX01 • K01 ≈ K01 • CCX02 • CX01 • K01
  step3 = by-assoc-and (under (K01 • CCX02) (CX01 • K01) (axiom r025)) Eq.refl Eq.refl

  step4 : K01 • CCX02 • CX01 • K01 ≈ K01 • CX01 • CCX02 • K01
  step4 = by-assoc-and (under (K01) (K01) (drel92.proved)) Eq.refl Eq.refl

  step5 : K01 • CX01 • CCX02 • K01 ≈ K01 • CX01 • K01 • CCX12
  step5 = by-assoc-and (under (K01 • CX01) (ε) (sym (drel63.proved))) Eq.refl Eq.refl

  step6 : K01 • CX01 • K01 • CCX12 ≈ CX10 • CCX12
  step6 = by-assoc-and (under (ε) (CCX12) (sym (axiom r012))) Eq.refl Eq.refl

  proved : CCX12 • CX10 ≈ CX10 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel57 where

  step0 : CCX12 • CZ02 ≈ CCX12 • CZ02 • CCX12 • CCX12
  step0 = by-assoc-and (under (CCX12 • CZ02) (ε) (sym (axiom r024))) Eq.refl Eq.refl

  step1 : CCX12 • CZ02 • CCX12 • CCX12 ≈ CCX12 • CZ02 • CCX12 • CZ12 • CZ12 • CCX12
  step1 = by-assoc-and (under (CCX12 • CZ02 • CCX12) (CCX12) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

  step2 : CCX12 • CZ02 • CCX12 • CZ12 • CZ12 • CCX12 ≈ CCX12 • CZ02 • CCX12 • CZ12 • CZ02 • CZ02 • CZ12 • CCX12
  step2 = by-assoc-and (under (CCX12 • CZ02 • CCX12 • CZ12) (CZ12 • CCX12) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step3 : CCX12 • CZ02 • CCX12 • CZ12 • CZ02 • CZ02 • CZ12 • CCX12 ≈ CCX12 • CZ02 • CZ02 • CCX12 • CZ02 • CZ12 • CCX12
  step3 = by-assoc-and (under (CCX12 • CZ02) (CZ02 • CZ12 • CCX12) (sym (drel150.proved))) Eq.refl Eq.refl

  step4 : CCX12 • CZ02 • CZ02 • CCX12 • CZ02 • CZ12 • CCX12 ≈ CCX12 • CCX12 • CZ02 • CZ12 • CCX12
  step4 = by-assoc-and (under (CCX12) (CCX12 • CZ02 • CZ12 • CCX12) (elim_CZ02.proved)) Eq.refl Eq.refl

  step5 : CCX12 • CCX12 • CZ02 • CZ12 • CCX12 ≈ CZ02 • CZ12 • CCX12
  step5 = by-assoc-and (under (ε) (CZ02 • CZ12 • CCX12) (axiom r024)) Eq.refl Eq.refl

  proved : CCX12 • CZ02 ≈ CZ02 • CZ12 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel61 where

  step0 : CX02 • X2 ≈ CX02 • SWAP12 • X1 • SWAP12
  step0 = by-assoc-and (under (CX02) (ε) (symmetry_X_c.proved)) Eq.refl Eq.refl

  step1 : CX02 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • X1 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • CX01 • X1 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX01) (X1 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • X1 • SWAP12 ≈ SWAP12 • X1 • CX01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (sym (drel82.proved))) Eq.refl Eq.refl

  step4 : SWAP12 • X1 • CX01 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • SWAP12 • CX01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • X1) (CX01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • X1 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • CX02
  step5 = by-assoc-and (under (SWAP12 • X1 • SWAP12) (ε) (sym (axiom r009))) Eq.refl Eq.refl

  step6 : SWAP12 • X1 • SWAP12 • CX02 ≈ X2 • CX02
  step6 = by-assoc-and (under (ε) (CX02) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

  proved : CX02 • X2 ≈ X2 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel62 where

  step0 : CZ02 • Z2 ≈ K12 • K12 • CZ02 • Z2
  step0 = by-assoc-and (under (ε) (CZ02 • Z2) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ02 • Z2 ≈ K12 • CX02 • K12 • Z2
  step1 = by-assoc-and (under (K12) (Z2) (drel47.proved)) Eq.refl Eq.refl

  step2 : K12 • CX02 • K12 • Z2 ≈ K12 • CX02 • X2 • K12
  step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

  step3 : K12 • CX02 • X2 • K12 ≈ K12 • X2 • CX02 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel61.proved)) Eq.refl Eq.refl

  step4 : K12 • X2 • CX02 • K12 ≈ K12 • X2 • K12 • CZ02
  step4 = by-assoc-and (under (K12 • X2) (ε) (sym (drel47.proved))) Eq.refl Eq.refl

  step5 : K12 • X2 • K12 • CZ02 ≈ K12 • K12 • Z2 • CZ02
  step5 = by-assoc-and (under (K12) (CZ02) (drel64.proved)) Eq.refl Eq.refl

  step6 : K12 • K12 • Z2 • CZ02 ≈ Z2 • CZ02
  step6 = by-assoc-and (under (ε) (Z2 • CZ02) (axiom r023)) Eq.refl Eq.refl

  proved : CZ02 • Z2 ≈ Z2 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel60 where

  step0 : CZ12 • Z2 ≈ SWAP01 • CZ02 • SWAP01 • Z2
  step0 = by-assoc-and (under (ε) (Z2) (axiom r019)) Eq.refl Eq.refl

  step1 : SWAP01 • CZ02 • SWAP01 • Z2 ≈ SWAP01 • CZ02 • Z2 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • CZ02) (ε) (sym (bifunct_Z_SWAP_c.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • Z2 • SWAP01 ≈ SWAP01 • Z2 • CZ02 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (SWAP01) (drel62.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • Z2 • CZ02 • SWAP01 ≈ Z2 • SWAP01 • CZ02 • SWAP01
  step3 = by-assoc-and (under (ε) (CZ02 • SWAP01) (sym (bifunct_Z_SWAP_c.proved))) Eq.refl Eq.refl

  step4 : Z2 • SWAP01 • CZ02 • SWAP01 ≈ Z2 • CZ12
  step4 = by-assoc-and (under (Z2) (ε) (sym (axiom r019))) Eq.refl Eq.refl

  proved : CZ12 • Z2 ≈ Z2 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel79 where

  step0 : X1 • CX21 ≈ CX01 • X0 • CX01 • X0 • CX21
  step0 = by-assoc-and (under (ε) (CX21) (axiom r002)) Eq.refl Eq.refl

  step1 : CX01 • X0 • CX01 • X0 • CX21 ≈ CX01 • X0 • CX01 • CX21 • X0
  step1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

  step2 : CX01 • X0 • CX01 • CX21 • X0 ≈ CX01 • X0 • CX21 • CX01 • X0
  step2 = by-assoc-and (under (CX01 • X0) (X0) (drel41.proved)) Eq.refl Eq.refl

  step3 : CX01 • X0 • CX21 • CX01 • X0 ≈ CX01 • CX21 • X0 • CX01 • X0
  step3 = by-assoc-and (under (CX01) (CX01 • X0) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

  step4 : CX01 • CX21 • X0 • CX01 • X0 ≈ CX21 • CX01 • X0 • CX01 • X0
  step4 = by-assoc-and (under (ε) (X0 • CX01 • X0) (drel41.proved)) Eq.refl Eq.refl

  step5 : CX21 • CX01 • X0 • CX01 • X0 ≈ CX21 • X1
  step5 = by-assoc-and (under (CX21) (ε) (sym (axiom r002))) Eq.refl Eq.refl

  proved : X1 • CX21 ≈ CX21 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
