{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B004 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r003 ; r007 ; r009 ; r011 ; r012 ; r014 ; r015 ; r017 ; r018 ; r019 ; r021 ; r022 ; r024 ; r025 ; r030 ; r031 ; r032 ; r033 ; r040 ; r042 ; r043 ; r046 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Proofs.B000 using (module X0X1)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_K_b ; module drel128 ; module drel162 ; module elim_CCX1 ; module elim_CX02 ; module elim_CX10 ; module elim_CX12 ; module elim_CX20 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module elim_X1 ; module symmetry_CX_e)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel134 ; module drel166 ; module elim_CZ01 ; module elim_CZ02 ; module elim_X2 ; module elim_Z0 ; module symmetry_CX_b ; module symmetry_CZ_b ; module symmetry_CZ_e)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_SWAP_a ; module symmetry_X_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module cadd3 ; module cadd7 ; module drel141 ; module symmetry_CCX_c ; module symmetry_CCX_f ; module symmetry_CCX_g)

module cadd4 where

  step0 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • SWAP01 • CX20 • SWAP01
  step0 = by-assoc-and (under (CX21 • CCX01) (ε) (axiom r031)) Eq.refl Eq.refl

  step1 : CX21 • CCX01 • SWAP01 • CX20 • SWAP01 ≈ SWAP01 • CX20 • SWAP01 • CCX01 • SWAP01 • CX20 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX01 • SWAP01 • CX20 • SWAP01) (axiom r031)) Eq.refl Eq.refl

  step2 : SWAP01 • CX20 • SWAP01 • CCX01 • SWAP01 • CX20 • SWAP01 ≈ SWAP01 • CX20 • CCX01 • CX20 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CX20) (CX20 • SWAP01) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

  step3 : SWAP01 • CX20 • CCX01 • CX20 • SWAP01 ≈ SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (cadd3.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX12) (CCX12 • SWAP01) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CCX01 • CCX02
  step5 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01 • CCX01) (ε) (sym (axiom r014))) Eq.refl Eq.refl

  step6 : SWAP01 • CCX12 • SWAP01 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02
  step6 = by-assoc-and (under (ε) (CCX01 • CCX02) (sym (axiom r014))) Eq.refl Eq.refl

  proved : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module cadd5 where

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

module cadd6 where

  step0 : CX10 • CCX02 • CX10 ≈ CX10 • CCX02 • CX10 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CX10 • CCX02 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CX10 • CCX02 • CX10 • SWAP01 • SWAP01 ≈ CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (CX10) (CX10 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step2 : CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01
  step2 = by-assoc-and (under (ε) (CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • CX01 • SWAP01
  step3 = by-assoc-and (under (SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • CX01 • SWAP01 ≈ SWAP01 • CX01 • CCX12 • CX01 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CCX12 • CX01 • SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • CX01 • CCX12 • CX01 • SWAP01 ≈ SWAP01 • CCX02 • CCX12 • CCX02 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (SWAP01) (cadd7.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • CCX02 • CCX12 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • CCX02 • CCX12) (SWAP01) (axiom r014)) Eq.refl Eq.refl

  step7 : SWAP01 • CCX02 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step7 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step8 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12
  step8 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step9 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 ≈ CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12
  step9 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step10 : CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 ≈ CCX12 • CCX02 • CCX12
  step10 = by-assoc-and (under (CCX12) (CCX12) (sym (axiom r014))) Eq.refl Eq.refl

  proved : CX10 • CCX02 • CX10 ≈ CCX12 • CCX02 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module cflip3 where

  step0 : CCX02 • CCX01 • CCX02 ≈ CCX02 • CCX02 • CCX01 • CCX02 • CCX01
  step0 = by-assoc-and (under (CCX02) (ε) (axiom r046)) Eq.refl Eq.refl

  step1 : CCX02 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01
  step1 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) (elim_CCX1.proved)) Eq.refl Eq.refl

  proved : CCX02 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX01
  proved = trans step0 (trans step1 (refl))

module cflip0 where

  step0 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
  step0 = by-assoc-and (under (ε) (ε) (cadd4.proved)) Eq.refl Eq.refl

  step1 : CCX02 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX01
  step1 = by-assoc-and (under (ε) (ε) (cflip3.proved)) Eq.refl Eq.refl

  step2 : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
  step2 = by-assoc-and (under (ε) (ε) (sym (cadd5.proved))) Eq.refl Eq.refl

  proved : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
  proved = trans step0 (trans step1 (trans step2 (refl)))

module cflip1 where

  step0 : CCX01 • CCX12 • CCX01 ≈ CCX01 • CCX12 • SWAP01 • CCX01 • SWAP01
  step0 = by-assoc-and (under (CCX01 • CCX12) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step1 : CCX01 • CCX12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CCX01 • SWAP01) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • CCX02 • CCX01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CCX01) (CCX01 • SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step3 : SWAP01 • CCX01 • CCX02 • CCX01 • SWAP01 ≈ SWAP01 • CCX02 • CCX01 • CCX02 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (sym (cflip3.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • CCX02 • CCX01 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX02 • CCX01) (SWAP01) (axiom r014)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX02 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step5 = by-assoc-and (under (SWAP01) (CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (CCX12 • SWAP01 • SWAP01) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12
  step7 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CCX12
  step8 = by-assoc-and (under (ε) (CCX12 • CCX01 • CCX12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module cflip2 where

  step0 : CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (CCX02 • CCX12 • CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : CCX02 • CCX12 • CCX02 • SWAP12 • SWAP12 ≈ CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (CCX02) (CCX02 • SWAP12 • SWAP12) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

  step2 : CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12
  step2 = by-assoc-and (under (ε) (CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step3 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01 • SWAP12 ≈ SWAP12 • CCX01 • CCX12 • CCX01 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CCX12 • CCX01 • SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

  step5 : SWAP12 • CCX01 • CCX12 • CCX01 • SWAP12 ≈ SWAP12 • CCX12 • CCX01 • CCX12 • SWAP12
  step5 = by-assoc-and (under (SWAP12) (SWAP12) (cflip1.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • CCX12 • CCX01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12
  step6 = by-assoc-and (under (SWAP12 • CCX12) (CCX12 • SWAP12) (axiom r033)) Eq.refl Eq.refl

  step7 : SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CCX02 • CCX12
  step7 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12 • CCX02) (ε) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  step8 : SWAP12 • CCX12 • SWAP12 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CCX12
  step8 = by-assoc-and (under (ε) (CCX02 • CCX12) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

  proved : CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel135 where

  step0 : CX12 • CX20 ≈ CX12 • CX20 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CX12 • CX20) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CX12 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • CX20 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CX20 • SWAP01 • SWAP01) (axiom r030)) Eq.refl Eq.refl

  step2 : SWAP01 • CX02 • SWAP01 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CX02 • CX21 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CX02) (SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

  step3 : SWAP01 • CX02 • CX21 • SWAP01 ≈ SWAP01 • CX21 • CX02 • CX01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel134.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CX21 • CX02 • CX01 • SWAP01 ≈ SWAP01 • SWAP01 • CX20 • SWAP01 • CX02 • CX01 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CX02 • CX01 • SWAP01) (axiom r031)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CX20 • SWAP01 • CX02 • CX01 • SWAP01 ≈ CX20 • SWAP01 • CX02 • CX01 • SWAP01
  step5 = by-assoc-and (under (ε) (CX20 • SWAP01 • CX02 • CX01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : CX20 • SWAP01 • CX02 • CX01 • SWAP01 ≈ CX20 • SWAP01 • CX02 • SWAP01 • CX10 • SWAP01 • SWAP01
  step6 = by-assoc-and (under (CX20 • SWAP01 • CX02) (SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step7 : CX20 • SWAP01 • CX02 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ CX20 • CX12 • CX10 • SWAP01 • SWAP01
  step7 = by-assoc-and (under (CX20) (CX10 • SWAP01 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step8 : CX20 • CX12 • CX10 • SWAP01 • SWAP01 ≈ CX20 • CX12 • CX10
  step8 = by-assoc-and (under (CX20 • CX12 • CX10) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CX12 • CX20 ≈ CX20 • CX12 • CX10
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel10 where

  step0 : CX10 • CX12 ≈ CX10 • CX12 • CX20 • CX20
  step0 = by-assoc-and (under (CX10 • CX12) (ε) (sym (elim_CX20.proved))) Eq.refl Eq.refl

  step1 : CX10 • CX12 • CX20 • CX20 ≈ CX10 • CX12 • CX20 • CX12 • CX12 • CX20
  step1 = by-assoc-and (under (CX10 • CX12 • CX20) (CX20) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step2 : CX10 • CX12 • CX20 • CX12 • CX12 • CX20 ≈ CX10 • CX12 • CX20 • CX12 • CX20 • CX20 • CX12 • CX20
  step2 = by-assoc-and (under (CX10 • CX12 • CX20 • CX12) (CX12 • CX20) (sym (elim_CX20.proved))) Eq.refl Eq.refl

  step3 : CX10 • CX12 • CX20 • CX12 • CX20 • CX20 • CX12 • CX20 ≈ CX10 • CX12 • CX20 • CX20 • CX12 • CX10 • CX20 • CX12 • CX20
  step3 = by-assoc-and (under (CX10 • CX12 • CX20) (CX20 • CX12 • CX20) (drel135.proved)) Eq.refl Eq.refl

  step4 : CX10 • CX12 • CX20 • CX20 • CX12 • CX10 • CX20 • CX12 • CX20 ≈ CX10 • CX12 • CX12 • CX10 • CX20 • CX12 • CX20
  step4 = by-assoc-and (under (CX10 • CX12) (CX12 • CX10 • CX20 • CX12 • CX20) (elim_CX20.proved)) Eq.refl Eq.refl

  step5 : CX10 • CX12 • CX12 • CX10 • CX20 • CX12 • CX20 ≈ CX10 • CX10 • CX20 • CX12 • CX20
  step5 = by-assoc-and (under (CX10) (CX10 • CX20 • CX12 • CX20) (elim_CX12.proved)) Eq.refl Eq.refl

  step6 : CX10 • CX10 • CX20 • CX12 • CX20 ≈ CX20 • CX12 • CX20
  step6 = by-assoc-and (under (ε) (CX20 • CX12 • CX20) (elim_CX10.proved)) Eq.refl Eq.refl

  step7 : CX20 • CX12 • CX20 ≈ CX20 • CX20 • CX12 • CX10
  step7 = by-assoc-and (under (CX20) (ε) (drel135.proved)) Eq.refl Eq.refl

  step8 : CX20 • CX20 • CX12 • CX10 ≈ CX12 • CX10
  step8 = by-assoc-and (under (ε) (CX12 • CX10) (elim_CX20.proved)) Eq.refl Eq.refl

  proved : CX10 • CX12 ≈ CX12 • CX10
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel130 where

  step0 : X2 • CCX12 ≈ SWAP02 • X0 • SWAP02 • CCX12
  step0 = by-assoc-and (under (ε) (CCX12) (axiom r015)) Eq.refl Eq.refl

  step1 : SWAP02 • X0 • SWAP02 • CCX12 ≈ SWAP02 • X0 • SWAP02 • CCX12 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (SWAP02 • X0 • SWAP02 • CCX12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • X0 • CCX01 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • CCX01 • SWAP02 ≈ SWAP02 • CCX01 • CX12 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r042)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX01 • CX12 • X0 • SWAP02 ≈ SWAP02 • SWAP02 • CCX12 • SWAP02 • CX12 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02) (CX12 • X0 • SWAP02) (axiom r032)) Eq.refl Eq.refl

  step5 : SWAP02 • SWAP02 • CCX12 • SWAP02 • CX12 • X0 • SWAP02 ≈ CCX12 • SWAP02 • CX12 • X0 • SWAP02
  step5 = by-assoc-and (under (ε) (CCX12 • SWAP02 • CX12 • X0 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step6 : CCX12 • SWAP02 • CX12 • X0 • SWAP02 ≈ CCX12 • SWAP02 • CX12 • SWAP02 • SWAP02 • X0 • SWAP02
  step6 = by-assoc-and (under (CCX12 • SWAP02 • CX12) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step7 : CCX12 • SWAP02 • CX12 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ CCX12 • SWAP02 • CX12 • SWAP02 • X2
  step7 = by-assoc-and (under (CCX12 • SWAP02 • CX12 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  step8 : CCX12 • SWAP02 • CX12 • SWAP02 • X2 ≈ CCX12 • CX10 • X2
  step8 = by-assoc-and (under (CCX12) (X2) (sym (symmetry_CX_b.proved))) Eq.refl Eq.refl

  proved : X2 • CCX12 ≈ CCX12 • CX10 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel63 where

  step0 : K01 • CCX12 ≈ SWAP02 • K12 • SWAP02 • CCX12
  step0 = by-assoc-and (under (ε) (CCX12) (axiom r011)) Eq.refl Eq.refl

  step1 : SWAP02 • K12 • SWAP02 • CCX12 ≈ SWAP02 • K12 • SWAP02 • CCX12 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (SWAP02 • K12 • SWAP02 • CCX12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • K12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • K12 • CCX01 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • K12) (SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

  step3 : SWAP02 • K12 • CCX01 • SWAP02 ≈ SWAP02 • CCX02 • K12 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel128.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CCX02 • K12 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02 • SWAP02 • K12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CCX02) (K12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CCX02 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02 • K01
  step5 = by-assoc-and (under (SWAP02 • CCX02 • SWAP02) (ε) (sym (axiom r011))) Eq.refl Eq.refl

  step6 : SWAP02 • CCX02 • SWAP02 • K01 ≈ CCX02 • K01
  step6 = by-assoc-and (under (ε) (K01) (sym (symmetry_CCX_f.proved))) Eq.refl Eq.refl

  proved : K01 • CCX12 ≈ CCX02 • K01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel129 where

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

module drel101 where

  step0 : X2 • CX01 • CCX02 ≈ X2 • CX01 • CCX02 • X2 • X2
  step0 = by-assoc-and (under (X2 • CX01 • CCX02) (ε) (sym (elim_X2.proved))) Eq.refl Eq.refl

  step1 : X2 • CX01 • CCX02 • X2 • X2 ≈ X2 • CX01 • CCX02 • X2 • CCX02 • CCX02 • X2
  step1 = by-assoc-and (under (X2 • CX01 • CCX02 • X2) (X2) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

  step2 : X2 • CX01 • CCX02 • X2 • CCX02 • CCX02 • X2 ≈ X2 • CX01 • CCX02 • CCX02 • CX01 • X2 • CCX02 • X2
  step2 = by-assoc-and (under (X2 • CX01 • CCX02) (CCX02 • X2) (drel129.proved)) Eq.refl Eq.refl

  step3 : X2 • CX01 • CCX02 • CCX02 • CX01 • X2 • CCX02 • X2 ≈ X2 • CX01 • CX01 • X2 • CCX02 • X2
  step3 = by-assoc-and (under (X2 • CX01) (CX01 • X2 • CCX02 • X2) (elim_CCX1.proved)) Eq.refl Eq.refl

  step4 : X2 • CX01 • CX01 • X2 • CCX02 • X2 ≈ X2 • X2 • CCX02 • X2
  step4 = by-assoc-and (under (X2) (X2 • CCX02 • X2) (axiom r022)) Eq.refl Eq.refl

  step5 : X2 • X2 • CCX02 • X2 ≈ CCX02 • X2
  step5 = by-assoc-and (under (ε) (CCX02 • X2) (elim_X2.proved)) Eq.refl Eq.refl

  proved : X2 • CX01 • CCX02 ≈ CCX02 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module elim_CCX2 where

  step0 : CCX01 • CCX01 ≈ CCX01 • SWAP02 • CCX12 • SWAP02
  step0 = by-assoc-and (under (CCX01) (ε) (axiom r032)) Eq.refl Eq.refl

  step1 : CCX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • SWAP02 • CCX12 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CCX12 • SWAP02) (axiom r032)) Eq.refl Eq.refl

  step2 : SWAP02 • CCX12 • SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CCX12 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • CCX12) (CCX12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • CCX12 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r024)) Eq.refl Eq.refl

  step4 : SWAP02 • SWAP02 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : CCX01 • CCX01 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel103 where

  step0 : CCX01 • CX01 ≈ CCX01 • CX01 • CCX01 • CCX01
  step0 = by-assoc-and (under (CCX01 • CX01) (ε) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

  step1 : CCX01 • CX01 • CCX01 • CCX01 ≈ CCX01 • CX01 • CCX01 • CX02 • CX02 • CCX01
  step1 = by-assoc-and (under (CCX01 • CX01 • CCX01) (CCX01) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step2 : CCX01 • CX01 • CCX01 • CX02 • CX02 • CCX01 ≈ CCX01 • CX01 • CCX01 • CX02 • CX01 • CX01 • CX02 • CCX01
  step2 = by-assoc-and (under (CCX01 • CX01 • CCX01 • CX02) (CX02 • CCX01) (sym (axiom r022))) Eq.refl Eq.refl

  step3 : CCX01 • CX01 • CCX01 • CX02 • CX01 • CX01 • CX02 • CCX01 ≈ CCX01 • CX01 • CX01 • CCX01 • CX01 • CX02 • CCX01
  step3 = by-assoc-and (under (CCX01 • CX01) (CX01 • CX02 • CCX01) (sym (drel141.proved))) Eq.refl Eq.refl

  step4 : CCX01 • CX01 • CX01 • CCX01 • CX01 • CX02 • CCX01 ≈ CCX01 • CCX01 • CX01 • CX02 • CCX01
  step4 = by-assoc-and (under (CCX01) (CCX01 • CX01 • CX02 • CCX01) (axiom r022)) Eq.refl Eq.refl

  step5 : CCX01 • CCX01 • CX01 • CX02 • CCX01 ≈ CX01 • CX02 • CCX01
  step5 = by-assoc-and (under (ε) (CX01 • CX02 • CCX01) (elim_CCX2.proved)) Eq.refl Eq.refl

  proved : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel168 where

  step0 : CX01 • CZ01 ≈ CX01 • CZ01 • CX01 • CX01
  step0 = by-assoc-and (under (CX01 • CZ01) (ε) (sym (axiom r022))) Eq.refl Eq.refl

  step1 : CX01 • CZ01 • CX01 • CX01 ≈ CZ01 • CZ01 • CX01 • CZ01 • CX01 • CX01
  step1 = by-assoc-and (under (ε) (CX01 • CZ01 • CX01 • CX01) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : CZ01 • CZ01 • CX01 • CZ01 • CX01 • CX01 ≈ CZ01 • Z0 • CX01
  step2 = by-assoc-and (under (CZ01) (CX01) (sym (axiom r003))) Eq.refl Eq.refl

  proved : CX01 • CZ01 ≈ CZ01 • Z0 • CX01
  proved = trans step0 (trans step1 (trans step2 (refl)))

module drel104 where

  step0 : CX01 • Z0 • CZ01 ≈ CX01 • Z0 • CZ01 • CX01 • CX01
  step0 = by-assoc-and (under (CX01 • Z0 • CZ01) (ε) (sym (axiom r022))) Eq.refl Eq.refl

  step1 : CX01 • Z0 • CZ01 • CX01 • CX01 ≈ CX01 • Z0 • CZ01 • CX01 • CZ01 • CZ01 • CX01
  step1 = by-assoc-and (under (CX01 • Z0 • CZ01 • CX01) (CX01) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : CX01 • Z0 • CZ01 • CX01 • CZ01 • CZ01 • CX01 ≈ CX01 • Z0 • CZ01 • CZ01 • Z0 • CX01 • CZ01 • CX01
  step2 = by-assoc-and (under (CX01 • Z0 • CZ01) (CZ01 • CX01) (drel168.proved)) Eq.refl Eq.refl

  step3 : CX01 • Z0 • CZ01 • CZ01 • Z0 • CX01 • CZ01 • CX01 ≈ CX01 • Z0 • Z0 • CX01 • CZ01 • CX01
  step3 = by-assoc-and (under (CX01 • Z0) (Z0 • CX01 • CZ01 • CX01) (elim_CZ01.proved)) Eq.refl Eq.refl

  step4 : CX01 • Z0 • Z0 • CX01 • CZ01 • CX01 ≈ CX01 • CX01 • CZ01 • CX01
  step4 = by-assoc-and (under (CX01) (CX01 • CZ01 • CX01) (elim_Z0.proved)) Eq.refl Eq.refl

  step5 : CX01 • CX01 • CZ01 • CX01 ≈ CZ01 • CX01
  step5 = by-assoc-and (under (ε) (CZ01 • CX01) (axiom r022)) Eq.refl Eq.refl

  proved : CX01 • Z0 • CZ01 ≈ CZ01 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel105 where

  step0 : X0 • X1 • CX01 ≈ X1 • X0 • CX01
  step0 = by-assoc-and (under (ε) (CX01) (X0X1.proved)) Eq.refl Eq.refl

  step1 : X1 • X0 • CX01 ≈ CX01 • CX01 • X1 • X0 • CX01
  step1 = by-assoc-and (under (ε) (X1 • X0 • CX01) (sym (axiom r022))) Eq.refl Eq.refl

  step2 : CX01 • CX01 • X1 • X0 • CX01 ≈ CX01 • X0 • X0 • CX01 • X1 • X0 • CX01
  step2 = by-assoc-and (under (CX01) (CX01 • X1 • X0 • CX01) (sym (axiom r021))) Eq.refl Eq.refl

  step3 : CX01 • X0 • X0 • CX01 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X1 • X0 • X1 • X0 • CX01
  step3 = by-assoc-and (under (CX01 • X0) (X1 • X0 • CX01) (drel162.proved)) Eq.refl Eq.refl

  step4 : CX01 • X0 • CX01 • X1 • X0 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X0 • X1 • X1 • X0 • CX01
  step4 = by-assoc-and (under (CX01 • X0 • CX01) (X1 • X0 • CX01) (sym (X0X1.proved))) Eq.refl Eq.refl

  step5 : CX01 • X0 • CX01 • X0 • X1 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X0 • X0 • CX01
  step5 = by-assoc-and (under (CX01 • X0 • CX01 • X0) (X0 • CX01) (elim_X1.proved)) Eq.refl Eq.refl

  step6 : CX01 • X0 • CX01 • X0 • X0 • CX01 ≈ CX01 • X0 • CX01 • CX01
  step6 = by-assoc-and (under (CX01 • X0 • CX01) (CX01) (axiom r021)) Eq.refl Eq.refl

  step7 : CX01 • X0 • CX01 • CX01 ≈ CX01 • X0
  step7 = by-assoc-and (under (CX01 • X0) (ε) (axiom r022)) Eq.refl Eq.refl

  proved : X0 • X1 • CX01 ≈ CX01 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel126 where

  step0 : X0 • CX02 ≈ X0 • SWAP12 • CX01 • SWAP12
  step0 = by-assoc-and (under (X0) (ε) (axiom r009)) Eq.refl Eq.refl

  step1 : X0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • X0 • CX01 • SWAP12
  step1 = by-assoc-and (under (ε) (CX01 • SWAP12) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • X0 • CX01 • SWAP12 ≈ SWAP12 • CX01 • X1 • X0 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (drel162.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • X1 • X0 • SWAP12 ≈ SWAP12 • CX01 • X1 • SWAP12 • X0
  step3 = by-assoc-and (under (SWAP12 • CX01 • X1) (ε) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CX01 • X1 • SWAP12 • X0 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 • X0
  step4 = by-assoc-and (under (SWAP12 • CX01) (X1 • SWAP12 • X0) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 • X0 ≈ SWAP12 • CX01 • SWAP12 • X2 • X0
  step5 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (X0) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CX01 • SWAP12 • X2 • X0 ≈ CX02 • X2 • X0
  step6 = by-assoc-and (under (ε) (X2 • X0) (sym (axiom r009))) Eq.refl Eq.refl

  proved : X0 • CX02 ≈ CX02 • X2 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel106 where

  step0 : X0 • X2 • CX02 ≈ CX02 • CX02 • X0 • X2 • CX02
  step0 = by-assoc-and (under (ε) (X0 • X2 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step1 : CX02 • CX02 • X0 • X2 • CX02 ≈ CX02 • X0 • X0 • CX02 • X0 • X2 • CX02
  step1 = by-assoc-and (under (CX02) (CX02 • X0 • X2 • CX02) (sym (axiom r021))) Eq.refl Eq.refl

  step2 : CX02 • X0 • X0 • CX02 • X0 • X2 • CX02 ≈ CX02 • X0 • CX02 • X2 • X0 • X0 • X2 • CX02
  step2 = by-assoc-and (under (CX02 • X0) (X0 • X2 • CX02) (drel126.proved)) Eq.refl Eq.refl

  step3 : CX02 • X0 • CX02 • X2 • X0 • X0 • X2 • CX02 ≈ CX02 • X0 • CX02 • X2 • X2 • CX02
  step3 = by-assoc-and (under (CX02 • X0 • CX02 • X2) (X2 • CX02) (axiom r021)) Eq.refl Eq.refl

  step4 : CX02 • X0 • CX02 • X2 • X2 • CX02 ≈ CX02 • X0 • CX02 • CX02
  step4 = by-assoc-and (under (CX02 • X0 • CX02) (CX02) (elim_X2.proved)) Eq.refl Eq.refl

  step5 : CX02 • X0 • CX02 • CX02 ≈ CX02 • X0
  step5 = by-assoc-and (under (CX02 • X0) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : X0 • X2 • CX02 ≈ CX02 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_CZ_c where

  step0 : CZ02 ≈ CZ02 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CZ02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CZ02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r019))) Eq.refl Eq.refl

  proved : CZ02 ≈ SWAP01 • CZ12 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (refl)))

module drel139 where

  step0 : CX12 • CZ02 ≈ SWAP01 • CX02 • SWAP01 • CZ02
  step0 = by-assoc-and (under (ε) (CZ02) (axiom r030)) Eq.refl Eq.refl

  step1 : SWAP01 • CX02 • SWAP01 • CZ02 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • CZ02
  step1 = by-assoc-and (under (SWAP01) (SWAP01 • CZ02) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • CZ02 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • CZ12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01) (ε) (symmetry_CZ_c.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • CZ12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01
  step3 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01) (SWAP01) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CZ12 • SWAP12 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12) (SWAP12 • CZ12 • SWAP12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP01
  step5 = by-assoc-and (under (SWAP01 • SWAP12 • CX01) (CZ12 • SWAP12 • SWAP01) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (axiom r043)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP01
  step7 = by-assoc-and (under (SWAP01 • SWAP12 • CZ12) (CX01 • SWAP12 • SWAP01) (axiom r018)) Eq.refl Eq.refl

  step8 : SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP01
  step8 = by-assoc-and (under (SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01) (SWAP01) (sym (axiom r009))) Eq.refl Eq.refl

  step9 : SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • CZ01 • CX02 • SWAP01
  step9 = by-assoc-and (under (SWAP01) (CZ01 • CX02 • SWAP01) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

  step10 : SWAP01 • CZ12 • CZ01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01
  step10 = by-assoc-and (under (SWAP01 • CZ12) (CX02 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step11 : SWAP01 • CZ12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01 • CZ01 • CX12
  step11 = by-assoc-and (under (SWAP01 • CZ12 • SWAP01 • CZ01) (ε) (sym (axiom r030))) Eq.refl Eq.refl

  step12 : SWAP01 • CZ12 • SWAP01 • CZ01 • CX12 ≈ CZ02 • CZ01 • CX12
  step12 = by-assoc-and (under (ε) (CZ01 • CX12) (sym (symmetry_CZ_c.proved))) Eq.refl Eq.refl

  proved : CX12 • CZ02 ≈ CZ02 • CZ01 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))

module drel108 where

  step0 : CZ02 • CX12 ≈ CX12 • CX12 • CZ02 • CX12
  step0 = by-assoc-and (under (ε) (CZ02 • CX12) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step1 : CX12 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ01 • CX12 • CZ02 • CX12
  step1 = by-assoc-and (under (CX12) (CX12 • CZ02 • CX12) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : CX12 • CZ01 • CZ01 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CZ02 • CZ01 • CX12 • CZ02 • CX12
  step2 = by-assoc-and (under (CX12 • CZ01) (CZ01 • CX12 • CZ02 • CX12) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step3 : CX12 • CZ01 • CZ02 • CZ02 • CZ01 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CX12 • CZ02 • CZ02 • CX12
  step3 = by-assoc-and (under (CX12 • CZ01 • CZ02) (CZ02 • CX12) (sym (drel139.proved))) Eq.refl Eq.refl

  step4 : CX12 • CZ01 • CZ02 • CX12 • CZ02 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CX12 • CX12
  step4 = by-assoc-and (under (CX12 • CZ01 • CZ02 • CX12) (CX12) (elim_CZ02.proved)) Eq.refl Eq.refl

  step5 : CX12 • CZ01 • CZ02 • CX12 • CX12 ≈ CX12 • CZ01 • CZ02
  step5 = by-assoc-and (under (CX12 • CZ01 • CZ02) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

  proved : CZ02 • CX12 ≈ CX12 • CZ01 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel164 where

  step0 : CZ02 • CZ12 ≈ CZ02 • SWAP12 • CZ12 • SWAP12
  step0 = by-assoc-and (under (CZ02) (ε) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

  step1 : CZ02 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ12 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CZ12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CZ01 • CZ12 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01) (CZ12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • CZ12 • SWAP12 ≈ SWAP12 • CZ12 • CZ01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r040)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ12 • CZ01 • SWAP12 ≈ SWAP12 • CZ12 • SWAP12 • SWAP12 • CZ01 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CZ12) (CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CZ12 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ CZ12 • SWAP12 • CZ01 • SWAP12
  step5 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

  step6 : CZ12 • SWAP12 • CZ01 • SWAP12 ≈ CZ12 • CZ02
  step6 = by-assoc-and (under (CZ12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

  proved : CZ02 • CZ12 ≈ CZ12 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel109 where

  step0 : CZ12 • CX01 ≈ CZ02 • CZ02 • CZ12 • CX01
  step0 = by-assoc-and (under (ε) (CZ12 • CX01) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step1 : CZ02 • CZ02 • CZ12 • CX01 ≈ CZ02 • CZ12 • CZ02 • CX01
  step1 = by-assoc-and (under (CZ02) (CX01) (drel164.proved)) Eq.refl Eq.refl

  step2 : CZ02 • CZ12 • CZ02 • CX01 ≈ CZ02 • CX01 • CZ12
  step2 = by-assoc-and (under (CZ02) (ε) (sym (axiom r043))) Eq.refl Eq.refl

  step3 : CZ02 • CX01 • CZ12 ≈ CX01 • CZ02 • CZ12
  step3 = by-assoc-and (under (ε) (CZ12) (sym (drel166.proved))) Eq.refl Eq.refl

  proved : CZ12 • CX01 ≈ CX01 • CZ02 • CZ12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))
