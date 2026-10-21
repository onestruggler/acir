{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B005 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r001 ; r004 ; r009 ; r011 ; r012 ; r014 ; r015 ; r016 ; r018 ; r019 ; r021 ; r022 ; r023 ; r024 ; r025 ; r027 ; r028 ; r029 ; r030 ; r033 ; r034 ; r035 ; r039 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Proofs.B000 using (module X0X1)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module drel128 ; module drel162 ; module elim_CCX1 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module elim_X1 ; module symmetry_CX_d ; module symmetry_CX_h ; module symmetry_SWAP02)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel41 ; module drel64 ; module drel9 ; module elim_CZ01 ; module elim_CZ02 ; module elim_CZ12 ; module elim_X2 ; module elim_Z0 ; module elim_Z2 ; module symmetry_CZ_a ; module symmetry_CZ_b)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_SWAP_a ; module drel137 ; module elim_Z1 ; module symmetry_X_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module drel30 ; module drel47 ; module drel48 ; module drel90 ; module symmetry_K_a)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module drel63 ; module elim_CCX2)

module drel11 where

  step0 : CX12 • CX02 ≈ SWAP01 • CX02 • SWAP01 • CX02
  step0 = by-assoc-and (under (ε) (CX02) (axiom r030)) Eq.refl Eq.refl

  step1 : SWAP01 • CX02 • SWAP01 • CX02 ≈ SWAP01 • CX02 • SWAP01 • CX02 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • CX02 • SWAP01 • CX02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • CX02 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • CX02 • CX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CX02) (SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step3 : SWAP01 • CX02 • CX12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • CX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (CX12 • SWAP01) (axiom r009)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • CX01 • SWAP12 • CX12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX21 • SWAP12 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12) (SWAP01) (symmetry_CX_d.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX21 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • CX21 • SWAP12 • SWAP01
  step5 = by-assoc-and (under (SWAP01 • SWAP12 • CX01) (CX21 • SWAP12 • SWAP01) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP12 • CX01 • CX21 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX21 • CX01 • SWAP12 • SWAP01
  step6 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (drel41.proved)) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP12 • CX21 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX21 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP01
  step7 = by-assoc-and (under (SWAP01 • SWAP12 • CX21) (CX01 • SWAP12 • SWAP01) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step8 : SWAP01 • SWAP12 • CX21 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX21 • SWAP12 • CX02 • SWAP01
  step8 = by-assoc-and (under (SWAP01 • SWAP12 • CX21 • SWAP12) (SWAP01) (sym (axiom r009))) Eq.refl Eq.refl

  step9 : SWAP01 • SWAP12 • CX21 • SWAP12 • CX02 • SWAP01 ≈ SWAP01 • CX12 • CX02 • SWAP01
  step9 = by-assoc-and (under (SWAP01) (CX02 • SWAP01) (sym (symmetry_CX_d.proved))) Eq.refl Eq.refl

  step10 : SWAP01 • CX12 • CX02 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • CX02 • SWAP01
  step10 = by-assoc-and (under (SWAP01) (CX02 • SWAP01) (axiom r030)) Eq.refl Eq.refl

  step11 : SWAP01 • SWAP01 • CX02 • SWAP01 • CX02 • SWAP01 ≈ CX02 • SWAP01 • CX02 • SWAP01
  step11 = by-assoc-and (under (ε) (CX02 • SWAP01 • CX02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step12 : CX02 • SWAP01 • CX02 • SWAP01 ≈ CX02 • CX12
  step12 = by-assoc-and (under (CX02) (ε) (sym (axiom r030))) Eq.refl Eq.refl

  proved : CX12 • CX02 ≈ CX02 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))

module drel29 where

  step0 : CCX01 • K12 ≈ CCX01 • K12 • CCX02 • CCX02
  step0 = by-assoc-and (under (CCX01 • K12) (ε) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

  step1 : CCX01 • K12 • CCX02 • CCX02 ≈ CCX01 • K12 • CCX02 • K12 • K12 • CCX02
  step1 = by-assoc-and (under (CCX01 • K12 • CCX02) (CCX02) (sym (axiom r023))) Eq.refl Eq.refl

  step2 : CCX01 • K12 • CCX02 • K12 • K12 • CCX02 ≈ CCX01 • K12 • K12 • CCX01 • K12 • CCX02
  step2 = by-assoc-and (under (CCX01 • K12) (K12 • CCX02) (sym (drel128.proved))) Eq.refl Eq.refl

  step3 : CCX01 • K12 • K12 • CCX01 • K12 • CCX02 ≈ CCX01 • CCX01 • K12 • CCX02
  step3 = by-assoc-and (under (CCX01) (CCX01 • K12 • CCX02) (axiom r023)) Eq.refl Eq.refl

  step4 : CCX01 • CCX01 • K12 • CCX02 ≈ K12 • CCX02
  step4 = by-assoc-and (under (ε) (K12 • CCX02) (elim_CCX2.proved)) Eq.refl Eq.refl

  proved : CCX01 • K12 ≈ K12 • CCX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel49 where

  step0 : K12 • CZ01 ≈ K12 • K12 • CX01 • K12
  step0 = by-assoc-and (under (K12) (ε) (axiom r001)) Eq.refl Eq.refl

  step1 : K12 • K12 • CX01 • K12 ≈ CX01 • K12
  step1 = by-assoc-and (under (ε) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

  proved : K12 • CZ01 ≈ CX01 • K12
  proved = trans step0 (trans step1 (refl))

module drel85 where

  step0 : CCX12 • K01 ≈ K01 • K01 • CCX12 • K01
  step0 = by-assoc-and (under (ε) (CCX12 • K01) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • CCX12 • K01 ≈ K01 • CCX02 • K01 • K01
  step1 = by-assoc-and (under (K01) (K01) (drel63.proved)) Eq.refl Eq.refl

  step2 : K01 • CCX02 • K01 • K01 ≈ K01 • CCX02
  step2 = by-assoc-and (under (K01 • CCX02) (ε) (axiom r025)) Eq.refl Eq.refl

  proved : CCX12 • K01 ≈ K01 • CCX02
  proved = trans step0 (trans step1 (trans step2 (refl)))

module drel86 where

  step0 : K12 • CCX01 ≈ K12 • CCX01 • K12 • K12
  step0 = by-assoc-and (under (K12 • CCX01) (ε) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • CCX01 • K12 • K12 ≈ K12 • K12 • CCX02 • K12
  step1 = by-assoc-and (under (K12) (K12) (drel29.proved)) Eq.refl Eq.refl

  step2 : K12 • K12 • CCX02 • K12 ≈ CCX02 • K12
  step2 = by-assoc-and (under (ε) (CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

  proved : K12 • CCX01 ≈ CCX02 • K12
  proved = trans step0 (trans step1 (trans step2 (refl)))

module drel74 where

  step0 : K01 • CX20 ≈ K01 • SWAP02 • CX02 • SWAP02
  step0 = by-assoc-and (under (K01) (ε) (axiom r029)) Eq.refl Eq.refl

  step1 : K01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • SWAP02 • CX02 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CX02 • SWAP02) (axiom r011)) Eq.refl Eq.refl

  step2 : SWAP02 • K12 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • K12 • CX02 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • K12) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • K12 • CX02 • SWAP02 ≈ SWAP02 • CZ02 • K12 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (sym (drel48.proved))) Eq.refl Eq.refl

  step4 : SWAP02 • CZ02 • K12 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • SWAP02 • K12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CZ02) (K12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CZ02 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • K01
  step5 = by-assoc-and (under (SWAP02 • CZ02 • SWAP02) (ε) (sym (axiom r011))) Eq.refl Eq.refl

  step6 : SWAP02 • CZ02 • SWAP02 • K01 ≈ CZ02 • K01
  step6 = by-assoc-and (under (ε) (K01) (sym (symmetry_CZ_a.proved))) Eq.refl Eq.refl

  proved : K01 • CX20 ≈ CZ02 • K01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel89 where

  step0 : CZ12 • K01 ≈ SWAP01 • CZ02 • SWAP01 • K01
  step0 = by-assoc-and (under (ε) (K01) (axiom r019)) Eq.refl Eq.refl

  step1 : SWAP01 • CZ02 • SWAP01 • K01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • K01 • SWAP01
  step1 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01) (ε) (axiom r035)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • K01 • SWAP01 ≈ SWAP01 • CZ02 • K01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ02) (K01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CZ02 • K01 • SWAP01 ≈ SWAP01 • K01 • CX20 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (sym (drel74.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • K01 • CX20 • SWAP01 ≈ SWAP01 • SWAP01 • K01 • SWAP01 • CX20 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CX20 • SWAP01) (axiom r035)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • K01 • SWAP01 • CX20 • SWAP01 ≈ K01 • SWAP01 • CX20 • SWAP01
  step5 = by-assoc-and (under (ε) (K01 • SWAP01 • CX20 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : K01 • SWAP01 • CX20 • SWAP01 ≈ K01 • SWAP01 • SWAP01 • CX21 • SWAP01 • SWAP01
  step6 = by-assoc-and (under (K01 • SWAP01) (SWAP01) (symmetry_CX_h.proved)) Eq.refl Eq.refl

  step7 : K01 • SWAP01 • SWAP01 • CX21 • SWAP01 • SWAP01 ≈ K01 • SWAP01 • SWAP01 • CX21
  step7 = by-assoc-and (under (K01 • SWAP01 • SWAP01 • CX21) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step8 : K01 • SWAP01 • SWAP01 • CX21 ≈ K01 • CX21
  step8 = by-assoc-and (under (K01) (CX21) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CZ12 • K01 ≈ K01 • CX21
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel159 where

  step0 : CZ01 • CCX12 ≈ K12 • K12 • CZ01 • CCX12
  step0 = by-assoc-and (under (ε) (CZ01 • CCX12) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ01 • CCX12 ≈ K12 • K01 • K01 • K12 • CZ01 • CCX12
  step1 = by-assoc-and (under (K12) (K12 • CZ01 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

  step2 : K12 • K01 • K01 • K12 • CZ01 • CCX12 ≈ K12 • K01 • K01 • CX01 • K12 • CCX12
  step2 = by-assoc-and (under (K12 • K01 • K01) (CCX12) (drel49.proved)) Eq.refl Eq.refl

  step3 : K12 • K01 • K01 • CX01 • K12 • CCX12 ≈ K12 • K01 • K01 • CX01 • K01 • K01 • K12 • CCX12
  step3 = by-assoc-and (under (K12 • K01 • K01 • CX01) (K12 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

  step4 : K12 • K01 • K01 • CX01 • K01 • K01 • K12 • CCX12 ≈ K12 • K01 • CX10 • K01 • K12 • CCX12
  step4 = by-assoc-and (under (K12 • K01) (K01 • K12 • CCX12) (sym (axiom r012))) Eq.refl Eq.refl

  step5 : K12 • K01 • CX10 • K01 • K12 • CCX12 ≈ K12 • K01 • CX10 • K12 • K01 • CCX12
  step5 = by-assoc-and (under (K12 • K01 • CX10) (CCX12) (axiom r039)) Eq.refl Eq.refl

  step6 : K12 • K01 • CX10 • K12 • K01 • CCX12 ≈ K12 • K01 • CX10 • K12 • CCX02 • K01
  step6 = by-assoc-and (under (K12 • K01 • CX10 • K12) (ε) (drel63.proved)) Eq.refl Eq.refl

  step7 : K12 • K01 • CX10 • K12 • CCX02 • K01 ≈ K12 • K01 • CX10 • CCX01 • K12 • K01
  step7 = by-assoc-and (under (K12 • K01 • CX10) (K01) (sym (drel29.proved))) Eq.refl Eq.refl

  step8 : K12 • K01 • CX10 • CCX01 • K12 • K01 ≈ K12 • K01 • CCX01 • CX12 • CX10 • K12 • K01
  step8 = by-assoc-and (under (K12 • K01) (K12 • K01) (drel90.proved)) Eq.refl Eq.refl

  step9 : K12 • K01 • CCX01 • CX12 • CX10 • K12 • K01 ≈ K12 • K01 • CCX01 • CX12 • CX10 • K01 • K12
  step9 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • CX10) (ε) (sym (axiom r039))) Eq.refl Eq.refl

  step10 : K12 • K01 • CCX01 • CX12 • CX10 • K01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • CX01 • K01 • K01 • K12
  step10 = by-assoc-and (under (K12 • K01 • CCX01 • CX12) (K01 • K12) (axiom r012)) Eq.refl Eq.refl

  step11 : K12 • K01 • CCX01 • CX12 • K01 • CX01 • K01 • K01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • CX01 • K12
  step11 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01 • CX01) (K12) (axiom r025)) Eq.refl Eq.refl

  step12 : K12 • K01 • CCX01 • CX12 • K01 • CX01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • K12 • K12 • CX01 • K12
  step12 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01) (CX01 • K12) (sym (axiom r023))) Eq.refl Eq.refl

  step13 : K12 • K01 • CCX01 • CX12 • K01 • K12 • K12 • CX01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • K12 • CZ01
  step13 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01 • K12) (ε) (sym (axiom r001))) Eq.refl Eq.refl

  step14 : K12 • K01 • CCX01 • CX12 • K01 • K12 • CZ01 ≈ K01 • K12 • CCX01 • CX12 • K01 • K12 • CZ01
  step14 = by-assoc-and (under (ε) (CCX01 • CX12 • K01 • K12 • CZ01) (sym (axiom r039))) Eq.refl Eq.refl

  step15 : K01 • K12 • CCX01 • CX12 • K01 • K12 • CZ01 ≈ K01 • CCX02 • K12 • CX12 • K01 • K12 • CZ01
  step15 = by-assoc-and (under (K01) (CX12 • K01 • K12 • CZ01) (drel86.proved)) Eq.refl Eq.refl

  step16 : K01 • CCX02 • K12 • CX12 • K01 • K12 • CZ01 ≈ K01 • CCX02 • K12 • CX12 • K12 • K01 • CZ01
  step16 = by-assoc-and (under (K01 • CCX02 • K12 • CX12) (CZ01) (axiom r039)) Eq.refl Eq.refl

  step17 : K01 • CCX02 • K12 • CX12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • K12 • CX12 • K12 • K01 • CZ01
  step17 = by-assoc-and (under (ε) (K12 • CX12 • K12 • K01 • CZ01) (sym (drel85.proved))) Eq.refl Eq.refl

  step18 : CCX12 • K01 • K12 • CX12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • CX21 • K12 • K12 • K01 • CZ01
  step18 = by-assoc-and (under (CCX12 • K01) (K12 • K01 • CZ01) (sym (drel30.proved))) Eq.refl Eq.refl

  step19 : CCX12 • K01 • CX21 • K12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • CX21 • K01 • CZ01
  step19 = by-assoc-and (under (CCX12 • K01 • CX21) (K01 • CZ01) (axiom r023)) Eq.refl Eq.refl

  step20 : CCX12 • K01 • CX21 • K01 • CZ01 ≈ CCX12 • CZ12 • K01 • K01 • CZ01
  step20 = by-assoc-and (under (CCX12) (K01 • CZ01) (sym (drel89.proved))) Eq.refl Eq.refl

  step21 : CCX12 • CZ12 • K01 • K01 • CZ01 ≈ CCX12 • CZ12 • CZ01
  step21 = by-assoc-and (under (CCX12 • CZ12) (CZ01) (axiom r025)) Eq.refl Eq.refl

  proved : CZ01 • CCX12 ≈ CCX12 • CZ12 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (trans step15 (trans step16 (trans step17 (trans step18 (trans step19 (trans step20 (trans step21 (refl))))))))))))))))))))))

module drel50 where

  step0 : CZ01 • K12 ≈ CZ01 • K12 • CX01 • CX01
  step0 = by-assoc-and (under (CZ01 • K12) (ε) (sym (axiom r022))) Eq.refl Eq.refl

  step1 : CZ01 • K12 • CX01 • CX01 ≈ CZ01 • K12 • CX01 • K12 • K12 • CX01
  step1 = by-assoc-and (under (CZ01 • K12 • CX01) (CX01) (sym (axiom r023))) Eq.refl Eq.refl

  step2 : CZ01 • K12 • CX01 • K12 • K12 • CX01 ≈ CZ01 • K12 • K12 • CZ01 • K12 • CX01
  step2 = by-assoc-and (under (CZ01 • K12) (K12 • CX01) (sym (drel49.proved))) Eq.refl Eq.refl

  step3 : CZ01 • K12 • K12 • CZ01 • K12 • CX01 ≈ CZ01 • CZ01 • K12 • CX01
  step3 = by-assoc-and (under (CZ01) (CZ01 • K12 • CX01) (axiom r023)) Eq.refl Eq.refl

  step4 : CZ01 • CZ01 • K12 • CX01 ≈ K12 • CX01
  step4 = by-assoc-and (under (ε) (K12 • CX01) (elim_CZ01.proved)) Eq.refl Eq.refl

  proved : CZ01 • K12 ≈ K12 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel71 where

  step0 : CZ01 • CZ02 ≈ K12 • K12 • CZ01 • CZ02
  step0 = by-assoc-and (under (ε) (CZ01 • CZ02) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CZ01 • CZ02 ≈ K12 • CX01 • K12 • CZ02
  step1 = by-assoc-and (under (K12) (CZ02) (drel49.proved)) Eq.refl Eq.refl

  step2 : K12 • CX01 • K12 • CZ02 ≈ K12 • CX01 • CX02 • K12
  step2 = by-assoc-and (under (K12 • CX01) (ε) (drel47.proved)) Eq.refl Eq.refl

  step3 : K12 • CX01 • CX02 • K12 ≈ K12 • CX02 • CX01 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel9.proved)) Eq.refl Eq.refl

  step4 : K12 • CX02 • CX01 • K12 ≈ CZ02 • K12 • CX01 • K12
  step4 = by-assoc-and (under (ε) (CX01 • K12) (sym (drel48.proved))) Eq.refl Eq.refl

  step5 : CZ02 • K12 • CX01 • K12 ≈ CZ02 • CZ01 • K12 • K12
  step5 = by-assoc-and (under (CZ02) (K12) (sym (drel50.proved))) Eq.refl Eq.refl

  step6 : CZ02 • CZ01 • K12 • K12 ≈ CZ02 • CZ01
  step6 = by-assoc-and (under (CZ02 • CZ01) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CZ01 • CZ02 ≈ CZ02 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel152 where

  step0 : CZ01 • CCX02 ≈ CZ01 • SWAP01 • CCX12 • SWAP01
  step0 = by-assoc-and (under (CZ01) (ε) (axiom r014)) Eq.refl Eq.refl

  step1 : CZ01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01 • SWAP01 • CCX12 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ01 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CZ01 • CCX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ01) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CZ01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CZ12 • CZ01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel159.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX12 • CZ12 • CZ01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 • CZ01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CCX12) (CZ01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step5 : SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CZ02 • CZ01
  step5 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01 • CZ02) (ε) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

  step6 : SWAP01 • CCX12 • SWAP01 • CZ02 • CZ01 ≈ CCX02 • CZ02 • CZ01
  step6 = by-assoc-and (under (ε) (CZ02 • CZ01) (sym (axiom r014))) Eq.refl Eq.refl

  step7 : CCX02 • CZ02 • CZ01 ≈ CCX02 • CZ01 • CZ02
  step7 = by-assoc-and (under (CCX02) (ε) (sym (drel71.proved))) Eq.refl Eq.refl

  proved : CZ01 • CCX02 ≈ CCX02 • CZ01 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module drel151 where

  step0 : CZ02 • CCX01 ≈ CZ02 • SWAP12 • CCX02 • SWAP12
  step0 = by-assoc-and (under (CZ02) (ε) (axiom r033)) Eq.refl Eq.refl

  step1 : CZ02 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX02 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CCX02 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CZ01 • CCX02 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01) (CCX02 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • CZ01 • CZ02 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel152.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CCX02 • CZ01 • CZ02 • SWAP12 ≈ SWAP12 • CCX02 • CZ01 • SWAP12 • CZ01 • SWAP12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CCX02 • CZ01) (SWAP12) (axiom r018)) Eq.refl Eq.refl

  step5 : SWAP12 • CCX02 • CZ01 • SWAP12 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CCX02 • CZ01 • SWAP12 • CZ01
  step5 = by-assoc-and (under (SWAP12 • CCX02 • CZ01 • SWAP12 • CZ01) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • CCX02 • CZ01 • SWAP12 • CZ01 ≈ SWAP12 • CCX02 • SWAP12 • SWAP12 • CZ01 • SWAP12 • CZ01
  step6 = by-assoc-and (under (SWAP12 • CCX02) (CZ01 • SWAP12 • CZ01) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • CCX02 • SWAP12 • SWAP12 • CZ01 • SWAP12 • CZ01 ≈ SWAP12 • CCX02 • SWAP12 • CZ02 • CZ01
  step7 = by-assoc-and (under (SWAP12 • CCX02 • SWAP12) (CZ01) (sym (axiom r018))) Eq.refl Eq.refl

  step8 : SWAP12 • CCX02 • SWAP12 • CZ02 • CZ01 ≈ CCX01 • CZ02 • CZ01
  step8 = by-assoc-and (under (ε) (CZ02 • CZ01) (sym (axiom r033))) Eq.refl Eq.refl

  step9 : CCX01 • CZ02 • CZ01 ≈ CCX01 • CZ01 • CZ02
  step9 = by-assoc-and (under (CCX01) (ε) (sym (drel71.proved))) Eq.refl Eq.refl

  proved : CZ02 • CCX01 ≈ CCX01 • CZ01 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))

module drel114 where

  step0 : CZ02 • CZ01 • CCX01 ≈ CZ02 • CZ01 • CCX01 • CZ02 • CZ02
  step0 = by-assoc-and (under (CZ02 • CZ01 • CCX01) (ε) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step1 : CZ02 • CZ01 • CCX01 • CZ02 • CZ02 ≈ CZ02 • CZ01 • CCX01 • CZ02 • CCX01 • CCX01 • CZ02
  step1 = by-assoc-and (under (CZ02 • CZ01 • CCX01 • CZ02) (CZ02) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

  step2 : CZ02 • CZ01 • CCX01 • CZ02 • CCX01 • CCX01 • CZ02 ≈ CZ02 • CZ01 • CCX01 • CCX01 • CZ01 • CZ02 • CCX01 • CZ02
  step2 = by-assoc-and (under (CZ02 • CZ01 • CCX01) (CCX01 • CZ02) (drel151.proved)) Eq.refl Eq.refl

  step3 : CZ02 • CZ01 • CCX01 • CCX01 • CZ01 • CZ02 • CCX01 • CZ02 ≈ CZ02 • CZ01 • CZ01 • CZ02 • CCX01 • CZ02
  step3 = by-assoc-and (under (CZ02 • CZ01) (CZ01 • CZ02 • CCX01 • CZ02) (elim_CCX2.proved)) Eq.refl Eq.refl

  step4 : CZ02 • CZ01 • CZ01 • CZ02 • CCX01 • CZ02 ≈ CZ02 • CZ02 • CCX01 • CZ02
  step4 = by-assoc-and (under (CZ02) (CZ02 • CCX01 • CZ02) (elim_CZ01.proved)) Eq.refl Eq.refl

  step5 : CZ02 • CZ02 • CCX01 • CZ02 ≈ CCX01 • CZ02
  step5 = by-assoc-and (under (ε) (CCX01 • CZ02) (elim_CZ02.proved)) Eq.refl Eq.refl

  proved : CZ02 • CZ01 • CCX01 ≈ CCX01 • CZ02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel115 where

  step0 : CZ01 • CZ12 • CCX12 ≈ CZ01 • CZ12 • CCX12 • CZ01 • CZ01
  step0 = by-assoc-and (under (CZ01 • CZ12 • CCX12) (ε) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step1 : CZ01 • CZ12 • CCX12 • CZ01 • CZ01 ≈ CZ01 • CZ12 • CCX12 • CZ01 • CCX12 • CCX12 • CZ01
  step1 = by-assoc-and (under (CZ01 • CZ12 • CCX12 • CZ01) (CZ01) (sym (axiom r024))) Eq.refl Eq.refl

  step2 : CZ01 • CZ12 • CCX12 • CZ01 • CCX12 • CCX12 • CZ01 ≈ CZ01 • CZ12 • CCX12 • CCX12 • CZ12 • CZ01 • CCX12 • CZ01
  step2 = by-assoc-and (under (CZ01 • CZ12 • CCX12) (CCX12 • CZ01) (drel159.proved)) Eq.refl Eq.refl

  step3 : CZ01 • CZ12 • CCX12 • CCX12 • CZ12 • CZ01 • CCX12 • CZ01 ≈ CZ01 • CZ12 • CZ12 • CZ01 • CCX12 • CZ01
  step3 = by-assoc-and (under (CZ01 • CZ12) (CZ12 • CZ01 • CCX12 • CZ01) (axiom r024)) Eq.refl Eq.refl

  step4 : CZ01 • CZ12 • CZ12 • CZ01 • CCX12 • CZ01 ≈ CZ01 • CZ01 • CCX12 • CZ01
  step4 = by-assoc-and (under (CZ01) (CZ01 • CCX12 • CZ01) (elim_CZ12.proved)) Eq.refl Eq.refl

  step5 : CZ01 • CZ01 • CCX12 • CZ01 ≈ CCX12 • CZ01
  step5 = by-assoc-and (under (ε) (CCX12 • CZ01) (elim_CZ01.proved)) Eq.refl Eq.refl

  proved : CZ01 • CZ12 • CCX12 ≈ CCX12 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel117 where

  step0 : CZ01 • CZ02 • CCX02 ≈ CZ02 • CZ01 • CCX02
  step0 = by-assoc-and (under (ε) (CCX02) (drel71.proved)) Eq.refl Eq.refl

  step1 : CZ02 • CZ01 • CCX02 ≈ CZ02 • CZ01 • CCX02 • CZ01 • CZ01
  step1 = by-assoc-and (under (CZ02 • CZ01 • CCX02) (ε) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : CZ02 • CZ01 • CCX02 • CZ01 • CZ01 ≈ CZ02 • CZ01 • CCX02 • CZ01 • CCX02 • CCX02 • CZ01
  step2 = by-assoc-and (under (CZ02 • CZ01 • CCX02 • CZ01) (CZ01) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

  step3 : CZ02 • CZ01 • CCX02 • CZ01 • CCX02 • CCX02 • CZ01 ≈ CZ02 • CZ01 • CCX02 • CCX02 • CZ01 • CZ02 • CCX02 • CZ01
  step3 = by-assoc-and (under (CZ02 • CZ01 • CCX02) (CCX02 • CZ01) (drel152.proved)) Eq.refl Eq.refl

  step4 : CZ02 • CZ01 • CCX02 • CCX02 • CZ01 • CZ02 • CCX02 • CZ01 ≈ CZ02 • CZ01 • CZ01 • CZ02 • CCX02 • CZ01
  step4 = by-assoc-and (under (CZ02 • CZ01) (CZ01 • CZ02 • CCX02 • CZ01) (elim_CCX1.proved)) Eq.refl Eq.refl

  step5 : CZ02 • CZ01 • CZ01 • CZ02 • CCX02 • CZ01 ≈ CZ02 • CZ02 • CCX02 • CZ01
  step5 = by-assoc-and (under (CZ02) (CZ02 • CCX02 • CZ01) (elim_CZ01.proved)) Eq.refl Eq.refl

  step6 : CZ02 • CZ02 • CCX02 • CZ01 ≈ CCX02 • CZ01
  step6 = by-assoc-and (under (ε) (CCX02 • CZ01) (elim_CZ02.proved)) Eq.refl Eq.refl

  proved : CZ01 • CZ02 • CCX02 ≈ CCX02 • CZ01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel160 where

  step0 : X0 • CZ01 ≈ X0 • K12 • K12 • CZ01
  step0 = by-assoc-and (under (X0) (CZ01) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : X0 • K12 • K12 • CZ01 ≈ K12 • X0 • K12 • CZ01
  step1 = by-assoc-and (under (ε) (K12 • CZ01) (axiom r027)) Eq.refl Eq.refl

  step2 : K12 • X0 • K12 • CZ01 ≈ K12 • X0 • CX01 • K12
  step2 = by-assoc-and (under (K12 • X0) (ε) (drel49.proved)) Eq.refl Eq.refl

  step3 : K12 • X0 • CX01 • K12 ≈ K12 • CX01 • X1 • X0 • K12
  step3 = by-assoc-and (under (K12) (K12) (drel162.proved)) Eq.refl Eq.refl

  step4 : K12 • CX01 • X1 • X0 • K12 ≈ K12 • CX01 • X0 • X1 • K12
  step4 = by-assoc-and (under (K12 • CX01) (K12) (sym (X0X1.proved))) Eq.refl Eq.refl

  step5 : K12 • CX01 • X0 • X1 • K12 ≈ K12 • CX01 • X1 • X0 • K12
  step5 = by-assoc-and (under (K12 • CX01) (K12) (X0X1.proved)) Eq.refl Eq.refl

  step6 : K12 • CX01 • X1 • X0 • K12 ≈ K12 • CX01 • X1 • K12 • X0
  step6 = by-assoc-and (under (K12 • CX01 • X1) (ε) (axiom r027)) Eq.refl Eq.refl

  step7 : K12 • CX01 • X1 • K12 • X0 ≈ K12 • CX01 • K12 • K12 • X1 • K12 • X0
  step7 = by-assoc-and (under (K12 • CX01) (X1 • K12 • X0) (sym (axiom r023))) Eq.refl Eq.refl

  step8 : K12 • CX01 • K12 • K12 • X1 • K12 • X0 ≈ K12 • CX01 • K12 • Z1 • X0
  step8 = by-assoc-and (under (K12 • CX01 • K12) (X0) (sym (axiom r004))) Eq.refl Eq.refl

  step9 : K12 • CX01 • K12 • Z1 • X0 ≈ CZ01 • Z1 • X0
  step9 = by-assoc-and (under (ε) (Z1 • X0) (sym (axiom r001))) Eq.refl Eq.refl

  proved : X0 • CZ01 ≈ CZ01 • Z1 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))

module drel118 where

  step0 : X0 • Z1 • CZ01 ≈ X0 • Z1 • CZ01 • X0 • X0
  step0 = by-assoc-and (under (X0 • Z1 • CZ01) (ε) (sym (axiom r021))) Eq.refl Eq.refl

  step1 : X0 • Z1 • CZ01 • X0 • X0 ≈ X0 • Z1 • CZ01 • X0 • CZ01 • CZ01 • X0
  step1 = by-assoc-and (under (X0 • Z1 • CZ01 • X0) (X0) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : X0 • Z1 • CZ01 • X0 • CZ01 • CZ01 • X0 ≈ X0 • Z1 • CZ01 • CZ01 • Z1 • X0 • CZ01 • X0
  step2 = by-assoc-and (under (X0 • Z1 • CZ01) (CZ01 • X0) (drel160.proved)) Eq.refl Eq.refl

  step3 : X0 • Z1 • CZ01 • CZ01 • Z1 • X0 • CZ01 • X0 ≈ X0 • Z1 • Z1 • X0 • CZ01 • X0
  step3 = by-assoc-and (under (X0 • Z1) (Z1 • X0 • CZ01 • X0) (elim_CZ01.proved)) Eq.refl Eq.refl

  step4 : X0 • Z1 • Z1 • X0 • CZ01 • X0 ≈ X0 • X0 • CZ01 • X0
  step4 = by-assoc-and (under (X0) (X0 • CZ01 • X0) (elim_Z1.proved)) Eq.refl Eq.refl

  step5 : X0 • X0 • CZ01 • X0 ≈ CZ01 • X0
  step5 = by-assoc-and (under (ε) (CZ01 • X0) (axiom r021)) Eq.refl Eq.refl

  proved : X0 • Z1 • CZ01 ≈ CZ01 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel145 where

  step0 : X1 • CZ01 ≈ X1 • SWAP01 • CZ01 • SWAP01
  step0 = by-assoc-and (under (X1) (ε) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step1 : X1 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CZ01 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CZ01 • SWAP01) (axiom r028)) Eq.refl Eq.refl

  step2 : SWAP01 • X0 • SWAP01 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • X0 • CZ01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • X0) (CZ01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • X0 • CZ01 • SWAP01 ≈ SWAP01 • CZ01 • Z1 • X0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel160.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CZ01 • Z1 • X0 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01 • Z0 • SWAP01 • X0 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • CZ01) (X0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

  step5 : SWAP01 • CZ01 • SWAP01 • Z0 • SWAP01 • X0 • SWAP01 ≈ CZ01 • Z0 • SWAP01 • X0 • SWAP01
  step5 = by-assoc-and (under (ε) (Z0 • SWAP01 • X0 • SWAP01) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

  step6 : CZ01 • Z0 • SWAP01 • X0 • SWAP01 ≈ CZ01 • Z0 • X1
  step6 = by-assoc-and (under (CZ01 • Z0) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  proved : X1 • CZ01 ≈ CZ01 • Z0 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel119 where

  step0 : X1 • Z0 • CZ01 ≈ X1 • Z0 • CZ01 • X1 • X1
  step0 = by-assoc-and (under (X1 • Z0 • CZ01) (ε) (sym (elim_X1.proved))) Eq.refl Eq.refl

  step1 : X1 • Z0 • CZ01 • X1 • X1 ≈ X1 • Z0 • CZ01 • X1 • CZ01 • CZ01 • X1
  step1 = by-assoc-and (under (X1 • Z0 • CZ01 • X1) (X1) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

  step2 : X1 • Z0 • CZ01 • X1 • CZ01 • CZ01 • X1 ≈ X1 • Z0 • CZ01 • CZ01 • Z0 • X1 • CZ01 • X1
  step2 = by-assoc-and (under (X1 • Z0 • CZ01) (CZ01 • X1) (drel145.proved)) Eq.refl Eq.refl

  step3 : X1 • Z0 • CZ01 • CZ01 • Z0 • X1 • CZ01 • X1 ≈ X1 • Z0 • Z0 • X1 • CZ01 • X1
  step3 = by-assoc-and (under (X1 • Z0) (Z0 • X1 • CZ01 • X1) (elim_CZ01.proved)) Eq.refl Eq.refl

  step4 : X1 • Z0 • Z0 • X1 • CZ01 • X1 ≈ X1 • X1 • CZ01 • X1
  step4 = by-assoc-and (under (X1) (X1 • CZ01 • X1) (elim_Z0.proved)) Eq.refl Eq.refl

  step5 : X1 • X1 • CZ01 • X1 ≈ CZ01 • X1
  step5 = by-assoc-and (under (ε) (CZ01 • X1) (elim_X1.proved)) Eq.refl Eq.refl

  proved : X1 • Z0 • CZ01 ≈ CZ01 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_Z_c where

  step0 : Z2 ≈ K12 • K12 • Z2
  step0 = by-assoc-and (under (ε) (Z2) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • Z2 ≈ K12 • X2 • K12
  step1 = by-assoc-and (under (K12) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

  step2 : K12 • X2 • K12 ≈ K12 • SWAP12 • X1 • SWAP12 • K12
  step2 = by-assoc-and (under (K12) (K12) (symmetry_X_c.proved)) Eq.refl Eq.refl

  step3 : K12 • SWAP12 • X1 • SWAP12 • K12 ≈ K12 • SWAP12 • X1 • SWAP12 • SWAP12 • K12 • SWAP12
  step3 = by-assoc-and (under (K12 • SWAP12 • X1 • SWAP12) (ε) (symmetry_K_a.proved)) Eq.refl Eq.refl

  step4 : K12 • SWAP12 • X1 • SWAP12 • SWAP12 • K12 • SWAP12 ≈ K12 • SWAP12 • X1 • K12 • SWAP12
  step4 = by-assoc-and (under (K12 • SWAP12 • X1) (K12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step5 : K12 • SWAP12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • SWAP12 • SWAP12 • X1 • K12 • SWAP12
  step5 = by-assoc-and (under (ε) (SWAP12 • X1 • K12 • SWAP12) (symmetry_K_a.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • K12 • SWAP12 • SWAP12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • X1 • K12 • SWAP12
  step6 = by-assoc-and (under (SWAP12 • K12) (X1 • K12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step7 : SWAP12 • K12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • K12 • Z1 • SWAP12
  step7 = by-assoc-and (under (SWAP12 • K12) (SWAP12) (drel137.proved)) Eq.refl Eq.refl

  step8 : SWAP12 • K12 • K12 • Z1 • SWAP12 ≈ SWAP12 • Z1 • SWAP12
  step8 = by-assoc-and (under (SWAP12) (Z1 • SWAP12) (axiom r023)) Eq.refl Eq.refl

  proved : Z2 ≈ SWAP12 • Z1 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel156 where

  step0 : X0 • CZ02 ≈ X0 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (X0) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : X0 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • X0 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (CZ01 • SWAP12) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step2 : SWAP12 • X0 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • Z1 • X0 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (drel160.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • Z1 • X0 • SWAP12 ≈ SWAP12 • CZ01 • Z1 • SWAP12 • X0
  step3 = by-assoc-and (under (SWAP12 • CZ01 • Z1) (ε) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ01 • Z1 • SWAP12 • X0 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • Z1 • SWAP12 • X0
  step4 = by-assoc-and (under (SWAP12 • CZ01) (Z1 • SWAP12 • X0) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • CZ01 • SWAP12 • SWAP12 • Z1 • SWAP12 • X0 ≈ SWAP12 • CZ01 • SWAP12 • Z2 • X0
  step5 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12) (X0) (sym (symmetry_Z_c.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • CZ01 • SWAP12 • Z2 • X0 ≈ CZ02 • Z2 • X0
  step6 = by-assoc-and (under (ε) (Z2 • X0) (sym (axiom r018))) Eq.refl Eq.refl

  proved : X0 • CZ02 ≈ CZ02 • Z2 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel146 where

  step0 : X2 • CZ02 ≈ X2 • SWAP02 • CZ02 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (symmetry_CZ_a.proved)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • CZ02 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CZ02 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • CZ02 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CZ02 • SWAP02 ≈ SWAP02 • X0 • CZ02 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (CZ02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • CZ02 • SWAP02 ≈ SWAP02 • CZ02 • Z2 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel156.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CZ02 • Z2 • X0 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • Z0 • SWAP02 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CZ02) (X0 • SWAP02) (axiom r016)) Eq.refl Eq.refl

  step5 : SWAP02 • CZ02 • SWAP02 • Z0 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • Z0 • X2
  step5 = by-assoc-and (under (SWAP02 • CZ02 • SWAP02 • Z0) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  step6 : SWAP02 • CZ02 • SWAP02 • Z0 • X2 ≈ CZ02 • Z0 • X2
  step6 = by-assoc-and (under (ε) (Z0 • X2) (sym (symmetry_CZ_a.proved))) Eq.refl Eq.refl

  proved : X2 • CZ02 ≈ CZ02 • Z0 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel120 where

  step0 : X2 • Z0 • CZ02 ≈ X2 • Z0 • CZ02 • X2 • X2
  step0 = by-assoc-and (under (X2 • Z0 • CZ02) (ε) (sym (elim_X2.proved))) Eq.refl Eq.refl

  step1 : X2 • Z0 • CZ02 • X2 • X2 ≈ X2 • Z0 • CZ02 • X2 • CZ02 • CZ02 • X2
  step1 = by-assoc-and (under (X2 • Z0 • CZ02 • X2) (X2) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step2 : X2 • Z0 • CZ02 • X2 • CZ02 • CZ02 • X2 ≈ X2 • Z0 • CZ02 • CZ02 • Z0 • X2 • CZ02 • X2
  step2 = by-assoc-and (under (X2 • Z0 • CZ02) (CZ02 • X2) (drel146.proved)) Eq.refl Eq.refl

  step3 : X2 • Z0 • CZ02 • CZ02 • Z0 • X2 • CZ02 • X2 ≈ X2 • Z0 • Z0 • X2 • CZ02 • X2
  step3 = by-assoc-and (under (X2 • Z0) (Z0 • X2 • CZ02 • X2) (elim_CZ02.proved)) Eq.refl Eq.refl

  step4 : X2 • Z0 • Z0 • X2 • CZ02 • X2 ≈ X2 • X2 • CZ02 • X2
  step4 = by-assoc-and (under (X2) (X2 • CZ02 • X2) (elim_Z0.proved)) Eq.refl Eq.refl

  step5 : X2 • X2 • CZ02 • X2 ≈ CZ02 • X2
  step5 = by-assoc-and (under (ε) (CZ02 • X2) (elim_X2.proved)) Eq.refl Eq.refl

  proved : X2 • Z0 • CZ02 ≈ CZ02 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel123 where

  step0 : X0 • Z2 • CZ02 ≈ X0 • Z2 • CZ02 • X0 • X0
  step0 = by-assoc-and (under (X0 • Z2 • CZ02) (ε) (sym (axiom r021))) Eq.refl Eq.refl

  step1 : X0 • Z2 • CZ02 • X0 • X0 ≈ X0 • Z2 • CZ02 • X0 • CZ02 • CZ02 • X0
  step1 = by-assoc-and (under (X0 • Z2 • CZ02 • X0) (X0) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

  step2 : X0 • Z2 • CZ02 • X0 • CZ02 • CZ02 • X0 ≈ X0 • Z2 • CZ02 • CZ02 • Z2 • X0 • CZ02 • X0
  step2 = by-assoc-and (under (X0 • Z2 • CZ02) (CZ02 • X0) (drel156.proved)) Eq.refl Eq.refl

  step3 : X0 • Z2 • CZ02 • CZ02 • Z2 • X0 • CZ02 • X0 ≈ X0 • Z2 • Z2 • X0 • CZ02 • X0
  step3 = by-assoc-and (under (X0 • Z2) (Z2 • X0 • CZ02 • X0) (elim_CZ02.proved)) Eq.refl Eq.refl

  step4 : X0 • Z2 • Z2 • X0 • CZ02 • X0 ≈ X0 • X0 • CZ02 • X0
  step4 = by-assoc-and (under (X0) (X0 • CZ02 • X0) (elim_Z2.proved)) Eq.refl Eq.refl

  step5 : X0 • X0 • CZ02 • X0 ≈ CZ02 • X0
  step5 = by-assoc-and (under (ε) (CZ02 • X0) (axiom r021)) Eq.refl Eq.refl

  proved : X0 • Z2 • CZ02 ≈ CZ02 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_CZ_d where

  step0 : CZ12 ≈ SWAP01 • CZ02 • SWAP01
  step0 = by-assoc-and (under (ε) (ε) (axiom r019)) Eq.refl Eq.refl

  step1 : SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP12 • CZ01 • SWAP12 • SWAP01
  step1 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP12 • CZ01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP01 • SWAP12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP02
  step3 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP01 • CZ01) (ε) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP02 ≈ SWAP02 • CZ01 • SWAP02
  step4 = by-assoc-and (under (ε) (CZ01 • SWAP02) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  proved : CZ12 ≈ SWAP02 • CZ01 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
