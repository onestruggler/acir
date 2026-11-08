{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B001 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X2 ; Z0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r001 ; r003 ; r006 ; r007 ; r008 ; r009 ; r010 ; r011 ; r013 ; r015 ; r016 ; r018 ; r019 ; r020 ; r021 ; r022 ; r023 ; r025 ; r029 ; r030 ; r039 ; r041 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_K_b ; module drel161 ; module elim_CX02 ; module elim_CX10 ; module elim_CX12 ; module elim_CX21 ; module elim_SWAP01 ; module elim_SWAP02 ; module elim_SWAP12 ; module symmetry_CX_d ; module symmetry_CX_f ; module symmetry_CX_g ; module symmetry_CX_h ; module symmetry_CX_i ; module symmetry_SWAP02)

module drel112 where

  step0 : CX01 • CX12 ≈ CX12 • CX12 • CX01 • CX12
  step0 = by-assoc-and (under (ε) (CX01 • CX12) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step1 : CX12 • CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX01 • CX12 • CX01 • CX12
  step1 = by-assoc-and (under (CX12) (CX12 • CX01 • CX12) (sym (axiom r022))) Eq.refl Eq.refl

  step2 : CX12 • CX01 • CX01 • CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX01 • CX12 • CX01 • SWAP12 • CX21 • SWAP12
  step2 = by-assoc-and (under (CX12 • CX01 • CX01 • CX12 • CX01) (ε) (symmetry_CX_d.proved)) Eq.refl Eq.refl

  step3 : CX12 • CX01 • CX01 • CX12 • CX01 • SWAP12 • CX21 • SWAP12 ≈ CX12 • CX01 • CX01 • SWAP12 • CX21 • SWAP12 • CX01 • SWAP12 • CX21 • SWAP12
  step3 = by-assoc-and (under (CX12 • CX01 • CX01) (CX01 • SWAP12 • CX21 • SWAP12) (symmetry_CX_d.proved)) Eq.refl Eq.refl

  step4 : CX12 • CX01 • CX01 • SWAP12 • CX21 • SWAP12 • CX01 • SWAP12 • CX21 • SWAP12 ≈ CX12 • CX01 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12
  step4 = by-assoc-and (under (CX12 • CX01 • CX01 • SWAP12 • CX21) (CX21 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

  step5 : CX12 • CX01 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12
  step5 = by-assoc-and (under (CX12 • CX01) (CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step6 : CX12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • CX21 • SWAP12
  step6 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX21 • CX02 • CX21 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

  step7 : CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12
  step7 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02) (SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step8 : CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • SWAP02 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12
  step8 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02) (CX02 • SWAP02 • CX01 • SWAP02 • SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step9 : CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • SWAP02 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
  step9 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01) (CX01 • SWAP02 • SWAP12) (sym (axiom r029))) Eq.refl Eq.refl

  step10 : CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
  step10 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step11 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • CX20 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
  step11 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (CX01 • CX20 • CX01 • SWAP02 • SWAP12) (sym (axiom r029))) Eq.refl Eq.refl

  step12 : CX12 • CX01 • SWAP12 • SWAP02 • CX20 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • CX21 • SWAP02 • SWAP12
  step12 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (SWAP02 • SWAP12) (sym (axiom r006))) Eq.refl Eq.refl

  step13 : CX12 • CX01 • SWAP12 • SWAP02 • CX21 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 • SWAP12
  step13 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (SWAP02 • SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step14 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP12
  step14 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01) (SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step15 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX01 • SWAP12
  step15 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX01 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step16 : CX12 • CX01 • SWAP12 • CX01 • SWAP12 ≈ CX12 • CX01 • CX02
  step16 = by-assoc-and (under (CX12 • CX01) (ε) (sym (axiom r009))) Eq.refl Eq.refl

  proved : CX01 • CX12 ≈ CX12 • CX01 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (trans step15 (trans step16 (refl)))))))))))))))))

module drel134 where

  step0 : CX02 • CX21 ≈ CX02 • SWAP12 • CX12 • SWAP12
  step0 = by-assoc-and (under (CX02) (ε) (symmetry_CX_g.proved)) Eq.refl Eq.refl

  step1 : CX02 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX12 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CX12 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CX01 • CX12 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX01) (CX12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • CX12 • SWAP12 ≈ SWAP12 • CX12 • CX01 • CX02 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel112.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CX12 • CX01 • CX02 • SWAP12 ≈ SWAP12 • CX12 • CX01 • SWAP12 • CX01 • SWAP12 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • CX12 • CX01) (SWAP12) (axiom r009)) Eq.refl Eq.refl

  step5 : SWAP12 • CX12 • CX01 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ SWAP12 • CX12 • CX01 • SWAP12 • CX01
  step5 = by-assoc-and (under (SWAP12 • CX12 • CX01 • SWAP12 • CX01) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • CX12 • CX01 • SWAP12 • CX01 ≈ SWAP12 • CX12 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX01
  step6 = by-assoc-and (under (SWAP12 • CX12) (CX01 • SWAP12 • CX01) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • CX12 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX01 ≈ SWAP12 • CX12 • SWAP12 • CX02 • CX01
  step7 = by-assoc-and (under (SWAP12 • CX12 • SWAP12) (CX01) (sym (axiom r009))) Eq.refl Eq.refl

  step8 : SWAP12 • CX12 • SWAP12 • CX02 • CX01 ≈ CX21 • CX02 • CX01
  step8 = by-assoc-and (under (ε) (CX02 • CX01) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

  proved : CX02 • CX21 ≈ CX21 • CX02 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel110 where

  step0 : CX21 • CX02 ≈ CX21 • CX02 • CX01 • CX01
  step0 = by-assoc-and (under (CX21 • CX02) (ε) (sym (axiom r022))) Eq.refl Eq.refl

  step1 : CX21 • CX02 • CX01 • CX01 ≈ CX02 • CX21 • CX01
  step1 = by-assoc-and (under (ε) (CX01) (sym (drel134.proved))) Eq.refl Eq.refl

  proved : CX21 • CX02 ≈ CX02 • CX21 • CX01
  proved = trans step0 (trans step1 (refl))

module drel41 where

  step0 : CX01 • CX21 ≈ CX02 • CX02 • CX01 • CX21
  step0 = by-assoc-and (under (ε) (CX01 • CX21) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step1 : CX02 • CX02 • CX01 • CX21 ≈ CX02 • CX21 • CX21 • CX02 • CX01 • CX21
  step1 = by-assoc-and (under (CX02) (CX02 • CX01 • CX21) (sym (elim_CX21.proved))) Eq.refl Eq.refl

  step2 : CX02 • CX21 • CX21 • CX02 • CX01 • CX21 ≈ CX02 • CX21 • CX02 • CX21 • CX21
  step2 = by-assoc-and (under (CX02 • CX21) (CX21) (sym (drel134.proved))) Eq.refl Eq.refl

  step3 : CX02 • CX21 • CX02 • CX21 • CX21 ≈ CX02 • CX21 • CX02
  step3 = by-assoc-and (under (CX02 • CX21 • CX02) (ε) (elim_CX21.proved)) Eq.refl Eq.refl

  step4 : CX02 • CX21 • CX02 ≈ CX02 • CX02 • CX21 • CX01
  step4 = by-assoc-and (under (CX02) (ε) (drel110.proved)) Eq.refl Eq.refl

  step5 : CX02 • CX02 • CX21 • CX01 ≈ CX21 • CX01
  step5 = by-assoc-and (under (ε) (CX21 • CX01) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : CX01 • CX21 ≈ CX21 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module drel165 where

  step0 : CX12 • CZ01 ≈ CX12 • K12 • CX01 • K12
  step0 = by-assoc-and (under (CX12) (ε) (axiom r001)) Eq.refl Eq.refl

  step1 : CX12 • K12 • CX01 • K12 ≈ K12 • CX21 • K12 • K12 • CX01 • K12
  step1 = by-assoc-and (under (ε) (K12 • CX01 • K12) (axiom r007)) Eq.refl Eq.refl

  step2 : K12 • CX21 • K12 • K12 • CX01 • K12 ≈ K12 • CX21 • CX01 • K12
  step2 = by-assoc-and (under (K12 • CX21) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

  step3 : K12 • CX21 • CX01 • K12 ≈ K12 • CX01 • CX21 • K12
  step3 = by-assoc-and (under (K12) (K12) (sym (drel41.proved))) Eq.refl Eq.refl

  step4 : K12 • CX01 • CX21 • K12 ≈ K12 • CX01 • K12 • K12 • CX21 • K12
  step4 = by-assoc-and (under (K12 • CX01) (CX21 • K12) (sym (axiom r023))) Eq.refl Eq.refl

  step5 : K12 • CX01 • K12 • K12 • CX21 • K12 ≈ K12 • CX01 • K12 • CX12
  step5 = by-assoc-and (under (K12 • CX01 • K12) (ε) (sym (axiom r007))) Eq.refl Eq.refl

  step6 : K12 • CX01 • K12 • CX12 ≈ CZ01 • CX12
  step6 = by-assoc-and (under (ε) (CX12) (sym (axiom r001))) Eq.refl Eq.refl

  proved : CX12 • CZ01 ≈ CZ01 • CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module elim_CZ01 where

  step0 : CZ01 • CZ01 ≈ CZ01 • K12 • CX01 • K12
  step0 = by-assoc-and (under (CZ01) (ε) (axiom r001)) Eq.refl Eq.refl

  step1 : CZ01 • K12 • CX01 • K12 ≈ K12 • CX01 • K12 • K12 • CX01 • K12
  step1 = by-assoc-and (under (ε) (K12 • CX01 • K12) (axiom r001)) Eq.refl Eq.refl

  step2 : K12 • CX01 • K12 • K12 • CX01 • K12 ≈ K12 • CX01 • CX01 • K12
  step2 = by-assoc-and (under (K12 • CX01) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

  step3 : K12 • CX01 • CX01 • K12 ≈ K12 • K12
  step3 = by-assoc-and (under (K12) (K12) (axiom r022)) Eq.refl Eq.refl

  step4 : K12 • K12 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CZ01 • CZ01 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_CZ02 where

  step0 : CZ02 • CZ02 ≈ CZ02 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (CZ02) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : CZ02 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • CZ01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ01) (CZ01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ01 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (elim_CZ01.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP12 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  proved : CZ02 • CZ02 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_CZ12 where

  step0 : CZ12 • CZ12 ≈ CZ12 • SWAP01 • CZ02 • SWAP01
  step0 = by-assoc-and (under (CZ12) (ε) (axiom r019)) Eq.refl Eq.refl

  step1 : CZ12 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • CZ02 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CZ02 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • CZ02 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CZ02) (CZ02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CZ02 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (elim_CZ02.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CZ12 • CZ12 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module symmetry_SWAP12_alt where

  step0 : K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • SWAP12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
  step0 = by-assoc-and (under (ε) (K12 • CZ12 • K12 • CZ12 • K12 • CZ12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : SWAP12 • SWAP12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
  step1 = by-assoc-and (under (SWAP12) (K12 • CZ12 • K12 • CZ12 • K12 • CZ12) (axiom r020)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 • K12 • CZ12
  step2 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12) (CZ12 • K12 • CZ12 • K12 • CZ12) (axiom r023)) Eq.refl Eq.refl

  step3 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12
  step3 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12 • K12) (K12 • CZ12 • K12 • CZ12) (elim_CZ12.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12
  step4 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12) (CZ12 • K12 • CZ12) (axiom r023)) Eq.refl Eq.refl

  step5 : SWAP12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • K12 • CZ12
  step5 = by-assoc-and (under (SWAP12 • CZ12 • K12) (K12 • CZ12) (elim_CZ12.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • CZ12 • K12 • K12 • CZ12 ≈ SWAP12 • CZ12 • CZ12
  step6 = by-assoc-and (under (SWAP12 • CZ12) (CZ12) (axiom r023)) Eq.refl Eq.refl

  step7 : SWAP12 • CZ12 • CZ12 ≈ SWAP12
  step7 = by-assoc-and (under (SWAP12) (ε) (elim_CZ12.proved)) Eq.refl Eq.refl

  proved : K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module symmetry_CZ_e where

  step0 : CZ12 ≈ SWAP12 • SWAP12 • CZ12
  step0 = by-assoc-and (under (ε) (CZ12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : SWAP12 • SWAP12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
  step1 = by-assoc-and (under (SWAP12) (CZ12) (axiom r020)) Eq.refl Eq.refl

  step2 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CZ12) (ε) (symmetry_SWAP12_alt.proved)) Eq.refl Eq.refl

  proved : CZ12 ≈ SWAP12 • CZ12 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (refl)))

module symmetry_CZ_a where

  step0 : CZ02 ≈ CZ02 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (CZ02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CZ02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r019))) Eq.refl Eq.refl

  step3 : SWAP01 • CZ12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP01 • SWAP12 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (axiom r019)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP02
  step5 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP01 • CZ02) (ε) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  step6 : SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02
  step6 = by-assoc-and (under (ε) (CZ02 • SWAP02) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  proved : CZ02 ≈ SWAP02 • CZ02 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_CX_b where

  step0 : CX10 ≈ CX10 • SWAP02 • SWAP02
  step0 = by-assoc-and (under (CX10) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step1 : CX10 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (ε) (CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • CX12 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

  proved : CX10 ≈ SWAP02 • CX12 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (refl)))

module symmetry_SWAP01 where

  step0 : SWAP01 ≈ CX10 • CX10 • SWAP01
  step0 = by-assoc-and (under (ε) (SWAP01) (sym (elim_CX10.proved))) Eq.refl Eq.refl

  step1 : CX10 • CX10 • SWAP01 ≈ CX10 • CX01 • CX10
  step1 = by-assoc-and (under (CX10) (ε) (sym (drel161.proved))) Eq.refl Eq.refl

  step2 : CX10 • CX01 • CX10 ≈ CX10 • CX01 • SWAP02 • CX12 • SWAP02
  step2 = by-assoc-and (under (CX10 • CX01) (ε) (symmetry_CX_b.proved)) Eq.refl Eq.refl

  step3 : CX10 • CX01 • SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • CX01 • SWAP02 • CX12 • SWAP02
  step3 = by-assoc-and (under (ε) (CX01 • SWAP02 • CX12 • SWAP02) (symmetry_CX_b.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • CX12 • SWAP02 • CX01 • SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • CX21 • CX12 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • CX12) (CX12 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • CX12 • CX21 • CX12 • SWAP02 ≈ SWAP02 • SWAP12 • SWAP02
  step5 = by-assoc-and (under (SWAP02) (SWAP02) (sym (axiom r008))) Eq.refl Eq.refl

  proved : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_CX_j where

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

module symmetry_SWAP01_alt where

  step0 : SWAP01 ≈ CX01 • CX10 • CX01
  step0 = by-assoc-and (under (ε) (ε) (axiom r013)) Eq.refl Eq.refl

  step1 : CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (CX01 • CX10 • CX01) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : CX01 • CX10 • CX01 • SWAP12 • SWAP12 ≈ CX01 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12
  step2 = by-assoc-and (under (CX01 • CX10) (CX01 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step3 : CX01 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12
  step3 = by-assoc-and (under (CX01) (CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step4 : CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12
  step4 = by-assoc-and (under (ε) (CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX02 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12) (SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX02 • SWAP12 ≈ SWAP12 • SWAP12 • CX01 • SWAP12 • CX20 • CX02 • SWAP12
  step6 = by-assoc-and (under (SWAP12 • SWAP12 • CX01 • SWAP12) (CX02 • SWAP12) (sym (symmetry_CX_j.proved))) Eq.refl Eq.refl

  step7 : SWAP12 • SWAP12 • CX01 • SWAP12 • CX20 • CX02 • SWAP12 ≈ SWAP12 • CX02 • CX20 • CX02 • SWAP12
  step7 = by-assoc-and (under (SWAP12) (CX20 • CX02 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

  step8 : SWAP12 • CX02 • CX20 • CX02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12
  step8 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r010))) Eq.refl Eq.refl

  proved : SWAP01 ≈ SWAP12 • SWAP02 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module symmetry_CZ_b where

  step0 : CZ01 ≈ CZ01 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (CZ01) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (ε) (CZ01 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CZ02 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r018))) Eq.refl Eq.refl

  step3 : SWAP12 • CZ02 • SWAP12 ≈ SWAP12 • SWAP02 • CZ02 • SWAP02 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (symmetry_CZ_a.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP02 • CZ02 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP12 • SWAP02 • SWAP12
  step4 = by-assoc-and (under (SWAP12 • SWAP02) (SWAP02 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP01
  step5 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • CZ01) (ε) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01
  step6 = by-assoc-and (under (ε) (CZ01 • SWAP01) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

  proved : CZ01 ≈ SWAP01 • CZ01 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel166 where

  step0 : CX01 • CZ02 ≈ CX01 • SWAP12 • CZ01 • SWAP12
  step0 = by-assoc-and (under (CX01) (ε) (axiom r018)) Eq.refl Eq.refl

  step1 : CX01 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12
  step1 = by-assoc-and (under (ε) (CX01 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step2 : SWAP12 • SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX02 • CZ01 • SWAP12
  step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

  step3 : SWAP12 • CX02 • CZ01 • SWAP12 ≈ SWAP12 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12
  step3 = by-assoc-and (under (SWAP12 • CX02) (SWAP12) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP01 • SWAP01 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CX12 • CZ01 • SWAP01 • SWAP12
  step5 = by-assoc-and (under (SWAP12 • SWAP01) (CZ01 • SWAP01 • SWAP12) (sym (axiom r030))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP01 • CX12 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • CX12 • SWAP01 • SWAP12
  step6 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (drel165.proved)) Eq.refl Eq.refl

  step7 : SWAP12 • SWAP01 • CZ01 • CX12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 • SWAP01 • SWAP12
  step7 = by-assoc-and (under (SWAP12 • SWAP01 • CZ01) (SWAP01 • SWAP12) (axiom r030)) Eq.refl Eq.refl

  step8 : SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP12
  step8 = by-assoc-and (under (SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02) (SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step9 : SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP12 ≈ SWAP12 • CZ01 • CX02 • SWAP12
  step9 = by-assoc-and (under (SWAP12) (CX02 • SWAP12) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

  step10 : SWAP12 • CZ01 • CX02 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP12
  step10 = by-assoc-and (under (SWAP12 • CZ01) (SWAP12) (axiom r009)) Eq.refl Eq.refl

  step11 : SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX01
  step11 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12 • CX01) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step12 : SWAP12 • CZ01 • SWAP12 • CX01 ≈ CZ02 • CX01
  step12 = by-assoc-and (under (ε) (CX01) (sym (axiom r018))) Eq.refl Eq.refl

  proved : CX01 • CZ02 ≈ CZ02 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))

module drel163 where

  step0 : CX02 • CZ01 ≈ CX02 • CZ01 • SWAP12 • SWAP12
  step0 = by-assoc-and (under (CX02 • CZ01) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

  step1 : CX02 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • SWAP12
  step1 = by-assoc-and (under (ε) (CZ01 • SWAP12 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CX01 • CZ02 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX01) (SWAP12) (sym (axiom r018))) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • CZ02 • SWAP12 ≈ SWAP12 • CZ02 • CX01 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel166.proved)) Eq.refl Eq.refl

  step4 : SWAP12 • CZ02 • CX01 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12
  step4 = by-assoc-and (under (SWAP12) (CX01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

  step5 : SWAP12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • CX02
  step5 = by-assoc-and (under (SWAP12 • SWAP12 • CZ01) (ε) (sym (axiom r009))) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP12 • CZ01 • CX02 ≈ CZ01 • CX02
  step6 = by-assoc-and (under (ε) (CZ01 • CX02) (elim_SWAP12.proved)) Eq.refl Eq.refl

  proved : CX02 • CZ01 ≈ CZ01 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel9 where

  step0 : CX01 • CX02 ≈ CX21 • CX21 • CX01 • CX02
  step0 = by-assoc-and (under (ε) (CX01 • CX02) (sym (elim_CX21.proved))) Eq.refl Eq.refl

  step1 : CX21 • CX21 • CX01 • CX02 ≈ CX21 • CX02 • CX02 • CX21 • CX01 • CX02
  step1 = by-assoc-and (under (CX21) (CX21 • CX01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

  step2 : CX21 • CX02 • CX02 • CX21 • CX01 • CX02 ≈ CX21 • CX02 • CX21 • CX02 • CX02
  step2 = by-assoc-and (under (CX21 • CX02) (CX02) (sym (drel110.proved))) Eq.refl Eq.refl

  step3 : CX21 • CX02 • CX21 • CX02 • CX02 ≈ CX21 • CX02 • CX21
  step3 = by-assoc-and (under (CX21 • CX02 • CX21) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  step4 : CX21 • CX02 • CX21 ≈ CX21 • CX21 • CX02 • CX01
  step4 = by-assoc-and (under (CX21) (ε) (drel134.proved)) Eq.refl Eq.refl

  step5 : CX21 • CX21 • CX02 • CX01 ≈ CX02 • CX01
  step5 = by-assoc-and (under (ε) (CX02 • CX01) (elim_CX21.proved)) Eq.refl Eq.refl

  proved : CX01 • CX02 ≈ CX02 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module bifunct_Z_CX_b where

  step0 : Z0 • CX12 ≈ CZ01 • CX01 • CZ01 • CX01 • CX12
  step0 = by-assoc-and (under (ε) (CX12) (axiom r003)) Eq.refl Eq.refl

  step1 : CZ01 • CX01 • CZ01 • CX01 • CX12 ≈ CZ01 • CX01 • CZ01 • CX12 • CX01 • CX02
  step1 = by-assoc-and (under (CZ01 • CX01 • CZ01) (ε) (drel112.proved)) Eq.refl Eq.refl

  step2 : CZ01 • CX01 • CZ01 • CX12 • CX01 • CX02 ≈ CZ01 • CX01 • CX12 • CZ01 • CX01 • CX02
  step2 = by-assoc-and (under (CZ01 • CX01) (CX01 • CX02) (sym (drel165.proved))) Eq.refl Eq.refl

  step3 : CZ01 • CX01 • CX12 • CZ01 • CX01 • CX02 ≈ CZ01 • CX12 • CX01 • CX02 • CZ01 • CX01 • CX02
  step3 = by-assoc-and (under (CZ01) (CZ01 • CX01 • CX02) (drel112.proved)) Eq.refl Eq.refl

  step4 : CZ01 • CX12 • CX01 • CX02 • CZ01 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CX02 • CZ01 • CX01 • CX02
  step4 = by-assoc-and (under (ε) (CX01 • CX02 • CZ01 • CX01 • CX02) (sym (drel165.proved))) Eq.refl Eq.refl

  step5 : CX12 • CZ01 • CX01 • CX02 • CZ01 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX02 • CX01 • CX02
  step5 = by-assoc-and (under (CX12 • CZ01 • CX01) (CX01 • CX02) (drel163.proved)) Eq.refl Eq.refl

  step6 : CX12 • CZ01 • CX01 • CZ01 • CX02 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX01 • CX02 • CX02
  step6 = by-assoc-and (under (CX12 • CZ01 • CX01 • CZ01) (CX02) (sym (drel9.proved))) Eq.refl Eq.refl

  step7 : CX12 • CZ01 • CX01 • CZ01 • CX01 • CX02 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX01
  step7 = by-assoc-and (under (CX12 • CZ01 • CX01 • CZ01 • CX01) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  step8 : CX12 • CZ01 • CX01 • CZ01 • CX01 ≈ CX12 • Z0
  step8 = by-assoc-and (under (CX12) (ε) (sym (axiom r003))) Eq.refl Eq.refl

  proved : Z0 • CX12 ≈ CX12 • Z0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel64 where

  step0 : X2 • K12 ≈ SWAP02 • X0 • SWAP02 • K12
  step0 = by-assoc-and (under (ε) (K12) (axiom r015)) Eq.refl Eq.refl

  step1 : SWAP02 • X0 • SWAP02 • K12 ≈ SWAP02 • X0 • SWAP02 • K12 • SWAP02 • SWAP02
  step1 = by-assoc-and (under (SWAP02 • X0 • SWAP02 • K12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • K12 • SWAP02 • SWAP02 ≈ SWAP02 • X0 • K01 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (SWAP02) (sym (axiom r011))) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • K01 • SWAP02 ≈ SWAP02 • K01 • Z0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (sym (axiom r041))) Eq.refl Eq.refl

  step4 : SWAP02 • K01 • Z0 • SWAP02 ≈ SWAP02 • SWAP02 • K12 • SWAP02 • Z0 • SWAP02
  step4 = by-assoc-and (under (SWAP02) (Z0 • SWAP02) (axiom r011)) Eq.refl Eq.refl

  step5 : SWAP02 • SWAP02 • K12 • SWAP02 • Z0 • SWAP02 ≈ K12 • SWAP02 • Z0 • SWAP02
  step5 = by-assoc-and (under (ε) (K12 • SWAP02 • Z0 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step6 : K12 • SWAP02 • Z0 • SWAP02 ≈ K12 • Z2
  step6 = by-assoc-and (under (K12) (ε) (sym (axiom r016))) Eq.refl Eq.refl

  proved : X2 • K12 ≈ K12 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module elim_X2 where

  step0 : X2 • X2 ≈ X2 • SWAP02 • X0 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (axiom r015)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • X0 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • X0 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • X0 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (X0 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • X0 • SWAP02 ≈ SWAP02 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r021)) Eq.refl Eq.refl

  step4 : SWAP02 • SWAP02 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : X2 • X2 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_Z0 where

  step0 : Z0 • Z0 ≈ K01 • K01 • Z0 • Z0
  step0 = by-assoc-and (under (ε) (Z0 • Z0) (sym (axiom r025))) Eq.refl Eq.refl

  step1 : K01 • K01 • Z0 • Z0 ≈ K01 • X0 • K01 • Z0
  step1 = by-assoc-and (under (K01) (Z0) (axiom r041)) Eq.refl Eq.refl

  step2 : K01 • X0 • K01 • Z0 ≈ K01 • X0 • X0 • K01
  step2 = by-assoc-and (under (K01 • X0) (ε) (axiom r041)) Eq.refl Eq.refl

  step3 : K01 • X0 • X0 • K01 ≈ K01 • K01
  step3 = by-assoc-and (under (K01) (K01) (axiom r021)) Eq.refl Eq.refl

  step4 : K01 • K01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (axiom r025)) Eq.refl Eq.refl

  proved : Z0 • Z0 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_Z2 where

  step0 : Z2 • Z2 ≈ Z2 • SWAP02 • Z0 • SWAP02
  step0 = by-assoc-and (under (Z2) (ε) (axiom r016)) Eq.refl Eq.refl

  step1 : Z2 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • Z0 • SWAP02 • SWAP02 • Z0 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • Z0 • SWAP02) (axiom r016)) Eq.refl Eq.refl

  step2 : SWAP02 • Z0 • SWAP02 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • Z0 • Z0 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • Z0) (Z0 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • Z0 • Z0 • SWAP02 ≈ SWAP02 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (elim_Z0.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • SWAP02 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  proved : Z2 • Z2 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel66 where

  step0 : K12 • X2 ≈ K12 • X2 • K12 • K12
  step0 = by-assoc-and (under (K12 • X2) (ε) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • X2 • K12 • K12 ≈ K12 • X2 • K12 • Z2 • Z2 • K12
  step1 = by-assoc-and (under (K12 • X2 • K12) (K12) (sym (elim_Z2.proved))) Eq.refl Eq.refl

  step2 : K12 • X2 • K12 • Z2 • Z2 • K12 ≈ K12 • X2 • X2 • K12 • Z2 • K12
  step2 = by-assoc-and (under (K12 • X2) (Z2 • K12) (sym (drel64.proved))) Eq.refl Eq.refl

  step3 : K12 • X2 • X2 • K12 • Z2 • K12 ≈ K12 • K12 • Z2 • K12
  step3 = by-assoc-and (under (K12) (K12 • Z2 • K12) (elim_X2.proved)) Eq.refl Eq.refl

  step4 : K12 • K12 • Z2 • K12 ≈ Z2 • K12
  step4 = by-assoc-and (under (ε) (Z2 • K12) (axiom r023)) Eq.refl Eq.refl

  proved : K12 • X2 ≈ Z2 • K12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_Z_K_b where

  step0 : Z2 • K01 ≈ Z2 • K12 • K12 • K01
  step0 = by-assoc-and (under (Z2) (K01) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : Z2 • K12 • K12 • K01 ≈ K12 • X2 • K12 • K01
  step1 = by-assoc-and (under (ε) (K12 • K01) (sym (drel66.proved))) Eq.refl Eq.refl

  step2 : K12 • X2 • K12 • K01 ≈ K12 • X2 • K01 • K12
  step2 = by-assoc-and (under (K12 • X2) (ε) (sym (axiom r039))) Eq.refl Eq.refl

  step3 : K12 • X2 • K01 • K12 ≈ K12 • K01 • X2 • K12
  step3 = by-assoc-and (under (K12) (K12) (bifunct_X_K_b.proved)) Eq.refl Eq.refl

  step4 : K12 • K01 • X2 • K12 ≈ K01 • K12 • X2 • K12
  step4 = by-assoc-and (under (ε) (X2 • K12) (sym (axiom r039))) Eq.refl Eq.refl

  step5 : K01 • K12 • X2 • K12 ≈ K01 • Z2 • K12 • K12
  step5 = by-assoc-and (under (K01) (K12) (drel66.proved)) Eq.refl Eq.refl

  step6 : K01 • Z2 • K12 • K12 ≈ K01 • Z2
  step6 = by-assoc-and (under (K01 • Z2) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : Z2 • K01 ≈ K01 • Z2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
