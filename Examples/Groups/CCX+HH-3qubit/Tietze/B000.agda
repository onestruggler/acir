{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.B000 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; K01 ; K12 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r002 ; r005 ; r007 ; r008 ; r009 ; r010 ; r011 ; r012 ; r013 ; r014 ; r015 ; r017 ; r021 ; r022 ; r023 ; r024 ; r025 ; r026 ; r027 ; r028 ; r029 ; r030 ; r031 ; r035 ; r042 ; refl ; sym ; trans ; under ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1

module drel46 where

  step0 : K12 • CX21 ≈ K12 • CX21 • K12 • K12
  step0 = by-assoc-and (under (K12 • CX21) (ε) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • CX21 • K12 • K12 ≈ CX12 • K12
  step1 = by-assoc-and (under (ε) (K12) (sym (axiom r007))) Eq.refl Eq.refl

  proved : K12 • CX21 ≈ CX12 • K12
  proved = trans step0 (trans step1 (refl))

module bifunct_X_CX_b where

  step0 : CX21 • X0 ≈ K12 • K12 • CX21 • X0
  step0 = by-assoc-and (under (ε) (CX21 • X0) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CX21 • X0 ≈ K12 • CX12 • K12 • X0
  step1 = by-assoc-and (under (K12) (X0) (drel46.proved)) Eq.refl Eq.refl

  step2 : K12 • CX12 • K12 • X0 ≈ K12 • CX12 • X0 • K12
  step2 = by-assoc-and (under (K12 • CX12) (ε) (sym (axiom r027))) Eq.refl Eq.refl

  step3 : K12 • CX12 • X0 • K12 ≈ K12 • X0 • CX12 • K12
  step3 = by-assoc-and (under (K12) (K12) (axiom r026)) Eq.refl Eq.refl

  step4 : K12 • X0 • CX12 • K12 ≈ X0 • K12 • CX12 • K12
  step4 = by-assoc-and (under (ε) (CX12 • K12) (sym (axiom r027))) Eq.refl Eq.refl

  step5 : X0 • K12 • CX12 • K12 ≈ X0 • K12 • K12 • CX21
  step5 = by-assoc-and (under (X0 • K12) (ε) (sym (drel46.proved))) Eq.refl Eq.refl

  step6 : X0 • K12 • K12 • CX21 ≈ X0 • CX21
  step6 = by-assoc-and (under (X0) (CX21) (axiom r023)) Eq.refl Eq.refl

  proved : CX21 • X0 ≈ X0 • CX21
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel128 where

  step0 : K12 • CCX01 ≈ K12 • K12 • CCX02 • K12
  step0 = by-assoc-and (under (K12) (ε) (axiom r017)) Eq.refl Eq.refl

  step1 : K12 • K12 • CCX02 • K12 ≈ CCX02 • K12
  step1 = by-assoc-and (under (ε) (CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

  proved : K12 • CCX01 ≈ CCX02 • K12
  proved = trans step0 (trans step1 (refl))

module drel127 where

  step0 : X0 • CCX02 ≈ X0 • CCX02 • K12 • K12
  step0 = by-assoc-and (under (X0 • CCX02) (ε) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : X0 • CCX02 • K12 • K12 ≈ X0 • K12 • CCX01 • K12
  step1 = by-assoc-and (under (X0) (K12) (sym (drel128.proved))) Eq.refl Eq.refl

  step2 : X0 • K12 • CCX01 • K12 ≈ K12 • X0 • CCX01 • K12
  step2 = by-assoc-and (under (ε) (CCX01 • K12) (axiom r027)) Eq.refl Eq.refl

  step3 : K12 • X0 • CCX01 • K12 ≈ K12 • CCX01 • CX12 • X0 • K12
  step3 = by-assoc-and (under (K12) (K12) (axiom r042)) Eq.refl Eq.refl

  step4 : K12 • CCX01 • CX12 • X0 • K12 ≈ CCX02 • K12 • CX12 • X0 • K12
  step4 = by-assoc-and (under (ε) (CX12 • X0 • K12) (drel128.proved)) Eq.refl Eq.refl

  step5 : CCX02 • K12 • CX12 • X0 • K12 ≈ CCX02 • K12 • K12 • CX21 • K12 • X0 • K12
  step5 = by-assoc-and (under (CCX02 • K12) (X0 • K12) (axiom r007)) Eq.refl Eq.refl

  step6 : CCX02 • K12 • K12 • CX21 • K12 • X0 • K12 ≈ CCX02 • CX21 • K12 • X0 • K12
  step6 = by-assoc-and (under (CCX02) (CX21 • K12 • X0 • K12) (axiom r023)) Eq.refl Eq.refl

  step7 : CCX02 • CX21 • K12 • X0 • K12 ≈ CCX02 • CX21 • K12 • K12 • X0
  step7 = by-assoc-and (under (CCX02 • CX21 • K12) (ε) (axiom r027)) Eq.refl Eq.refl

  step8 : CCX02 • CX21 • K12 • K12 • X0 ≈ CCX02 • CX21 • X0
  step8 = by-assoc-and (under (CCX02 • CX21) (X0) (axiom r023)) Eq.refl Eq.refl

  proved : X0 • CCX02 ≈ CCX02 • CX21 • X0
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module elim_CX10 where

  step0 : CX10 • CX10 ≈ CX10 • K01 • CX01 • K01
  step0 = by-assoc-and (under (CX10) (ε) (axiom r012)) Eq.refl Eq.refl

  step1 : CX10 • K01 • CX01 • K01 ≈ K01 • CX01 • K01 • K01 • CX01 • K01
  step1 = by-assoc-and (under (ε) (K01 • CX01 • K01) (axiom r012)) Eq.refl Eq.refl

  step2 : K01 • CX01 • K01 • K01 • CX01 • K01 ≈ K01 • CX01 • CX01 • K01
  step2 = by-assoc-and (under (K01 • CX01) (CX01 • K01) (axiom r025)) Eq.refl Eq.refl

  step3 : K01 • CX01 • CX01 • K01 ≈ K01 • K01
  step3 = by-assoc-and (under (K01) (K01) (axiom r022)) Eq.refl Eq.refl

  step4 : K01 • K01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (axiom r025)) Eq.refl Eq.refl

  proved : CX10 • CX10 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_SWAP01 where

  step0 : SWAP01 • SWAP01 ≈ SWAP01 • CX01 • CX10 • CX01
  step0 = by-assoc-and (under (SWAP01) (ε) (axiom r013)) Eq.refl Eq.refl

  step1 : SWAP01 • CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01 • CX01 • CX10 • CX01
  step1 = by-assoc-and (under (ε) (CX01 • CX10 • CX01) (axiom r013)) Eq.refl Eq.refl

  step2 : CX01 • CX10 • CX01 • CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX10 • CX01
  step2 = by-assoc-and (under (CX01 • CX10) (CX10 • CX01) (axiom r022)) Eq.refl Eq.refl

  step3 : CX01 • CX10 • CX10 • CX01 ≈ CX01 • CX01
  step3 = by-assoc-and (under (CX01) (CX01) (elim_CX10.proved)) Eq.refl Eq.refl

  step4 : CX01 • CX01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (axiom r022)) Eq.refl Eq.refl

  proved : SWAP01 • SWAP01 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_CCX1 where

  step0 : CCX02 • CCX02 ≈ CCX02 • SWAP01 • CCX12 • SWAP01
  step0 = by-assoc-and (under (CCX02) (ε) (axiom r014)) Eq.refl Eq.refl

  step1 : CCX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CCX12 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step2 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CCX12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CCX12) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CCX12 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r024)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP01 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CCX02 • CCX02 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_CX12_lemma where

  step0 : K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • SWAP01 • CCX12 • SWAP01 • K12
  step0 = by-assoc-and (under (K12 • X0 • CCX02 • X0) (K12) (axiom r014)) Eq.refl Eq.refl

  step1 : K12 • X0 • CCX02 • X0 • SWAP01 • CCX12 • SWAP01 • K12 ≈ K12 • X0 • SWAP01 • CCX12 • SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • K12
  step1 = by-assoc-and (under (K12 • X0) (X0 • SWAP01 • CCX12 • SWAP01 • K12) (axiom r014)) Eq.refl Eq.refl

  step2 : K12 • X0 • SWAP01 • CCX12 • SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • K12 ≈ K12 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12
  step2 = by-assoc-and (under (K12 • X0 • SWAP01 • CCX12) (CCX12 • SWAP01 • K12) (sym (axiom r028))) Eq.refl Eq.refl

  step3 : K12 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • SWAP01 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12
  step3 = by-assoc-and (under (K12) (X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step4 : K12 • SWAP01 • SWAP01 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • X1 • CCX12 • X1 • CCX12 • SWAP01 • K12
  step4 = by-assoc-and (under (K12 • SWAP01) (CCX12 • X1 • CCX12 • SWAP01 • K12) (sym (axiom r028))) Eq.refl Eq.refl

  step5 : K12 • SWAP01 • X1 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • CX20 • SWAP01 • K12
  step5 = by-assoc-and (under (K12 • SWAP01) (SWAP01 • K12) (sym (axiom r005))) Eq.refl Eq.refl

  step6 : K12 • SWAP01 • CX20 • SWAP01 • K12 ≈ K12 • CX21 • K12
  step6 = by-assoc-and (under (K12) (K12) (sym (axiom r031))) Eq.refl Eq.refl

  step7 : K12 • CX21 • K12 ≈ CX12
  step7 = by-assoc-and (under (ε) (ε) (sym (axiom r007))) Eq.refl Eq.refl

  proved : K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ CX12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module elim_CX12 where

  step0 : CX12 • CX12 ≈ CX12 • K12 • X0 • CCX02 • X0 • CCX02 • K12
  step0 = by-assoc-and (under (CX12) (ε) (sym (elim_CX12_lemma.proved))) Eq.refl Eq.refl

  step1 : CX12 • K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • K12 • K12 • X0 • CCX02 • X0 • CCX02 • K12
  step1 = by-assoc-and (under (ε) (K12 • X0 • CCX02 • X0 • CCX02 • K12) (sym (elim_CX12_lemma.proved))) Eq.refl Eq.refl

  step2 : K12 • X0 • CCX02 • X0 • CCX02 • K12 • K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • K12
  step2 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02) (X0 • CCX02 • X0 • CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

  step3 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • CCX02 • CX21 • X0 • K12
  step3 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02) (K12) (drel127.proved)) Eq.refl Eq.refl

  step4 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • CCX02 • CX21 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CX21 • X0 • K12
  step4 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02 • X0) (CX21 • X0 • K12) (elim_CCX1.proved)) Eq.refl Eq.refl

  step5 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CX21 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • CX21 • X0 • X0 • K12
  step5 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02) (X0 • K12) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

  step6 : K12 • X0 • CCX02 • X0 • CCX02 • CX21 • X0 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • X0 • CCX02 • X0 • K12
  step6 = by-assoc-and (under (K12 • X0 • CCX02 • X0) (X0 • K12) (sym (drel127.proved))) Eq.refl Eq.refl

  step7 : K12 • X0 • CCX02 • X0 • X0 • CCX02 • X0 • K12 ≈ K12 • X0 • CCX02 • CCX02 • X0 • K12
  step7 = by-assoc-and (under (K12 • X0 • CCX02) (CCX02 • X0 • K12) (axiom r021)) Eq.refl Eq.refl

  step8 : K12 • X0 • CCX02 • CCX02 • X0 • K12 ≈ K12 • X0 • X0 • K12
  step8 = by-assoc-and (under (K12 • X0) (X0 • K12) (elim_CCX1.proved)) Eq.refl Eq.refl

  step9 : K12 • X0 • X0 • K12 ≈ K12 • K12
  step9 = by-assoc-and (under (K12) (K12) (axiom r021)) Eq.refl Eq.refl

  step10 : K12 • K12 ≈ ε
  step10 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CX12 • CX12 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))

module elim_CX21 where

  step0 : CX21 • CX21 ≈ K12 • K12 • CX21 • CX21
  step0 = by-assoc-and (under (ε) (CX21 • CX21) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CX21 • CX21 ≈ K12 • CX12 • K12 • CX21
  step1 = by-assoc-and (under (K12) (CX21) (drel46.proved)) Eq.refl Eq.refl

  step2 : K12 • CX12 • K12 • CX21 ≈ K12 • CX12 • CX12 • K12
  step2 = by-assoc-and (under (K12 • CX12) (ε) (drel46.proved)) Eq.refl Eq.refl

  step3 : K12 • CX12 • CX12 • K12 ≈ K12 • K12
  step3 = by-assoc-and (under (K12) (K12) (elim_CX12.proved)) Eq.refl Eq.refl

  step4 : K12 • K12 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

  proved : CX21 • CX21 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_SWAP12 where

  step0 : SWAP12 • SWAP12 ≈ SWAP12 • CX12 • CX21 • CX12
  step0 = by-assoc-and (under (SWAP12) (ε) (axiom r008)) Eq.refl Eq.refl

  step1 : SWAP12 • CX12 • CX21 • CX12 ≈ CX12 • CX21 • CX12 • CX12 • CX21 • CX12
  step1 = by-assoc-and (under (ε) (CX12 • CX21 • CX12) (axiom r008)) Eq.refl Eq.refl

  step2 : CX12 • CX21 • CX12 • CX12 • CX21 • CX12 ≈ CX12 • CX21 • CX21 • CX12
  step2 = by-assoc-and (under (CX12 • CX21) (CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

  step3 : CX12 • CX21 • CX21 • CX12 ≈ CX12 • CX12
  step3 = by-assoc-and (under (CX12) (CX12) (elim_CX21.proved)) Eq.refl Eq.refl

  step4 : CX12 • CX12 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

  proved : SWAP12 • SWAP12 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module elim_CX02 where

  step0 : CX02 • CX02 ≈ CX02 • SWAP12 • CX01 • SWAP12
  step0 = by-assoc-and (under (CX02) (ε) (axiom r009)) Eq.refl Eq.refl

  step1 : CX02 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12
  step1 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CX01 • SWAP12
  step2 = by-assoc-and (under (SWAP12 • CX01) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

  step3 : SWAP12 • CX01 • CX01 • SWAP12 ≈ SWAP12 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r022)) Eq.refl Eq.refl

  step4 : SWAP12 • SWAP12 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

  proved : CX02 • CX02 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel131 where

  step0 : X1 • CCX12 ≈ X1 • CCX12 • SWAP01 • SWAP01
  step0 = by-assoc-and (under (X1 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step1 : X1 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r028)) Eq.refl Eq.refl

  step2 : SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • CCX02 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

  step3 : SWAP01 • X0 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CX21 • X0 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel127.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • CCX02 • CX21 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CX21 • X0 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (CX21 • X0 • SWAP01) (axiom r014)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CX21 • X0 • SWAP01 ≈ CCX12 • SWAP01 • CX21 • X0 • SWAP01
  step5 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CX21 • X0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : CCX12 • SWAP01 • CX21 • X0 • SWAP01 ≈ CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • X0 • SWAP01
  step6 = by-assoc-and (under (CCX12 • SWAP01) (X0 • SWAP01) (axiom r031)) Eq.refl Eq.refl

  step7 : CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • X0 • SWAP01 ≈ CCX12 • SWAP01 • SWAP01 • CX20 • X1
  step7 = by-assoc-and (under (CCX12 • SWAP01 • SWAP01 • CX20) (ε) (sym (axiom r028))) Eq.refl Eq.refl

  step8 : CCX12 • SWAP01 • SWAP01 • CX20 • X1 ≈ CCX12 • CX20 • X1
  step8 = by-assoc-and (under (CCX12) (CX20 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : X1 • CCX12 ≈ CCX12 • CX20 • X1
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module drel162 where

  step0 : X0 • CX01 ≈ X0 • CX01 • X0 • X0
  step0 = by-assoc-and (under (X0 • CX01) (ε) (sym (axiom r021))) Eq.refl Eq.refl

  step1 : X0 • CX01 • X0 • X0 ≈ CX01 • CX01 • X0 • CX01 • X0 • X0
  step1 = by-assoc-and (under (ε) (X0 • CX01 • X0 • X0) (sym (axiom r022))) Eq.refl Eq.refl

  step2 : CX01 • CX01 • X0 • CX01 • X0 • X0 ≈ CX01 • X1 • X0
  step2 = by-assoc-and (under (CX01) (X0) (sym (axiom r002))) Eq.refl Eq.refl

  proved : X0 • CX01 ≈ CX01 • X1 • X0
  proved = trans step0 (trans step1 (trans step2 (refl)))

module elim_X1 where

  step0 : X1 • X1 ≈ X1 • CX01 • X0 • CX01 • X0
  step0 = by-assoc-and (under (X1) (ε) (axiom r002)) Eq.refl Eq.refl

  step1 : X1 • CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • X0 • CX01 • X0
  step1 = by-assoc-and (under (ε) (CX01 • X0 • CX01 • X0) (axiom r002)) Eq.refl Eq.refl

  step2 : CX01 • X0 • CX01 • X0 • CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 • X0 • X0
  step2 = by-assoc-and (under (CX01 • X0 • CX01 • X0 • CX01) (X0) (drel162.proved)) Eq.refl Eq.refl

  step3 : CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 • X0 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1
  step3 = by-assoc-and (under (CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1) (ε) (axiom r021)) Eq.refl Eq.refl

  step4 : CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 ≈ CX01 • X0 • CX01 • X0 • X1
  step4 = by-assoc-and (under (CX01 • X0 • CX01 • X0) (X1) (axiom r022)) Eq.refl Eq.refl

  step5 : CX01 • X0 • CX01 • X0 • X1 ≈ CX01 • X0 • CX01 • X1 • X0
  step5 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (X0X1.proved)) Eq.refl Eq.refl

  step6 : CX01 • X0 • CX01 • X1 • X0 ≈ CX01 • X0 • X0 • CX01
  step6 = by-assoc-and (under (CX01 • X0) (ε) (sym (drel162.proved))) Eq.refl Eq.refl

  step7 : CX01 • X0 • X0 • CX01 ≈ CX01 • CX01
  step7 = by-assoc-and (under (CX01) (CX01) (axiom r021)) Eq.refl Eq.refl

  step8 : CX01 • CX01 ≈ ε
  step8 = by-assoc-and (under (ε) (ε) (axiom r022)) Eq.refl Eq.refl

  proved : X1 • X1 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module elim_CX20 where

  step0 : CX20 • CX20 ≈ X1 • CCX12 • X1 • CCX12 • CX20
  step0 = by-assoc-and (under (ε) (CX20) (axiom r005)) Eq.refl Eq.refl

  step1 : X1 • CCX12 • X1 • CCX12 • CX20 ≈ X1 • CCX12 • X1 • CCX12 • CX20 • X1 • X1
  step1 = by-assoc-and (under (X1 • CCX12 • X1 • CCX12 • CX20) (ε) (sym (elim_X1.proved))) Eq.refl Eq.refl

  step2 : X1 • CCX12 • X1 • CCX12 • CX20 • X1 • X1 ≈ X1 • CCX12 • X1 • X1 • CCX12 • X1
  step2 = by-assoc-and (under (X1 • CCX12 • X1) (X1) (sym (drel131.proved))) Eq.refl Eq.refl

  step3 : X1 • CCX12 • X1 • X1 • CCX12 • X1 ≈ X1 • CCX12 • CCX12 • X1
  step3 = by-assoc-and (under (X1 • CCX12) (CCX12 • X1) (elim_X1.proved)) Eq.refl Eq.refl

  step4 : X1 • CCX12 • CCX12 • X1 ≈ X1 • X1
  step4 = by-assoc-and (under (X1) (X1) (axiom r024)) Eq.refl Eq.refl

  step5 : X1 • X1 ≈ ε
  step5 = by-assoc-and (under (ε) (ε) (elim_X1.proved)) Eq.refl Eq.refl

  proved : CX20 • CX20 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module elim_SWAP02 where

  step0 : SWAP02 • SWAP02 ≈ SWAP02 • CX02 • CX20 • CX02
  step0 = by-assoc-and (under (SWAP02) (ε) (axiom r010)) Eq.refl Eq.refl

  step1 : SWAP02 • CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02 • CX02 • CX20 • CX02
  step1 = by-assoc-and (under (ε) (CX02 • CX20 • CX02) (axiom r010)) Eq.refl Eq.refl

  step2 : CX02 • CX20 • CX02 • CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX20 • CX02
  step2 = by-assoc-and (under (CX02 • CX20) (CX20 • CX02) (elim_CX02.proved)) Eq.refl Eq.refl

  step3 : CX02 • CX20 • CX20 • CX02 ≈ CX02 • CX02
  step3 = by-assoc-and (under (CX02) (CX02) (elim_CX20.proved)) Eq.refl Eq.refl

  step4 : CX02 • CX02 ≈ ε
  step4 = by-assoc-and (under (ε) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

  proved : SWAP02 • SWAP02 ≈ ε
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module drel161 where

  step0 : CX01 • CX10 ≈ CX10 • CX10 • CX01 • CX10
  step0 = by-assoc-and (under (ε) (CX01 • CX10) (sym (elim_CX10.proved))) Eq.refl Eq.refl

  step1 : CX10 • CX10 • CX01 • CX10 ≈ CX10 • CX10 • CX01 • K01 • CX01 • K01
  step1 = by-assoc-and (under (CX10 • CX10 • CX01) (ε) (axiom r012)) Eq.refl Eq.refl

  step2 : CX10 • CX10 • CX01 • K01 • CX01 • K01 ≈ CX10 • K01 • CX01 • K01 • CX01 • K01 • CX01 • K01
  step2 = by-assoc-and (under (CX10) (CX01 • K01 • CX01 • K01) (axiom r012)) Eq.refl Eq.refl

  step3 : CX10 • K01 • CX01 • K01 • CX01 • K01 • CX01 • K01 ≈ CX10 • K01 • CX01 • CX10 • CX01 • K01
  step3 = by-assoc-and (under (CX10 • K01 • CX01) (CX01 • K01) (sym (axiom r012))) Eq.refl Eq.refl

  step4 : CX10 • K01 • CX01 • CX10 • CX01 • K01 ≈ CX10 • K01 • SWAP01 • K01
  step4 = by-assoc-and (under (CX10 • K01) (K01) (sym (axiom r013))) Eq.refl Eq.refl

  step5 : CX10 • K01 • SWAP01 • K01 ≈ CX10 • SWAP01 • K01 • SWAP01 • SWAP01 • K01
  step5 = by-assoc-and (under (CX10) (SWAP01 • K01) (axiom r035)) Eq.refl Eq.refl

  step6 : CX10 • SWAP01 • K01 • SWAP01 • SWAP01 • K01 ≈ CX10 • SWAP01 • K01 • K01
  step6 = by-assoc-and (under (CX10 • SWAP01 • K01) (K01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step7 : CX10 • SWAP01 • K01 • K01 ≈ CX10 • SWAP01
  step7 = by-assoc-and (under (CX10 • SWAP01) (ε) (axiom r025)) Eq.refl Eq.refl

  proved : CX01 • CX10 ≈ CX10 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))

module symmetry_CX_e where

  step0 : CX01 ≈ CX01 • CX10 • CX10
  step0 = by-assoc-and (under (CX01) (ε) (sym (elim_CX10.proved))) Eq.refl Eq.refl

  step1 : CX01 • CX10 • CX10 ≈ CX01 • CX10 • CX01 • CX01 • CX10
  step1 = by-assoc-and (under (CX01 • CX10) (CX10) (sym (axiom r022))) Eq.refl Eq.refl

  step2 : CX01 • CX10 • CX01 • CX01 • CX10 ≈ SWAP01 • CX01 • CX10
  step2 = by-assoc-and (under (ε) (CX01 • CX10) (sym (axiom r013))) Eq.refl Eq.refl

  step3 : SWAP01 • CX01 • CX10 ≈ SWAP01 • CX10 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (ε) (drel161.proved)) Eq.refl Eq.refl

  proved : CX01 ≈ SWAP01 • CX10 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))

module symmetry_SWAP02 where

  step0 : SWAP02 ≈ CX02 • CX20 • CX02
  step0 = by-assoc-and (under (ε) (ε) (axiom r010)) Eq.refl Eq.refl

  step1 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02 • SWAP01 • SWAP01
  step1 = by-assoc-and (under (CX02 • CX20 • CX02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : CX02 • CX20 • CX02 • SWAP01 • SWAP01 ≈ CX02 • CX20 • SWAP01 • SWAP01 • CX02 • SWAP01 • SWAP01
  step2 = by-assoc-and (under (CX02 • CX20) (CX02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step3 : CX02 • CX20 • SWAP01 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ CX02 • CX20 • SWAP01 • CX12 • SWAP01
  step3 = by-assoc-and (under (CX02 • CX20 • SWAP01) (SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step4 : CX02 • CX20 • SWAP01 • CX12 • SWAP01 ≈ CX02 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX12 • SWAP01
  step4 = by-assoc-and (under (CX02) (CX20 • SWAP01 • CX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : CX02 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX12 • SWAP01 ≈ CX02 • SWAP01 • CX21 • CX12 • SWAP01
  step5 = by-assoc-and (under (CX02 • SWAP01) (CX12 • SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

  step6 : CX02 • SWAP01 • CX21 • CX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • CX21 • CX12 • SWAP01
  step6 = by-assoc-and (under (ε) (CX02 • SWAP01 • CX21 • CX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step7 : SWAP01 • SWAP01 • CX02 • SWAP01 • CX21 • CX12 • SWAP01 ≈ SWAP01 • CX12 • CX21 • CX12 • SWAP01
  step7 = by-assoc-and (under (SWAP01) (CX21 • CX12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step8 : SWAP01 • CX12 • CX21 • CX12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01
  step8 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r008))) Eq.refl Eq.refl

  proved : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))

module symmetry_CX_f where

  step0 : CX12 ≈ SWAP01 • CX02 • SWAP01
  step0 = by-assoc-and (under (ε) (ε) (axiom r030)) Eq.refl Eq.refl

  step1 : SWAP01 • CX02 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01
  step1 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r009)) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CX10 • SWAP01 • SWAP12 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP12 • SWAP01 • CX10 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CX10 • SWAP02
  step3 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP01 • CX10) (ε) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • SWAP01 • CX10 • SWAP02 ≈ SWAP02 • CX10 • SWAP02
  step4 = by-assoc-and (under (ε) (CX10 • SWAP02) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

  proved : CX12 ≈ SWAP02 • CX10 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module symmetry_CX_i where

  step0 : CX21 ≈ K12 • K12 • CX21
  step0 = by-assoc-and (under (ε) (CX21) (sym (axiom r023))) Eq.refl Eq.refl

  step1 : K12 • K12 • CX21 ≈ K12 • CX12 • K12
  step1 = by-assoc-and (under (K12) (ε) (drel46.proved)) Eq.refl Eq.refl

  step2 : K12 • CX12 • K12 ≈ K12 • SWAP02 • CX10 • SWAP02 • K12
  step2 = by-assoc-and (under (K12) (K12) (symmetry_CX_f.proved)) Eq.refl Eq.refl

  step3 : K12 • SWAP02 • CX10 • SWAP02 • K12 ≈ K12 • SWAP02 • CX10 • SWAP02 • K12 • SWAP02 • SWAP02
  step3 = by-assoc-and (under (K12 • SWAP02 • CX10 • SWAP02 • K12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step4 : K12 • SWAP02 • CX10 • SWAP02 • K12 • SWAP02 • SWAP02 ≈ K12 • SWAP02 • CX10 • K01 • SWAP02
  step4 = by-assoc-and (under (K12 • SWAP02 • CX10) (SWAP02) (sym (axiom r011))) Eq.refl Eq.refl

  step5 : K12 • SWAP02 • CX10 • K01 • SWAP02 ≈ SWAP02 • SWAP02 • K12 • SWAP02 • CX10 • K01 • SWAP02
  step5 = by-assoc-and (under (ε) (K12 • SWAP02 • CX10 • K01 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step6 : SWAP02 • SWAP02 • K12 • SWAP02 • CX10 • K01 • SWAP02 ≈ SWAP02 • K01 • CX10 • K01 • SWAP02
  step6 = by-assoc-and (under (SWAP02) (CX10 • K01 • SWAP02) (sym (axiom r011))) Eq.refl Eq.refl

  step7 : SWAP02 • K01 • CX10 • K01 • SWAP02 ≈ SWAP02 • K01 • K01 • CX01 • K01 • K01 • SWAP02
  step7 = by-assoc-and (under (SWAP02 • K01) (K01 • SWAP02) (axiom r012)) Eq.refl Eq.refl

  step8 : SWAP02 • K01 • K01 • CX01 • K01 • K01 • SWAP02 ≈ SWAP02 • K01 • K01 • CX01 • SWAP02
  step8 = by-assoc-and (under (SWAP02 • K01 • K01 • CX01) (SWAP02) (axiom r025)) Eq.refl Eq.refl

  step9 : SWAP02 • K01 • K01 • CX01 • SWAP02 ≈ SWAP02 • CX01 • SWAP02
  step9 = by-assoc-and (under (SWAP02) (CX01 • SWAP02) (axiom r025)) Eq.refl Eq.refl

  proved : CX21 ≈ SWAP02 • CX01 • SWAP02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))

module bifunct_X_CX_d where

  step0 : CX01 • X2 ≈ CX01 • SWAP02 • X0 • SWAP02
  step0 = by-assoc-and (under (CX01) (ε) (axiom r015)) Eq.refl Eq.refl

  step1 : CX01 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • SWAP02 • CX01 • SWAP02 • X0 • SWAP02
  step1 = by-assoc-and (under (ε) (CX01 • SWAP02 • X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step2 : SWAP02 • SWAP02 • CX01 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CX21 • X0 • SWAP02
  step2 = by-assoc-and (under (SWAP02) (X0 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

  step3 : SWAP02 • CX21 • X0 • SWAP02 ≈ SWAP02 • X0 • CX21 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (bifunct_X_CX_b.proved)) Eq.refl Eq.refl

  step4 : SWAP02 • X0 • CX21 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • CX01 • SWAP02 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • X0) (SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

  step5 : SWAP02 • X0 • SWAP02 • CX01 • SWAP02 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • CX01
  step5 = by-assoc-and (under (SWAP02 • X0 • SWAP02 • CX01) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step6 : SWAP02 • X0 • SWAP02 • CX01 ≈ X2 • CX01
  step6 = by-assoc-and (under (ε) (CX01) (sym (axiom r015))) Eq.refl Eq.refl

  proved : CX01 • X2 ≈ X2 • CX01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_K_b where

  step0 : X2 • K01 ≈ X2 • SWAP02 • K12 • SWAP02
  step0 = by-assoc-and (under (X2) (ε) (axiom r011)) Eq.refl Eq.refl

  step1 : X2 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • K12 • SWAP02
  step1 = by-assoc-and (under (ε) (SWAP02 • K12 • SWAP02) (axiom r015)) Eq.refl Eq.refl

  step2 : SWAP02 • X0 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • X0 • K12 • SWAP02
  step2 = by-assoc-and (under (SWAP02 • X0) (K12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP02 • X0 • K12 • SWAP02 ≈ SWAP02 • K12 • X0 • SWAP02
  step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r027)) Eq.refl Eq.refl

  step4 : SWAP02 • K12 • X0 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • SWAP02 • X0 • SWAP02
  step4 = by-assoc-and (under (SWAP02 • K12) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

  step5 : SWAP02 • K12 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • X2
  step5 = by-assoc-and (under (SWAP02 • K12 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

  step6 : SWAP02 • K12 • SWAP02 • X2 ≈ K01 • X2
  step6 = by-assoc-and (under (ε) (X2) (sym (axiom r011))) Eq.refl Eq.refl

  proved : X2 • K01 ≈ K01 • X2
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module bifunct_X_CX_c where

  step0 : CX10 • X2 ≈ K01 • CX01 • K01 • X2
  step0 = by-assoc-and (under (ε) (X2) (axiom r012)) Eq.refl Eq.refl

  step1 : K01 • CX01 • K01 • X2 ≈ K01 • CX01 • X2 • K01
  step1 = by-assoc-and (under (K01 • CX01) (ε) (sym (bifunct_X_K_b.proved))) Eq.refl Eq.refl

  step2 : K01 • CX01 • X2 • K01 ≈ K01 • X2 • CX01 • K01
  step2 = by-assoc-and (under (K01) (K01) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

  step3 : K01 • X2 • CX01 • K01 ≈ X2 • K01 • CX01 • K01
  step3 = by-assoc-and (under (ε) (CX01 • K01) (sym (bifunct_X_K_b.proved))) Eq.refl Eq.refl

  step4 : X2 • K01 • CX01 • K01 ≈ X2 • CX10
  step4 = by-assoc-and (under (X2) (ε) (sym (axiom r012))) Eq.refl Eq.refl

  proved : CX10 • X2 ≈ X2 • CX10
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_CX_e where

  step0 : CX02 • X1 ≈ CX02 • SWAP01 • X0 • SWAP01
  step0 = by-assoc-and (under (CX02) (ε) (axiom r028)) Eq.refl Eq.refl

  step1 : CX02 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • X0 • SWAP01
  step1 = by-assoc-and (under (ε) (CX02 • SWAP01 • X0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP01 • CX02 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX12 • X0 • SWAP01
  step2 = by-assoc-and (under (SWAP01) (X0 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step3 : SWAP01 • CX12 • X0 • SWAP01 ≈ SWAP01 • X0 • CX12 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r026)) Eq.refl Eq.refl

  step4 : SWAP01 • X0 • CX12 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • CX02 • SWAP01 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (axiom r030)) Eq.refl Eq.refl

  step5 : SWAP01 • X0 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ X1 • CX02 • SWAP01 • SWAP01
  step5 = by-assoc-and (under (ε) (CX02 • SWAP01 • SWAP01) (sym (axiom r028))) Eq.refl Eq.refl

  step6 : X1 • CX02 • SWAP01 • SWAP01 ≈ X1 • CX02
  step6 = by-assoc-and (under (X1 • CX02) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  proved : CX02 • X1 ≈ X1 • CX02
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_CX_g where

  step0 : CX21 ≈ SWAP01 • CX20 • SWAP01
  step0 = by-assoc-and (under (ε) (ε) (axiom r031)) Eq.refl Eq.refl

  step1 : SWAP01 • CX20 • SWAP01 ≈ SWAP01 • SWAP02 • CX02 • SWAP02 • SWAP01
  step1 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r029)) Eq.refl Eq.refl

  step2 : SWAP01 • SWAP02 • CX02 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • SWAP02 • CX02) (SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12
  step4 = by-assoc-and (under (SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step5 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12
  step5 = by-assoc-and (under (ε) (SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step6 : SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12
  step6 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r030))) Eq.refl Eq.refl

  proved : CX21 ≈ SWAP12 • CX12 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module symmetry_CX_h where

  step0 : CX20 ≈ SWAP02 • CX02 • SWAP02
  step0 = by-assoc-and (under (ε) (ε) (axiom r029)) Eq.refl Eq.refl

  step1 : SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01
  step1 = by-assoc-and (under (SWAP02 • CX02) (ε) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step2 : SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01
  step2 = by-assoc-and (under (ε) (CX02 • SWAP01 • SWAP12 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01
  step3 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

  step4 : SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01 ≈ SWAP01 • CX21 • SWAP01
  step4 = by-assoc-and (under (SWAP01) (SWAP01) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

  proved : CX20 ≈ SWAP01 • CX21 • SWAP01
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))

module bifunct_X_CX_f where

  step0 : CX20 • X1 ≈ CX20 • SWAP01 • X0 • SWAP01
  step0 = by-assoc-and (under (CX20) (ε) (axiom r028)) Eq.refl Eq.refl

  step1 : CX20 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX21 • SWAP01 • SWAP01 • X0 • SWAP01
  step1 = by-assoc-and (under (ε) (SWAP01 • X0 • SWAP01) (symmetry_CX_h.proved)) Eq.refl Eq.refl

  step2 : SWAP01 • CX21 • SWAP01 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX21 • X0 • SWAP01
  step2 = by-assoc-and (under (SWAP01 • CX21) (X0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

  step3 : SWAP01 • CX21 • X0 • SWAP01 ≈ SWAP01 • X0 • CX21 • SWAP01
  step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_X_CX_b.proved)) Eq.refl Eq.refl

  step4 : SWAP01 • X0 • CX21 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CX21 • SWAP01
  step4 = by-assoc-and (under (SWAP01 • X0) (CX21 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

  step5 : SWAP01 • X0 • SWAP01 • SWAP01 • CX21 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • CX20
  step5 = by-assoc-and (under (SWAP01 • X0 • SWAP01) (ε) (sym (symmetry_CX_h.proved))) Eq.refl Eq.refl

  step6 : SWAP01 • X0 • SWAP01 • CX20 ≈ X1 • CX20
  step6 = by-assoc-and (under (ε) (CX20) (sym (axiom r028))) Eq.refl Eq.refl

  proved : CX20 • X1 ≈ X1 • CX20
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))

module drel154 where

  step0 : CX12 • CX21 ≈ CX12 • SWAP12 • CX12 • SWAP12
  step0 = by-assoc-and (under (CX12) (ε) (symmetry_CX_g.proved)) Eq.refl Eq.refl

  step1 : CX12 • SWAP12 • CX12 • SWAP12 ≈ CX12 • SWAP12 • CX12 • CX12 • CX21 • CX12
  step1 = by-assoc-and (under (CX12 • SWAP12 • CX12) (ε) (axiom r008)) Eq.refl Eq.refl

  step2 : CX12 • SWAP12 • CX12 • CX12 • CX21 • CX12 ≈ CX12 • SWAP12 • CX21 • CX12
  step2 = by-assoc-and (under (CX12 • SWAP12) (CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

  step3 : CX12 • SWAP12 • CX21 • CX12 ≈ CX12 • CX12 • CX21 • CX12 • CX21 • CX12
  step3 = by-assoc-and (under (CX12) (CX21 • CX12) (axiom r008)) Eq.refl Eq.refl

  step4 : CX12 • CX12 • CX21 • CX12 • CX21 • CX12 ≈ CX21 • CX12 • CX21 • CX12
  step4 = by-assoc-and (under (ε) (CX21 • CX12 • CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

  step5 : CX21 • CX12 • CX21 • CX12 ≈ CX21 • SWAP12
  step5 = by-assoc-and (under (CX21) (ε) (sym (axiom r008))) Eq.refl Eq.refl

  proved : CX12 • CX21 ≈ CX21 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))

module symmetry_CX_d where

  step0 : CX12 ≈ CX12 • CX21 • CX21
  step0 = by-assoc-and (under (CX12) (ε) (sym (elim_CX21.proved))) Eq.refl Eq.refl

  step1 : CX12 • CX21 • CX21 ≈ CX12 • CX21 • CX12 • CX12 • CX21
  step1 = by-assoc-and (under (CX12 • CX21) (CX21) (sym (elim_CX12.proved))) Eq.refl Eq.refl

  step2 : CX12 • CX21 • CX12 • CX12 • CX21 ≈ SWAP12 • CX12 • CX21
  step2 = by-assoc-and (under (ε) (CX12 • CX21) (sym (axiom r008))) Eq.refl Eq.refl

  step3 : SWAP12 • CX12 • CX21 ≈ SWAP12 • CX21 • SWAP12
  step3 = by-assoc-and (under (SWAP12) (ε) (drel154.proved)) Eq.refl Eq.refl

  proved : CX12 ≈ SWAP12 • CX21 • SWAP12
  proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))
