{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel11 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; CX21 ; SWAP01 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; r030 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel41 as drel41
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_d as symmetry_CX_d

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
