{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel134 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel112 as drel112
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g

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
