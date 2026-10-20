{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel84 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; SWAP02 ; X0 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; r038 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

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
