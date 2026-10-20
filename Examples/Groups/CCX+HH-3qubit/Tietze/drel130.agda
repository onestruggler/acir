{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel130 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX10 ; CX12 ; SWAP02 ; X0 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; r032 ; r042 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b as symmetry_CX_b

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
