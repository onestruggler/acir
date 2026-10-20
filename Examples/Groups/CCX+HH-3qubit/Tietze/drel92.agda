{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel92 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r036 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

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
