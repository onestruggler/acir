{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel90 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX10 ; CX12 ; SWAP02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r032 ; r044 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b as symmetry_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

step0 : CX10 • CCX01 ≈ CX10 • SWAP02 • CCX12 • SWAP02
step0 = by-assoc-and (under (CX10) (ε) (axiom r032)) Eq.refl Eq.refl

step1 : CX10 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX10 • SWAP02 • CCX12 • SWAP02
step1 = by-assoc-and (under (ε) (CX10 • SWAP02 • CCX12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • SWAP02 • CX10 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CX12 • CCX12 • SWAP02
step2 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

step3 : SWAP02 • CX12 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX10 • CX12 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r044)) Eq.refl Eq.refl

step4 : SWAP02 • CCX12 • CX10 • CX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • CX12 • SWAP02 • CX12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CCX12) (CX12 • SWAP02) (symmetry_CX_b.proved)) Eq.refl Eq.refl

step5 : SWAP02 • CCX12 • SWAP02 • CX12 • SWAP02 • CX12 • SWAP02 ≈ CCX01 • CX12 • SWAP02 • CX12 • SWAP02
step5 = by-assoc-and (under (ε) (CX12 • SWAP02 • CX12 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

step6 : CCX01 • CX12 • SWAP02 • CX12 • SWAP02 ≈ CCX01 • CX12 • CX10
step6 = by-assoc-and (under (CCX01 • CX12) (ε) (sym (symmetry_CX_b.proved))) Eq.refl Eq.refl

proved : CX10 • CCX01 ≈ CCX01 • CX12 • CX10
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
