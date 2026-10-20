{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel78 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r034 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel77 as drel77
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : CX01 • Z0 ≈ CX01 • Z0 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CX01 • Z0) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CX01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (Z0 • SWAP01 • SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

step2 : SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CX10 • Z1 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CX10) (SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

step3 : SWAP01 • CX10 • Z1 • SWAP01 ≈ SWAP01 • Z1 • CX10 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel77.proved)) Eq.refl Eq.refl

step4 : SWAP01 • Z1 • CX10 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CX10 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 • SWAP01 ≈ Z0 • SWAP01 • CX10 • SWAP01
step5 = by-assoc-and (under (ε) (Z0 • SWAP01 • CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : Z0 • SWAP01 • CX10 • SWAP01 ≈ Z0 • CX01
step6 = by-assoc-and (under (Z0) (ε) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

proved : CX01 • Z0 ≈ Z0 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
