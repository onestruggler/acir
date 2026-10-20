{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel67 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r028 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : X1 • CX10 ≈ SWAP01 • X0 • SWAP01 • CX10
step0 = by-assoc-and (under (ε) (CX10) (axiom r028)) Eq.refl Eq.refl

step1 : SWAP01 • X0 • SWAP01 • CX10 ≈ SWAP01 • X0 • SWAP01 • CX10 • SWAP01 • SWAP01
step1 = by-assoc-and (under (SWAP01 • X0 • SWAP01 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • X0 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • CX01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

step3 : SWAP01 • X0 • CX01 • SWAP01 ≈ SWAP01 • CX01 • X1 • X0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel162.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX01 • X1 • X0 • SWAP01 ≈ SWAP01 • CX01 • SWAP01 • X0 • SWAP01 • X0 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CX01) (X0 • SWAP01) (axiom r028)) Eq.refl Eq.refl

step5 : SWAP01 • CX01 • SWAP01 • X0 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX01 • SWAP01 • X0 • X1
step5 = by-assoc-and (under (SWAP01 • CX01 • SWAP01 • X0) (ε) (sym (axiom r028))) Eq.refl Eq.refl

step6 : SWAP01 • CX01 • SWAP01 • X0 • X1 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • X1
step6 = by-assoc-and (under (SWAP01) (SWAP01 • X0 • X1) (symmetry_CX_e.proved)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • CX10 • SWAP01 • SWAP01 • X0 • X1 ≈ SWAP01 • SWAP01 • CX10 • X0 • X1
step7 = by-assoc-and (under (SWAP01 • SWAP01 • CX10) (X0 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : SWAP01 • SWAP01 • CX10 • X0 • X1 ≈ CX10 • X0 • X1
step8 = by-assoc-and (under (ε) (CX10 • X0 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : X1 • CX10 ≈ CX10 • X0 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
