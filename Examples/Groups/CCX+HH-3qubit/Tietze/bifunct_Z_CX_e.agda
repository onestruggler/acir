{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_e where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; CX12 ; K01 ; SWAP02 ; Z0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r012 ; r016 ; r025 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_b as bifunct_Z_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_b as bifunct_Z_K_b
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

step0 : Z2 • CX01 ≈ Z2 • CX01 • K01 • K01
step0 = by-assoc-and (under (Z2 • CX01) (ε) (sym (axiom r025))) Eq.refl Eq.refl

step1 : Z2 • CX01 • K01 • K01 ≈ Z2 • K01 • K01 • CX01 • K01 • K01
step1 = by-assoc-and (under (Z2) (CX01 • K01 • K01) (sym (axiom r025))) Eq.refl Eq.refl

step2 : Z2 • K01 • K01 • CX01 • K01 • K01 ≈ Z2 • K01 • CX10 • K01
step2 = by-assoc-and (under (Z2 • K01) (K01) (sym (axiom r012))) Eq.refl Eq.refl

step3 : Z2 • K01 • CX10 • K01 ≈ K01 • Z2 • CX10 • K01
step3 = by-assoc-and (under (ε) (CX10 • K01) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

step4 : K01 • Z2 • CX10 • K01 ≈ K01 • SWAP02 • Z0 • SWAP02 • CX10 • K01
step4 = by-assoc-and (under (K01) (CX10 • K01) (axiom r016)) Eq.refl Eq.refl

step5 : K01 • SWAP02 • Z0 • SWAP02 • CX10 • K01 ≈ K01 • SWAP02 • Z0 • SWAP02 • CX10 • SWAP02 • SWAP02 • K01
step5 = by-assoc-and (under (K01 • SWAP02 • Z0 • SWAP02 • CX10) (K01) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step6 : K01 • SWAP02 • Z0 • SWAP02 • CX10 • SWAP02 • SWAP02 • K01 ≈ K01 • SWAP02 • Z0 • CX12 • SWAP02 • K01
step6 = by-assoc-and (under (K01 • SWAP02 • Z0) (SWAP02 • K01) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

step7 : K01 • SWAP02 • Z0 • CX12 • SWAP02 • K01 ≈ K01 • SWAP02 • CX12 • Z0 • SWAP02 • K01
step7 = by-assoc-and (under (K01 • SWAP02) (SWAP02 • K01) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

step8 : K01 • SWAP02 • CX12 • Z0 • SWAP02 • K01 ≈ K01 • SWAP02 • SWAP02 • CX10 • SWAP02 • Z0 • SWAP02 • K01
step8 = by-assoc-and (under (K01 • SWAP02) (Z0 • SWAP02 • K01) (symmetry_CX_f.proved)) Eq.refl Eq.refl

step9 : K01 • SWAP02 • SWAP02 • CX10 • SWAP02 • Z0 • SWAP02 • K01 ≈ K01 • CX10 • SWAP02 • Z0 • SWAP02 • K01
step9 = by-assoc-and (under (K01) (CX10 • SWAP02 • Z0 • SWAP02 • K01) (elim_SWAP02.proved)) Eq.refl Eq.refl

step10 : K01 • CX10 • SWAP02 • Z0 • SWAP02 • K01 ≈ K01 • CX10 • Z2 • K01
step10 = by-assoc-and (under (K01 • CX10) (K01) (sym (axiom r016))) Eq.refl Eq.refl

step11 : K01 • CX10 • Z2 • K01 ≈ K01 • K01 • CX01 • K01 • Z2 • K01
step11 = by-assoc-and (under (K01) (Z2 • K01) (axiom r012)) Eq.refl Eq.refl

step12 : K01 • K01 • CX01 • K01 • Z2 • K01 ≈ CX01 • K01 • Z2 • K01
step12 = by-assoc-and (under (ε) (CX01 • K01 • Z2 • K01) (axiom r025)) Eq.refl Eq.refl

step13 : CX01 • K01 • Z2 • K01 ≈ CX01 • K01 • K01 • Z2
step13 = by-assoc-and (under (CX01 • K01) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

step14 : CX01 • K01 • K01 • Z2 ≈ CX01 • Z2
step14 = by-assoc-and (under (CX01) (Z2) (axiom r025)) Eq.refl Eq.refl

proved : Z2 • CX01 ≈ CX01 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (refl)))))))))))))))
