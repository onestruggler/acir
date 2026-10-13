{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel42 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel19 as drel19
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b as symmetry_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_a as symmetry_Z_a
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_b as symmetry_Z_b

step0 : Z0 • CX10 ≈ Z0 • CX10 • SWAP02 • SWAP02
step0 = by-assoc-and (under (Z0 • CX10) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step1 : Z0 • CX10 • SWAP02 • SWAP02 ≈ Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
step1 = by-assoc-and (under (Z0) (CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
step2 = by-assoc-and (under (ε) (Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step3 : SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • Z2 • SWAP02 • CX10 • SWAP02 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02 • CX10 • SWAP02 • SWAP02) (sym (axiom r016))) Eq.refl Eq.refl

step4 : SWAP02 • Z2 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • Z2 • CX12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • Z2) (SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

step5 : SWAP02 • Z2 • CX12 • SWAP02 ≈ SWAP02 • CX12 • Z1 • Z2 • SWAP02
step5 = by-assoc-and (under (SWAP02) (SWAP02) (drel19.proved)) Eq.refl Eq.refl

step6 : SWAP02 • CX12 • Z1 • Z2 • SWAP02 ≈ SWAP02 • CX12 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02
step6 = by-assoc-and (under (SWAP02 • CX12 • Z1) (Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step7 : SWAP02 • CX12 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • SWAP02 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02
step7 = by-assoc-and (under (SWAP02 • CX12) (Z1 • SWAP02 • SWAP02 • Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step8 : SWAP02 • CX12 • SWAP02 • SWAP02 • Z1 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • Z1 • SWAP02 • Z2 • SWAP02
step8 = by-assoc-and (under (SWAP02 • CX12 • SWAP02) (SWAP02 • Z2 • SWAP02) (sym (symmetry_Z_a.proved))) Eq.refl Eq.refl

step9 : SWAP02 • CX12 • SWAP02 • Z1 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • Z1 • Z0
step9 = by-assoc-and (under (SWAP02 • CX12 • SWAP02 • Z1) (ε) (sym (symmetry_Z_b.proved))) Eq.refl Eq.refl

step10 : SWAP02 • CX12 • SWAP02 • Z1 • Z0 ≈ CX10 • Z1 • Z0
step10 = by-assoc-and (under (ε) (Z1 • Z0) (sym (symmetry_CX_b.proved))) Eq.refl Eq.refl

proved : Z0 • CX10 ≈ CX10 • Z1 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
