{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

step0 : CX21 ≈ K12 • K12 • CX21
step0 = by-assoc-and (under (ε) (CX21) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CX21 ≈ K12 • CX12 • K12
step1 = by-assoc-and (under (K12) (ε) (drel46.proved)) Eq.refl Eq.refl

step2 : K12 • CX12 • K12 ≈ K12 • SWAP02 • CX10 • SWAP02 • K12
step2 = by-assoc-and (under (K12) (K12) (symmetry_CX_f.proved)) Eq.refl Eq.refl

step3 : K12 • SWAP02 • CX10 • SWAP02 • K12 ≈ K12 • SWAP02 • CX10 • SWAP02 • K12 • SWAP02 • SWAP02
step3 = by-assoc-and (under (K12 • SWAP02 • CX10 • SWAP02 • K12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step4 : K12 • SWAP02 • CX10 • SWAP02 • K12 • SWAP02 • SWAP02 ≈ K12 • SWAP02 • CX10 • K01 • SWAP02
step4 = by-assoc-and (under (K12 • SWAP02 • CX10) (SWAP02) (sym (axiom r011))) Eq.refl Eq.refl

step5 : K12 • SWAP02 • CX10 • K01 • SWAP02 ≈ SWAP02 • SWAP02 • K12 • SWAP02 • CX10 • K01 • SWAP02
step5 = by-assoc-and (under (ε) (K12 • SWAP02 • CX10 • K01 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step6 : SWAP02 • SWAP02 • K12 • SWAP02 • CX10 • K01 • SWAP02 ≈ SWAP02 • K01 • CX10 • K01 • SWAP02
step6 = by-assoc-and (under (SWAP02) (CX10 • K01 • SWAP02) (sym (axiom r011))) Eq.refl Eq.refl

step7 : SWAP02 • K01 • CX10 • K01 • SWAP02 ≈ SWAP02 • K01 • K01 • CX01 • K01 • K01 • SWAP02
step7 = by-assoc-and (under (SWAP02 • K01) (K01 • SWAP02) (axiom r012)) Eq.refl Eq.refl

step8 : SWAP02 • K01 • K01 • CX01 • K01 • K01 • SWAP02 ≈ SWAP02 • K01 • K01 • CX01 • SWAP02
step8 = by-assoc-and (under (SWAP02 • K01 • K01 • CX01) (SWAP02) (axiom r025)) Eq.refl Eq.refl

step9 : SWAP02 • K01 • K01 • CX01 • SWAP02 ≈ SWAP02 • CX01 • SWAP02
step9 = by-assoc-and (under (SWAP02) (CX01 • SWAP02) (axiom r025)) Eq.refl Eq.refl

proved : CX21 ≈ SWAP02 • CX01 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))
