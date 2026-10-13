{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd6 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd7 as cadd7
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : CX10 • CCX02 • CX10 ≈ CX10 • CCX02 • CX10 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CX10 • CCX02 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CX10 • CCX02 • CX10 • SWAP01 • SWAP01 ≈ CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01
step1 = by-assoc-and (under (CX10) (CX10 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step2 : CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01
step2 = by-assoc-and (under (ε) (CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step3 : SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • CX01 • SWAP01
step3 = by-assoc-and (under (SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

step4 : SWAP01 • SWAP01 • CX10 • SWAP01 • CCX12 • CX01 • SWAP01 ≈ SWAP01 • CX01 • CCX12 • CX01 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CCX12 • CX01 • SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

step5 : SWAP01 • CX01 • CCX12 • CX01 • SWAP01 ≈ SWAP01 • CCX02 • CCX12 • CCX02 • SWAP01
step5 = by-assoc-and (under (SWAP01) (SWAP01) (cadd7.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CCX02 • CCX12 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01
step6 = by-assoc-and (under (SWAP01 • CCX02 • CCX12) (SWAP01) (axiom r014)) Eq.refl Eq.refl

step7 : SWAP01 • CCX02 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01
step7 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step8 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12
step8 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step9 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 ≈ CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12
step9 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step10 : CCX12 • SWAP01 • CCX12 • SWAP01 • CCX12 ≈ CCX12 • CCX02 • CCX12
step10 = by-assoc-and (under (CCX12) (CCX12) (sym (axiom r014))) Eq.refl Eq.refl

proved : CX10 • CCX02 • CX10 ≈ CCX12 • CCX02 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
