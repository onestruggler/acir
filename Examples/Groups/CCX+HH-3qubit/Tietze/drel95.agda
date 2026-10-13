{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel95 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : CX02 • CCX02 ≈ CX02 • SWAP01 • CCX12 • SWAP01
step0 = by-assoc-and (under (CX02) (ε) (axiom r014)) Eq.refl Eq.refl

step1 : CX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • CCX12 • SWAP01
step1 = by-assoc-and (under (ε) (CX02 • SWAP01 • CCX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CX12 • CCX12 • SWAP01
step2 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step3 : SWAP01 • CX12 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • CX12 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r044)) Eq.refl Eq.refl

step4 : SWAP01 • CCX12 • CX10 • CX12 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • SWAP01 • CX02 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX12 • CX10) (SWAP01) (axiom r030)) Eq.refl Eq.refl

step5 : SWAP01 • CCX12 • CX10 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX10 • SWAP01 • CX02
step5 = by-assoc-and (under (SWAP01 • CCX12 • CX10 • SWAP01 • CX02) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CCX12 • CX10 • SWAP01 • CX02 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01 • CX02
step6 = by-assoc-and (under (SWAP01 • CCX12) (CX10 • SWAP01 • CX02) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step7 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CX10 • SWAP01 • CX02 ≈ SWAP01 • CCX12 • SWAP01 • CX01 • CX02
step7 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01) (CX02) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

step8 : SWAP01 • CCX12 • SWAP01 • CX01 • CX02 ≈ CCX02 • CX01 • CX02
step8 = by-assoc-and (under (ε) (CX01 • CX02) (sym (axiom r014))) Eq.refl Eq.refl

proved : CX02 • CCX02 ≈ CCX02 • CX01 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
