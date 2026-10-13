{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel134 as drel134
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : CX12 • CX20 ≈ CX12 • CX20 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CX12 • CX20) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CX12 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • CX20 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CX20 • SWAP01 • SWAP01) (axiom r030)) Eq.refl Eq.refl

step2 : SWAP01 • CX02 • SWAP01 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CX02 • CX21 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CX02) (SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

step3 : SWAP01 • CX02 • CX21 • SWAP01 ≈ SWAP01 • CX21 • CX02 • CX01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel134.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX21 • CX02 • CX01 • SWAP01 ≈ SWAP01 • SWAP01 • CX20 • SWAP01 • CX02 • CX01 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CX02 • CX01 • SWAP01) (axiom r031)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CX20 • SWAP01 • CX02 • CX01 • SWAP01 ≈ CX20 • SWAP01 • CX02 • CX01 • SWAP01
step5 = by-assoc-and (under (ε) (CX20 • SWAP01 • CX02 • CX01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : CX20 • SWAP01 • CX02 • CX01 • SWAP01 ≈ CX20 • SWAP01 • CX02 • SWAP01 • CX10 • SWAP01 • SWAP01
step6 = by-assoc-and (under (CX20 • SWAP01 • CX02) (SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

step7 : CX20 • SWAP01 • CX02 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ CX20 • CX12 • CX10 • SWAP01 • SWAP01
step7 = by-assoc-and (under (CX20) (CX10 • SWAP01 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step8 : CX20 • CX12 • CX10 • SWAP01 • SWAP01 ≈ CX20 • CX12 • CX10
step8 = by-assoc-and (under (CX20 • CX12 • CX10) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CX12 • CX20 ≈ CX20 • CX12 • CX10
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
