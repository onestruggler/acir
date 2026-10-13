{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel94 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g as symmetry_CCX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_j as symmetry_CX_j

step0 : CCX12 • CX20 ≈ CCX12 • SWAP12 • CX10 • SWAP12
step0 = by-assoc-and (under (CCX12) (ε) (symmetry_CX_j.proved)) Eq.refl Eq.refl

step1 : CCX12 • SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CX10 • SWAP12) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

step2 : SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CCX12) (CX10 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CCX12 • CX10 • SWAP12 ≈ SWAP12 • CX10 • CCX12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r036)) Eq.refl Eq.refl

step4 : SWAP12 • CX10 • CCX12 • SWAP12 ≈ SWAP12 • CX10 • SWAP12 • SWAP12 • CCX12 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CX10) (CCX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CX10 • SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CX10 • SWAP12 • CCX12
step5 = by-assoc-and (under (SWAP12 • CX10 • SWAP12) (ε) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CX10 • SWAP12 • CCX12 ≈ CX20 • CCX12
step6 = by-assoc-and (under (ε) (CCX12) (sym (symmetry_CX_j.proved))) Eq.refl Eq.refl

proved : CCX12 • CX20 ≈ CX20 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
