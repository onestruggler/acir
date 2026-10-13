{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02_alt where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_j as symmetry_CX_j

step0 : SWAP02 ≈ CX02 • CX20 • CX02
step0 = by-assoc-and (under (ε) (ε) (axiom r010)) Eq.refl Eq.refl

step1 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • SWAP12 • CX01 • SWAP12
step1 = by-assoc-and (under (CX02 • CX20) (ε) (axiom r009)) Eq.refl Eq.refl

step2 : CX02 • CX20 • SWAP12 • CX01 • SWAP12 ≈ CX02 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12
step2 = by-assoc-and (under (CX02) (SWAP12 • CX01 • SWAP12) (symmetry_CX_j.proved)) Eq.refl Eq.refl

step3 : CX02 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12
step3 = by-assoc-and (under (ε) (SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12) (axiom r009)) Eq.refl Eq.refl

step4 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • CX01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CX01 • SWAP12 • SWAP12 • CX10) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step5 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX10 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CX10 • CX01 • SWAP12
step5 = by-assoc-and (under (SWAP12 • CX01) (CX10 • CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step6 : SWAP12 • CX01 • CX10 • CX01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12
step6 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r013))) Eq.refl Eq.refl

proved : SWAP02 ≈ SWAP12 • SWAP01 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
