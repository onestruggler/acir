{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_e as bifunct_Z_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_f as bifunct_Z_CX_f

step0 : Z2 • SWAP01 ≈ Z2 • CX01 • CX10 • CX01
step0 = by-assoc-and (under (Z2) (ε) (axiom r013)) Eq.refl Eq.refl

step1 : Z2 • CX01 • CX10 • CX01 ≈ CX01 • Z2 • CX10 • CX01
step1 = by-assoc-and (under (ε) (CX10 • CX01) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

step2 : CX01 • Z2 • CX10 • CX01 ≈ CX01 • CX10 • Z2 • CX01
step2 = by-assoc-and (under (CX01) (CX01) (bifunct_Z_CX_f.proved)) Eq.refl Eq.refl

step3 : CX01 • CX10 • Z2 • CX01 ≈ CX01 • CX10 • CX01 • Z2
step3 = by-assoc-and (under (CX01 • CX10) (ε) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

step4 : CX01 • CX10 • CX01 • Z2 ≈ SWAP01 • Z2
step4 = by-assoc-and (under (ε) (Z2) (sym (axiom r013))) Eq.refl Eq.refl

proved : Z2 • SWAP01 ≈ SWAP01 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
