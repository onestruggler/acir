{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_d where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b as bifunct_X_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : CX01 • X2 ≈ CX01 • SWAP02 • X0 • SWAP02
step0 = by-assoc-and (under (CX01) (ε) (axiom r015)) Eq.refl Eq.refl

step1 : CX01 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • SWAP02 • CX01 • SWAP02 • X0 • SWAP02
step1 = by-assoc-and (under (ε) (CX01 • SWAP02 • X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • SWAP02 • CX01 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CX21 • X0 • SWAP02
step2 = by-assoc-and (under (SWAP02) (X0 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

step3 : SWAP02 • CX21 • X0 • SWAP02 ≈ SWAP02 • X0 • CX21 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (bifunct_X_CX_b.proved)) Eq.refl Eq.refl

step4 : SWAP02 • X0 • CX21 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • CX01 • SWAP02 • SWAP02
step4 = by-assoc-and (under (SWAP02 • X0) (SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step5 : SWAP02 • X0 • SWAP02 • CX01 • SWAP02 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • CX01
step5 = by-assoc-and (under (SWAP02 • X0 • SWAP02 • CX01) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

step6 : SWAP02 • X0 • SWAP02 • CX01 ≈ X2 • CX01
step6 = by-assoc-and (under (ε) (CX01) (sym (axiom r015))) Eq.refl Eq.refl

proved : CX01 • X2 ≈ X2 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
