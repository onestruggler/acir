{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_a as bifunct_X_SWAP_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as symmetry_X_c

step0 : X0 • CX02 ≈ X0 • SWAP12 • CX01 • SWAP12
step0 = by-assoc-and (under (X0) (ε) (axiom r009)) Eq.refl Eq.refl

step1 : X0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • X0 • CX01 • SWAP12
step1 = by-assoc-and (under (ε) (CX01 • SWAP12) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

step2 : SWAP12 • X0 • CX01 • SWAP12 ≈ SWAP12 • CX01 • X1 • X0 • SWAP12
step2 = by-assoc-and (under (SWAP12) (SWAP12) (drel162.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CX01 • X1 • X0 • SWAP12 ≈ SWAP12 • CX01 • X1 • SWAP12 • X0
step3 = by-assoc-and (under (SWAP12 • CX01 • X1) (ε) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CX01 • X1 • SWAP12 • X0 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 • X0
step4 = by-assoc-and (under (SWAP12 • CX01) (X1 • SWAP12 • X0) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 • X0 ≈ SWAP12 • CX01 • SWAP12 • X2 • X0
step5 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (X0) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CX01 • SWAP12 • X2 • X0 ≈ CX02 • X2 • X0
step6 = by-assoc-and (under (ε) (X2 • X0) (sym (axiom r009))) Eq.refl Eq.refl

proved : X0 • CX02 ≈ CX02 • X2 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
