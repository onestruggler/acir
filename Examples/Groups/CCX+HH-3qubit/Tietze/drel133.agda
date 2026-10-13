{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel133 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_c as bifunct_X_SWAP_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : X2 • CX21 ≈ X2 • SWAP02 • CX01 • SWAP02
step0 = by-assoc-and (under (X2) (ε) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step1 : X2 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CX01 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CX01 • SWAP02) (axiom r015)) Eq.refl Eq.refl

step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • X0 • CX01 • SWAP02
step2 = by-assoc-and (under (SWAP02 • X0) (CX01 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • X0 • CX01 • SWAP02 ≈ SWAP02 • CX01 • X1 • X0 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel162.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX01 • X1 • X0 • SWAP02 ≈ SWAP02 • CX01 • X1 • SWAP02 • SWAP02 • X0 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CX01 • X1) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CX01 • X1 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CX01 • X1 • SWAP02 • X2
step5 = by-assoc-and (under (SWAP02 • CX01 • X1 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

step6 : SWAP02 • CX01 • X1 • SWAP02 • X2 ≈ SWAP02 • CX01 • SWAP02 • X1 • X2
step6 = by-assoc-and (under (SWAP02 • CX01) (X2) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

step7 : SWAP02 • CX01 • SWAP02 • X1 • X2 ≈ CX21 • X1 • X2
step7 = by-assoc-and (under (ε) (X1 • X2) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

proved : X2 • CX21 ≈ CX21 • X1 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
