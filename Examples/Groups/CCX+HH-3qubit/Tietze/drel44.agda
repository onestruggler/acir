{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel44 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_a as bifunct_Z_K_a
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_a as bifunct_Z_SWAP_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel78 as drel78

step0 : CZ02 • Z0 ≈ K12 • K12 • CZ02 • Z0
step0 = by-assoc-and (under (ε) (CZ02 • Z0) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ02 • Z0 ≈ K12 • CX02 • K12 • Z0
step1 = by-assoc-and (under (K12) (Z0) (drel47.proved)) Eq.refl Eq.refl

step2 : K12 • CX02 • K12 • Z0 ≈ K12 • CX02 • Z0 • K12
step2 = by-assoc-and (under (K12 • CX02) (ε) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

step3 : K12 • CX02 • Z0 • K12 ≈ K12 • SWAP12 • CX01 • SWAP12 • Z0 • K12
step3 = by-assoc-and (under (K12) (Z0 • K12) (axiom r009)) Eq.refl Eq.refl

step4 : K12 • SWAP12 • CX01 • SWAP12 • Z0 • K12 ≈ K12 • SWAP12 • CX01 • Z0 • SWAP12 • K12
step4 = by-assoc-and (under (K12 • SWAP12 • CX01) (K12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

step5 : K12 • SWAP12 • CX01 • Z0 • SWAP12 • K12 ≈ K12 • SWAP12 • Z0 • CX01 • SWAP12 • K12
step5 = by-assoc-and (under (K12 • SWAP12) (SWAP12 • K12) (drel78.proved)) Eq.refl Eq.refl

step6 : K12 • SWAP12 • Z0 • CX01 • SWAP12 • K12 ≈ K12 • Z0 • SWAP12 • CX01 • SWAP12 • K12
step6 = by-assoc-and (under (K12) (CX01 • SWAP12 • K12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

step7 : K12 • Z0 • SWAP12 • CX01 • SWAP12 • K12 ≈ Z0 • K12 • SWAP12 • CX01 • SWAP12 • K12
step7 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12 • K12) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

step8 : Z0 • K12 • SWAP12 • CX01 • SWAP12 • K12 ≈ Z0 • K12 • CX02 • K12
step8 = by-assoc-and (under (Z0 • K12) (K12) (sym (axiom r009))) Eq.refl Eq.refl

step9 : Z0 • K12 • CX02 • K12 ≈ Z0 • K12 • K12 • CZ02
step9 = by-assoc-and (under (Z0 • K12) (ε) (sym (drel47.proved))) Eq.refl Eq.refl

step10 : Z0 • K12 • K12 • CZ02 ≈ Z0 • CZ02
step10 = by-assoc-and (under (Z0) (CZ02) (axiom r023)) Eq.refl Eq.refl

proved : CZ02 • Z0 ≈ Z0 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
