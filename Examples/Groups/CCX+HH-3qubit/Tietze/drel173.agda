{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel173 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_a as bifunct_Z_SWAP_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel168 as drel168
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : CZ02 • Z0 • CX02 ≈ CZ02 • Z0 • SWAP12 • CX01 • SWAP12
step0 = by-assoc-and (under (CZ02 • Z0) (ε) (axiom r009)) Eq.refl Eq.refl

step1 : CZ02 • Z0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • Z0 • SWAP12 • CX01 • SWAP12
step1 = by-assoc-and (under (ε) (Z0 • SWAP12 • CX01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step2 : SWAP12 • CZ01 • SWAP12 • Z0 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • Z0 • CX01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12) (CX01 • SWAP12) (bifunct_Z_SWAP_a.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CZ01 • SWAP12 • SWAP12 • Z0 • CX01 • SWAP12 ≈ SWAP12 • CZ01 • Z0 • CX01 • SWAP12
step3 = by-assoc-and (under (SWAP12 • CZ01) (Z0 • CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CZ01 • Z0 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CZ01 • SWAP12
step4 = by-assoc-and (under (SWAP12) (SWAP12) (sym (drel168.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CX01 • CZ01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CZ01 • SWAP12
step5 = by-assoc-and (under (SWAP12 • CX01) (CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CX01 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ02
step6 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

step7 : SWAP12 • CX01 • SWAP12 • CZ02 ≈ CX02 • CZ02
step7 = by-assoc-and (under (ε) (CZ02) (sym (axiom r009))) Eq.refl Eq.refl

proved : CZ02 • Z0 • CX02 ≈ CX02 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
