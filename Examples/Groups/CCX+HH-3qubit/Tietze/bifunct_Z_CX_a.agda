{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_a where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_d as bifunct_Z_CX_d
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h as symmetry_CX_h

step0 : Z1 • CX20 ≈ SWAP01 • Z0 • SWAP01 • CX20
step0 = by-assoc-and (under (ε) (CX20) (axiom r034)) Eq.refl Eq.refl

step1 : SWAP01 • Z0 • SWAP01 • CX20 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • CX21 • SWAP01
step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01) (ε) (symmetry_CX_h.proved)) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • CX21 • SWAP01 ≈ SWAP01 • Z0 • CX21 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (CX21 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • CX21 • SWAP01 ≈ SWAP01 • CX21 • Z0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_Z_CX_d.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX21 • Z0 • SWAP01 ≈ SWAP01 • CX21 • SWAP01 • SWAP01 • Z0 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CX21) (Z0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step5 : SWAP01 • CX21 • SWAP01 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • CX21 • SWAP01 • Z1
step5 = by-assoc-and (under (SWAP01 • CX21 • SWAP01) (ε) (sym (axiom r034))) Eq.refl Eq.refl

step6 : SWAP01 • CX21 • SWAP01 • Z1 ≈ CX20 • Z1
step6 = by-assoc-and (under (ε) (Z1) (sym (symmetry_CX_h.proved))) Eq.refl Eq.refl

proved : Z1 • CX20 ≈ CX20 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
