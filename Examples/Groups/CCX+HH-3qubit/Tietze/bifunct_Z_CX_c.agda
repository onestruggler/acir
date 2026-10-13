{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_b as bifunct_Z_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : Z1 • CX02 ≈ SWAP01 • Z0 • SWAP01 • CX02
step0 = by-assoc-and (under (ε) (CX02) (axiom r034)) Eq.refl Eq.refl

step1 : SWAP01 • Z0 • SWAP01 • CX02 ≈ SWAP01 • Z0 • SWAP01 • CX02 • SWAP01 • SWAP01
step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01 • CX02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • CX12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • CX12 • SWAP01 ≈ SWAP01 • CX12 • Z0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX12 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • Z0 • SWAP01
step4 = by-assoc-and (under (SWAP01) (Z0 • SWAP01) (axiom r030)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CX02 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • Z1
step5 = by-assoc-and (under (SWAP01 • SWAP01 • CX02) (ε) (sym (axiom r034))) Eq.refl Eq.refl

step6 : SWAP01 • SWAP01 • CX02 • Z1 ≈ CX02 • Z1
step6 = by-assoc-and (under (ε) (CX02 • Z1) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : Z1 • CX02 ≈ CX02 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
