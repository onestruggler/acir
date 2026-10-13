{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel171 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel42 as drel42
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e

step0 : Z1 • CX01 ≈ Z1 • SWAP01 • CX10 • SWAP01
step0 = by-assoc-and (under (Z1) (ε) (symmetry_CX_e.proved)) Eq.refl Eq.refl

step1 : Z1 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • CX10 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CX10 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • CX10 • SWAP01 ≈ SWAP01 • Z0 • CX10 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (CX10 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • CX10 • SWAP01 ≈ SWAP01 • CX10 • Z1 • Z0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel42.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX10 • Z1 • Z0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • Z0 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CX10) (Z0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step5 : SWAP01 • CX10 • SWAP01 • Z0 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • CX10 • SWAP01 • Z0 • Z1
step5 = by-assoc-and (under (SWAP01 • CX10 • SWAP01 • Z0) (ε) (sym (axiom r034))) Eq.refl Eq.refl

step6 : SWAP01 • CX10 • SWAP01 • Z0 • Z1 ≈ CX01 • Z0 • Z1
step6 = by-assoc-and (under (ε) (Z0 • Z1) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

proved : Z1 • CX01 ≈ CX01 • Z0 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
