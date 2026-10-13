{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel161 as drel161
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10

step0 : CX01 ≈ CX01 • CX10 • CX10
step0 = by-assoc-and (under (CX01) (ε) (sym (elim_CX10.proved))) Eq.refl Eq.refl

step1 : CX01 • CX10 • CX10 ≈ CX01 • CX10 • CX01 • CX01 • CX10
step1 = by-assoc-and (under (CX01 • CX10) (CX10) (sym (axiom r022))) Eq.refl Eq.refl

step2 : CX01 • CX10 • CX01 • CX01 • CX10 ≈ SWAP01 • CX01 • CX10
step2 = by-assoc-and (under (ε) (CX01 • CX10) (sym (axiom r013))) Eq.refl Eq.refl

step3 : SWAP01 • CX01 • CX10 ≈ SWAP01 • CX10 • SWAP01
step3 = by-assoc-and (under (SWAP01) (ε) (drel161.proved)) Eq.refl Eq.refl

proved : CX01 ≈ SWAP01 • CX10 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))
