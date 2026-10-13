{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel161 as drel161
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b as symmetry_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : SWAP01 ≈ CX10 • CX10 • SWAP01
step0 = by-assoc-and (under (ε) (SWAP01) (sym (elim_CX10.proved))) Eq.refl Eq.refl

step1 : CX10 • CX10 • SWAP01 ≈ CX10 • CX01 • CX10
step1 = by-assoc-and (under (CX10) (ε) (sym (drel161.proved))) Eq.refl Eq.refl

step2 : CX10 • CX01 • CX10 ≈ CX10 • CX01 • SWAP02 • CX12 • SWAP02
step2 = by-assoc-and (under (CX10 • CX01) (ε) (symmetry_CX_b.proved)) Eq.refl Eq.refl

step3 : CX10 • CX01 • SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • SWAP02 • CX01 • SWAP02 • CX12 • SWAP02
step3 = by-assoc-and (under (ε) (CX01 • SWAP02 • CX12 • SWAP02) (symmetry_CX_b.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX12 • SWAP02 • CX01 • SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • CX21 • CX12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CX12) (CX12 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CX12 • CX21 • CX12 • SWAP02 ≈ SWAP02 • SWAP12 • SWAP02
step5 = by-assoc-and (under (SWAP02) (SWAP02) (sym (axiom r008))) Eq.refl Eq.refl

proved : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
