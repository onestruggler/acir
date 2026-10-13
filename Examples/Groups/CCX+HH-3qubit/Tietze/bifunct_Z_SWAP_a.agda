{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_a where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_b as bifunct_Z_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_d as bifunct_Z_CX_d

step0 : Z0 • SWAP12 ≈ Z0 • CX12 • CX21 • CX12
step0 = by-assoc-and (under (Z0) (ε) (axiom r008)) Eq.refl Eq.refl

step1 : Z0 • CX12 • CX21 • CX12 ≈ CX12 • Z0 • CX21 • CX12
step1 = by-assoc-and (under (ε) (CX21 • CX12) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

step2 : CX12 • Z0 • CX21 • CX12 ≈ CX12 • CX21 • Z0 • CX12
step2 = by-assoc-and (under (CX12) (CX12) (bifunct_Z_CX_d.proved)) Eq.refl Eq.refl

step3 : CX12 • CX21 • Z0 • CX12 ≈ CX12 • CX21 • CX12 • Z0
step3 = by-assoc-and (under (CX12 • CX21) (ε) (bifunct_Z_CX_b.proved)) Eq.refl Eq.refl

step4 : CX12 • CX21 • CX12 • Z0 ≈ SWAP12 • Z0
step4 = by-assoc-and (under (ε) (Z0) (sym (axiom r008))) Eq.refl Eq.refl

proved : Z0 • SWAP12 ≈ SWAP12 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
