{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_a where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b as bifunct_X_CX_b

step0 : X0 • SWAP12 ≈ X0 • CX12 • CX21 • CX12
step0 = by-assoc-and (under (X0) (ε) (axiom r008)) Eq.refl Eq.refl

step1 : X0 • CX12 • CX21 • CX12 ≈ CX12 • X0 • CX21 • CX12
step1 = by-assoc-and (under (ε) (CX21 • CX12) (sym (axiom r026))) Eq.refl Eq.refl

step2 : CX12 • X0 • CX21 • CX12 ≈ CX12 • CX21 • X0 • CX12
step2 = by-assoc-and (under (CX12) (CX12) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

step3 : CX12 • CX21 • X0 • CX12 ≈ CX12 • CX21 • CX12 • X0
step3 = by-assoc-and (under (CX12 • CX21) (ε) (sym (axiom r026))) Eq.refl Eq.refl

step4 : CX12 • CX21 • CX12 • X0 ≈ SWAP12 • X0
step4 = by-assoc-and (under (ε) (X0) (sym (axiom r008))) Eq.refl Eq.refl

proved : X0 • SWAP12 ≈ SWAP12 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
