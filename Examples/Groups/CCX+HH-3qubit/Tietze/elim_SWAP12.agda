{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as elim_CX21

step0 : SWAP12 • SWAP12 ≈ SWAP12 • CX12 • CX21 • CX12
step0 = by-assoc-and (under (SWAP12) (ε) (axiom r008)) Eq.refl Eq.refl

step1 : SWAP12 • CX12 • CX21 • CX12 ≈ CX12 • CX21 • CX12 • CX12 • CX21 • CX12
step1 = by-assoc-and (under (ε) (CX12 • CX21 • CX12) (axiom r008)) Eq.refl Eq.refl

step2 : CX12 • CX21 • CX12 • CX12 • CX21 • CX12 ≈ CX12 • CX21 • CX21 • CX12
step2 = by-assoc-and (under (CX12 • CX21) (CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

step3 : CX12 • CX21 • CX21 • CX12 ≈ CX12 • CX12
step3 = by-assoc-and (under (CX12) (CX12) (elim_CX21.proved)) Eq.refl Eq.refl

step4 : CX12 • CX12 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

proved : SWAP12 • SWAP12 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
