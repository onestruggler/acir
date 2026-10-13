{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_K_a where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel154 as drel154
import Examples.Groups.CCX+HH-3qubit.Tietze.drel30 as drel30
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as elim_CX21
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : K12 ≈ K12 • SWAP12 • SWAP12
step0 = by-assoc-and (under (K12) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : K12 • SWAP12 • SWAP12 ≈ K12 • CX12 • CX21 • CX12 • SWAP12
step1 = by-assoc-and (under (K12) (SWAP12) (axiom r008)) Eq.refl Eq.refl

step2 : K12 • CX12 • CX21 • CX12 • SWAP12 ≈ CX21 • K12 • CX21 • CX12 • SWAP12
step2 = by-assoc-and (under (ε) (CX21 • CX12 • SWAP12) (sym (drel30.proved))) Eq.refl Eq.refl

step3 : CX21 • K12 • CX21 • CX12 • SWAP12 ≈ CX21 • CX12 • K12 • CX12 • SWAP12
step3 = by-assoc-and (under (CX21) (CX12 • SWAP12) (drel46.proved)) Eq.refl Eq.refl

step4 : CX21 • CX12 • K12 • CX12 • SWAP12 ≈ CX21 • CX12 • CX21 • K12 • SWAP12
step4 = by-assoc-and (under (CX21 • CX12) (SWAP12) (sym (drel30.proved))) Eq.refl Eq.refl

step5 : CX21 • CX12 • CX21 • K12 • SWAP12 ≈ CX21 • CX21 • SWAP12 • K12 • SWAP12
step5 = by-assoc-and (under (CX21) (K12 • SWAP12) (drel154.proved)) Eq.refl Eq.refl

step6 : CX21 • CX21 • SWAP12 • K12 • SWAP12 ≈ SWAP12 • K12 • SWAP12
step6 = by-assoc-and (under (ε) (SWAP12 • K12 • SWAP12) (elim_CX21.proved)) Eq.refl Eq.refl

proved : K12 ≈ SWAP12 • K12 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
