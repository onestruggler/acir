{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12

step0 : CX21 • CX21 ≈ K12 • K12 • CX21 • CX21
step0 = by-assoc-and (under (ε) (CX21 • CX21) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CX21 • CX21 ≈ K12 • CX12 • K12 • CX21
step1 = by-assoc-and (under (K12) (CX21) (drel46.proved)) Eq.refl Eq.refl

step2 : K12 • CX12 • K12 • CX21 ≈ K12 • CX12 • CX12 • K12
step2 = by-assoc-and (under (K12 • CX12) (ε) (drel46.proved)) Eq.refl Eq.refl

step3 : K12 • CX12 • CX12 • K12 ≈ K12 • K12
step3 = by-assoc-and (under (K12) (K12) (elim_CX12.proved)) Eq.refl Eq.refl

step4 : K12 • K12 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CX21 • CX21 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
