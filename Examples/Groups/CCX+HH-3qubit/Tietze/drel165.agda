{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel165 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel41 as drel41

step0 : CX12 • CZ01 ≈ CX12 • K12 • CX01 • K12
step0 = by-assoc-and (under (CX12) (ε) (axiom r001)) Eq.refl Eq.refl

step1 : CX12 • K12 • CX01 • K12 ≈ K12 • CX21 • K12 • K12 • CX01 • K12
step1 = by-assoc-and (under (ε) (K12 • CX01 • K12) (axiom r007)) Eq.refl Eq.refl

step2 : K12 • CX21 • K12 • K12 • CX01 • K12 ≈ K12 • CX21 • CX01 • K12
step2 = by-assoc-and (under (K12 • CX21) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

step3 : K12 • CX21 • CX01 • K12 ≈ K12 • CX01 • CX21 • K12
step3 = by-assoc-and (under (K12) (K12) (sym (drel41.proved))) Eq.refl Eq.refl

step4 : K12 • CX01 • CX21 • K12 ≈ K12 • CX01 • K12 • K12 • CX21 • K12
step4 = by-assoc-and (under (K12 • CX01) (CX21 • K12) (sym (axiom r023))) Eq.refl Eq.refl

step5 : K12 • CX01 • K12 • K12 • CX21 • K12 ≈ K12 • CX01 • K12 • CX12
step5 = by-assoc-and (under (K12 • CX01 • K12) (ε) (sym (axiom r007))) Eq.refl Eq.refl

step6 : K12 • CX01 • K12 • CX12 ≈ CZ01 • CX12
step6 = by-assoc-and (under (ε) (CX12) (sym (axiom r001))) Eq.refl Eq.refl

proved : CX12 • CZ01 ≈ CZ01 • CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
