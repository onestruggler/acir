{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel90 as drel90
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12

step0 : CX10 • CCX01 • CX10 ≈ CCX01 • CX12 • CX10 • CX10
step0 = by-assoc-and (under (ε) (CX10) (drel90.proved)) Eq.refl Eq.refl

step1 : CCX01 • CX12 • CX10 • CX10 ≈ CCX01 • CX12
step1 = by-assoc-and (under (CCX01 • CX12) (ε) (elim_CX10.proved)) Eq.refl Eq.refl

step2 : CCX01 • CX12 ≈ X0 • X0 • CCX01 • CX12
step2 = by-assoc-and (under (ε) (CCX01 • CX12) (sym (axiom r021))) Eq.refl Eq.refl

step3 : X0 • X0 • CCX01 • CX12 ≈ X0 • CCX01 • CX12 • X0 • CX12
step3 = by-assoc-and (under (X0) (CX12) (axiom r042)) Eq.refl Eq.refl

step4 : X0 • CCX01 • CX12 • X0 • CX12 ≈ X0 • CCX01 • X0 • CX12 • CX12
step4 = by-assoc-and (under (X0 • CCX01) (CX12) (axiom r026)) Eq.refl Eq.refl

step5 : X0 • CCX01 • X0 • CX12 • CX12 ≈ X0 • CCX01 • X0
step5 = by-assoc-and (under (X0 • CCX01 • X0) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

proved : CX10 • CCX01 • CX10 ≈ X0 • CCX01 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
