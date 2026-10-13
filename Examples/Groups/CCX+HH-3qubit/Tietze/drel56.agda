{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel56 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel63 as drel63
import Examples.Groups.CCX+HH-3qubit.Tietze.drel92 as drel92

step0 : CCX12 • CX10 ≈ K01 • K01 • CCX12 • CX10
step0 = by-assoc-and (under (ε) (CCX12 • CX10) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • CCX12 • CX10 ≈ K01 • CCX02 • K01 • CX10
step1 = by-assoc-and (under (K01) (CX10) (drel63.proved)) Eq.refl Eq.refl

step2 : K01 • CCX02 • K01 • CX10 ≈ K01 • CCX02 • K01 • K01 • CX01 • K01
step2 = by-assoc-and (under (K01 • CCX02 • K01) (ε) (axiom r012)) Eq.refl Eq.refl

step3 : K01 • CCX02 • K01 • K01 • CX01 • K01 ≈ K01 • CCX02 • CX01 • K01
step3 = by-assoc-and (under (K01 • CCX02) (CX01 • K01) (axiom r025)) Eq.refl Eq.refl

step4 : K01 • CCX02 • CX01 • K01 ≈ K01 • CX01 • CCX02 • K01
step4 = by-assoc-and (under (K01) (K01) (drel92.proved)) Eq.refl Eq.refl

step5 : K01 • CX01 • CCX02 • K01 ≈ K01 • CX01 • K01 • CCX12
step5 = by-assoc-and (under (K01 • CX01) (ε) (sym (drel63.proved))) Eq.refl Eq.refl

step6 : K01 • CX01 • K01 • CCX12 ≈ CX10 • CCX12
step6 = by-assoc-and (under (ε) (CCX12) (sym (axiom r012))) Eq.refl Eq.refl

proved : CCX12 • CX10 ≈ CX10 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
