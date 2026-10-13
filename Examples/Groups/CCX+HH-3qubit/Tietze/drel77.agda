{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel77 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel58 as drel58
import Examples.Groups.CCX+HH-3qubit.Tietze.drel59 as drel59
import Examples.Groups.CCX+HH-3qubit.Tietze.drel82 as drel82

step0 : CX10 • Z1 ≈ K01 • CX01 • K01 • Z1
step0 = by-assoc-and (under (ε) (Z1) (axiom r012)) Eq.refl Eq.refl

step1 : K01 • CX01 • K01 • Z1 ≈ K01 • CX01 • X1 • K01
step1 = by-assoc-and (under (K01 • CX01) (ε) (sym (drel59.proved))) Eq.refl Eq.refl

step2 : K01 • CX01 • X1 • K01 ≈ K01 • X1 • CX01 • K01
step2 = by-assoc-and (under (K01) (K01) (sym (drel82.proved))) Eq.refl Eq.refl

step3 : K01 • X1 • CX01 • K01 ≈ Z1 • K01 • CX01 • K01
step3 = by-assoc-and (under (ε) (CX01 • K01) (sym (drel58.proved))) Eq.refl Eq.refl

step4 : Z1 • K01 • CX01 • K01 ≈ Z1 • CX10
step4 = by-assoc-and (under (Z1) (ε) (sym (axiom r012))) Eq.refl Eq.refl

proved : CX10 • Z1 ≈ Z1 • CX10
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
