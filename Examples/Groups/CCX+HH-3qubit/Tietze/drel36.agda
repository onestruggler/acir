{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel36 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel128 as drel128
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel92 as drel92

step0 : CZ01 • CCX01 ≈ K12 • CX01 • K12 • CCX01
step0 = by-assoc-and (under (ε) (CCX01) (axiom r001)) Eq.refl Eq.refl

step1 : K12 • CX01 • K12 • CCX01 ≈ K12 • CX01 • CCX02 • K12
step1 = by-assoc-and (under (K12 • CX01) (ε) (drel128.proved)) Eq.refl Eq.refl

step2 : K12 • CX01 • CCX02 • K12 ≈ K12 • CCX02 • CX01 • K12
step2 = by-assoc-and (under (K12) (K12) (sym (drel92.proved))) Eq.refl Eq.refl

step3 : K12 • CCX02 • CX01 • K12 ≈ CCX01 • K12 • CX01 • K12
step3 = by-assoc-and (under (ε) (CX01 • K12) (sym (drel29.proved))) Eq.refl Eq.refl

step4 : CCX01 • K12 • CX01 • K12 ≈ CCX01 • CZ01
step4 = by-assoc-and (under (CCX01) (ε) (sym (axiom r001))) Eq.refl Eq.refl

proved : CZ01 • CCX01 ≈ CCX01 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
