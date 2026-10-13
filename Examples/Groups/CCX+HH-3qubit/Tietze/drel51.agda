{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel51 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel25 as drel25
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel86 as drel86

step0 : Z1 • CCX01 ≈ K12 • X1 • K12 • CCX01
step0 = by-assoc-and (under (ε) (CCX01) (axiom r004)) Eq.refl Eq.refl

step1 : K12 • X1 • K12 • CCX01 ≈ K12 • X1 • CCX02 • K12
step1 = by-assoc-and (under (K12 • X1) (ε) (drel86.proved)) Eq.refl Eq.refl

step2 : K12 • X1 • CCX02 • K12 ≈ K12 • CCX02 • X1 • K12
step2 = by-assoc-and (under (K12) (K12) (drel25.proved)) Eq.refl Eq.refl

step3 : K12 • CCX02 • X1 • K12 ≈ CCX01 • K12 • X1 • K12
step3 = by-assoc-and (under (ε) (X1 • K12) (sym (drel29.proved))) Eq.refl Eq.refl

step4 : CCX01 • K12 • X1 • K12 ≈ CCX01 • Z1
step4 = by-assoc-and (under (CCX01) (ε) (sym (axiom r004))) Eq.refl Eq.refl

proved : Z1 • CCX01 ≈ CCX01 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
