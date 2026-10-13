{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel43 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_a as bifunct_Z_K_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel49 as drel49
import Examples.Groups.CCX+HH-3qubit.Tietze.drel50 as drel50
import Examples.Groups.CCX+HH-3qubit.Tietze.drel78 as drel78

step0 : CZ01 • Z0 ≈ K12 • K12 • CZ01 • Z0
step0 = by-assoc-and (under (ε) (CZ01 • Z0) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ01 • Z0 ≈ K12 • CX01 • K12 • Z0
step1 = by-assoc-and (under (K12) (Z0) (drel49.proved)) Eq.refl Eq.refl

step2 : K12 • CX01 • K12 • Z0 ≈ K12 • CX01 • Z0 • K12
step2 = by-assoc-and (under (K12 • CX01) (ε) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

step3 : K12 • CX01 • Z0 • K12 ≈ K12 • Z0 • CX01 • K12
step3 = by-assoc-and (under (K12) (K12) (drel78.proved)) Eq.refl Eq.refl

step4 : K12 • Z0 • CX01 • K12 ≈ Z0 • K12 • CX01 • K12
step4 = by-assoc-and (under (ε) (CX01 • K12) (sym (bifunct_Z_K_a.proved))) Eq.refl Eq.refl

step5 : Z0 • K12 • CX01 • K12 ≈ Z0 • CZ01 • K12 • K12
step5 = by-assoc-and (under (Z0) (K12) (sym (drel50.proved))) Eq.refl Eq.refl

step6 : Z0 • CZ01 • K12 • K12 ≈ Z0 • CZ01
step6 = by-assoc-and (under (Z0 • CZ01) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CZ01 • Z0 ≈ Z0 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
