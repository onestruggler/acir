{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_d as bifunct_X_CX_d
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_K_b as bifunct_X_K_b

step0 : CX10 • X2 ≈ K01 • CX01 • K01 • X2
step0 = by-assoc-and (under (ε) (X2) (axiom r012)) Eq.refl Eq.refl

step1 : K01 • CX01 • K01 • X2 ≈ K01 • CX01 • X2 • K01
step1 = by-assoc-and (under (K01 • CX01) (ε) (sym (bifunct_X_K_b.proved))) Eq.refl Eq.refl

step2 : K01 • CX01 • X2 • K01 ≈ K01 • X2 • CX01 • K01
step2 = by-assoc-and (under (K01) (K01) (bifunct_X_CX_d.proved)) Eq.refl Eq.refl

step3 : K01 • X2 • CX01 • K01 ≈ X2 • K01 • CX01 • K01
step3 = by-assoc-and (under (ε) (CX01 • K01) (sym (bifunct_X_K_b.proved))) Eq.refl Eq.refl

step4 : X2 • K01 • CX01 • K01 ≈ X2 • CX10
step4 = by-assoc-and (under (X2) (ε) (sym (axiom r012))) Eq.refl Eq.refl

proved : CX10 • X2 ≈ X2 • CX10
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
