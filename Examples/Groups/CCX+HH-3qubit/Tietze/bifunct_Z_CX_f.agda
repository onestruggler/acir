{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_f where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_e as bifunct_Z_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_K_b as bifunct_Z_K_b

step0 : Z2 • CX10 ≈ Z2 • K01 • CX01 • K01
step0 = by-assoc-and (under (Z2) (ε) (axiom r012)) Eq.refl Eq.refl

step1 : Z2 • K01 • CX01 • K01 ≈ K01 • Z2 • CX01 • K01
step1 = by-assoc-and (under (ε) (CX01 • K01) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

step2 : K01 • Z2 • CX01 • K01 ≈ K01 • CX01 • Z2 • K01
step2 = by-assoc-and (under (K01) (K01) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

step3 : K01 • CX01 • Z2 • K01 ≈ K01 • CX01 • K01 • Z2
step3 = by-assoc-and (under (K01 • CX01) (ε) (bifunct_Z_K_b.proved)) Eq.refl Eq.refl

step4 : K01 • CX01 • K01 • Z2 ≈ CX10 • Z2
step4 = by-assoc-and (under (ε) (Z2) (sym (axiom r012))) Eq.refl Eq.refl

proved : Z2 • CX10 ≈ CX10 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
