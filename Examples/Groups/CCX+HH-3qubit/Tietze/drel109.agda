{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel109 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel164 as drel164
import Examples.Groups.CCX+HH-3qubit.Tietze.drel166 as drel166
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02

step0 : CZ12 • CX01 ≈ CZ02 • CZ02 • CZ12 • CX01
step0 = by-assoc-and (under (ε) (CZ12 • CX01) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step1 : CZ02 • CZ02 • CZ12 • CX01 ≈ CZ02 • CZ12 • CZ02 • CX01
step1 = by-assoc-and (under (CZ02) (CX01) (drel164.proved)) Eq.refl Eq.refl

step2 : CZ02 • CZ12 • CZ02 • CX01 ≈ CZ02 • CX01 • CZ12
step2 = by-assoc-and (under (CZ02) (ε) (sym (axiom r043))) Eq.refl Eq.refl

step3 : CZ02 • CX01 • CZ12 ≈ CX01 • CZ02 • CZ12
step3 = by-assoc-and (under (ε) (CZ12) (sym (drel166.proved))) Eq.refl Eq.refl

proved : CZ12 • CX01 ≈ CX01 • CZ02 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))
