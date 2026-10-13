{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel184 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel110 as drel110
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02

step0 : CX21 • CX01 • CX02 ≈ CX02 • CX02 • CX21 • CX01 • CX02
step0 = by-assoc-and (under (ε) (CX21 • CX01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step1 : CX02 • CX02 • CX21 • CX01 • CX02 ≈ CX02 • CX21 • CX02 • CX02
step1 = by-assoc-and (under (CX02) (CX02) (sym (drel110.proved))) Eq.refl Eq.refl

step2 : CX02 • CX21 • CX02 • CX02 ≈ CX02 • CX21
step2 = by-assoc-and (under (CX02 • CX21) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

proved : CX21 • CX01 • CX02 ≈ CX02 • CX21
proved = trans step0 (trans step1 (trans step2 (refl)))
