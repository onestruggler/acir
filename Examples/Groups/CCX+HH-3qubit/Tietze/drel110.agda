{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel110 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel134 as drel134

step0 : CX21 • CX02 ≈ CX21 • CX02 • CX01 • CX01
step0 = by-assoc-and (under (CX21 • CX02) (ε) (sym (axiom r022))) Eq.refl Eq.refl

step1 : CX21 • CX02 • CX01 • CX01 ≈ CX02 • CX21 • CX01
step1 = by-assoc-and (under (ε) (CX01) (sym (drel134.proved))) Eq.refl Eq.refl

proved : CX21 • CX02 ≈ CX02 • CX21 • CX01
proved = trans step0 (trans step1 (refl))
