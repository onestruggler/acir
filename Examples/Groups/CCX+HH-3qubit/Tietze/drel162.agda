{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel162 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : X0 • CX01 ≈ X0 • CX01 • X0 • X0
step0 = by-assoc-and (under (X0 • CX01) (ε) (sym (axiom r021))) Eq.refl Eq.refl

step1 : X0 • CX01 • X0 • X0 ≈ CX01 • CX01 • X0 • CX01 • X0 • X0
step1 = by-assoc-and (under (ε) (X0 • CX01 • X0 • X0) (sym (axiom r022))) Eq.refl Eq.refl

step2 : CX01 • CX01 • X0 • CX01 • X0 • X0 ≈ CX01 • X1 • X0
step2 = by-assoc-and (under (CX01) (X0) (sym (axiom r002))) Eq.refl Eq.refl

proved : X0 • CX01 ≈ CX01 • X1 • X0
proved = trans step0 (trans step1 (trans step2 (refl)))
