{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : X1 • K12 ≈ K12 • K12 • X1 • K12
step0 = by-assoc-and (under (ε) (X1 • K12) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • X1 • K12 ≈ K12 • Z1
step1 = by-assoc-and (under (K12) (ε) (sym (axiom r004))) Eq.refl Eq.refl

proved : X1 • K12 ≈ K12 • Z1
proved = trans step0 (trans step1 (refl))
