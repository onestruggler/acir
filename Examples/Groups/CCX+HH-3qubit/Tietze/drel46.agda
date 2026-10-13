{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel46 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : K12 • CX21 ≈ K12 • CX21 • K12 • K12
step0 = by-assoc-and (under (K12 • CX21) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • CX21 • K12 • K12 ≈ CX12 • K12
step1 = by-assoc-and (under (ε) (K12) (sym (axiom r007))) Eq.refl Eq.refl

proved : K12 • CX21 ≈ CX12 • K12
proved = trans step0 (trans step1 (refl))
