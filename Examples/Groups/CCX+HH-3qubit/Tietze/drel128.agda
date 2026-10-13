{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel128 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : K12 • CCX01 ≈ K12 • K12 • CCX02 • K12
step0 = by-assoc-and (under (K12) (ε) (axiom r017)) Eq.refl Eq.refl

step1 : K12 • K12 • CCX02 • K12 ≈ CCX02 • K12
step1 = by-assoc-and (under (ε) (CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

proved : K12 • CCX01 ≈ CCX02 • K12
proved = trans step0 (trans step1 (refl))
