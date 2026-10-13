{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd7 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

step0 : CX01 • CCX12 • CX01 ≈ CX01 • CX01 • CCX02 • CCX12 • CCX02
step0 = by-assoc-and (under (CX01) (ε) (axiom r045)) Eq.refl Eq.refl

step1 : CX01 • CX01 • CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02
step1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CCX02) (axiom r022)) Eq.refl Eq.refl

proved : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
proved = trans step0 (trans step1 (refl))
