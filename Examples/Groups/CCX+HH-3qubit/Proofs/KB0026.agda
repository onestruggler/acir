{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0026 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CX10 ≈ K01 • CX01 • K01
p0 = by-assoc-and (axiom r012) Eq.refl Eq.refl

p1 : CX10 ≈ CX10
p1 = refl

p2 : K01 • CX01 • K01 ≈ K01 • CX01 • K01
p2 = refl

p3 : CX10 ≈ K01 • CX01 • K01
p3 = trans (sym p1) (trans p0 p2)

p4 : K01 • CX01 • K01 ≈ CX10
p4 = sym p3

proved : K01 • CX01 • K01 ≈ CX10
proved = p4
