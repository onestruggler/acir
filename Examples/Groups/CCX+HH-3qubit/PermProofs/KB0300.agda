{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0300 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CX21 ≈ CX20 • CX01 • CX20 • CX01
p0 = by-assoc-and (axiom r006) Eq.refl Eq.refl

p1 : CX21 ≈ CX21
p1 = refl

p2 : CX20 • CX01 • CX20 • CX01 ≈ CX20 • CX01 • CX20 • CX01
p2 = refl

p3 : CX21 ≈ CX20 • CX01 • CX20 • CX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX20 • CX01 • CX20 • CX01 ≈ CX21
p4 = sym p3

proved : CX20 • CX01 • CX20 • CX01 ≈ CX21
proved = p4
