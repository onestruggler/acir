{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0301 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0300 as B300

p0 : CX20 • CX20 • CX01 • CX20 • CX01 ≈ CX20 • CX21
p0 = by-assoc-and (under (CX20) (ε) B300.proved) Eq.refl Eq.refl

p1 : CX20 • CX20 • CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX01
p1 = by-assoc-and (under (ε) (CX01 • CX20 • CX01) B9.proved) Eq.refl Eq.refl

p2 : CX20 • CX21 ≈ CX01 • CX20 • CX01
p2 = trans (sym p0) p1

p3 : CX20 • CX21 ≈ CX20 • CX21
p3 = refl

p4 : CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX01
p4 = refl

p5 : CX20 • CX21 ≈ CX01 • CX20 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • CX20 • CX01 ≈ CX20 • CX21
p6 = sym p5

proved : CX01 • CX20 • CX01 ≈ CX20 • CX21
proved = p6
