{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1630 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1628 as B1628

p0 : CX01 • CX21 • X2 • CX20 • CX01 • CX01 ≈ X1 • X2 • CX20 • CX01
p0 = by-assoc-and (under (ε) (CX01) B1628.proved) Eq.refl Eq.refl

p1 : CX01 • CX21 • X2 • CX20 • CX01 • CX01 ≈ CX01 • CX21 • X2 • CX20
p1 = by-assoc-and (under (CX01 • CX21 • X2 • CX20) (ε) B13.proved) Eq.refl Eq.refl

p2 : X1 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20
p2 = trans (sym p0) p1

p3 : X1 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20 • CX01
p3 = refl

p4 : CX01 • CX21 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
p4 = refl

p5 : X1 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • CX21 • X2 • CX20 ≈ X1 • X2 • CX20 • CX01
p6 = sym p5

proved : CX01 • CX21 • X2 • CX20 ≈ X1 • X2 • CX20 • CX01
proved = p6
