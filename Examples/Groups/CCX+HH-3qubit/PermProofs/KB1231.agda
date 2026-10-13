{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1231 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0158 as B158
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316

p0 : X0 • CX01 • X0 • X2 • CX20 ≈ X0 • CX01 • CX20 • X2
p0 = by-assoc-and (under (X0 • CX01) (ε) B316.proved) Eq.refl Eq.refl

p1 : X0 • CX01 • X0 • X2 • CX20 ≈ X1 • CX01 • X2 • CX20
p1 = by-assoc-and (under (ε) (X2 • CX20) B158.proved) Eq.refl Eq.refl

p2 : X0 • CX01 • CX20 • X2 ≈ X1 • CX01 • X2 • CX20
p2 = trans (sym p0) p1

p3 : X0 • CX01 • CX20 • X2 ≈ X0 • CX01 • CX20 • X2
p3 = refl

p4 : X1 • CX01 • X2 • CX20 ≈ X1 • X2 • CX01 • CX20
p4 = by-assoc-and (under (X1) (CX20) B22.proved) Eq.refl Eq.refl

p5 : X1 • CX01 • X2 • CX20 ≈ X1 • X2 • CX01 • CX20
p5 = trans p4 (refl)

p6 : X0 • CX01 • CX20 • X2 ≈ X1 • X2 • CX01 • CX20
p6 = trans (sym p3) (trans p2 p5)

p7 : X1 • X2 • CX01 • CX20 ≈ X0 • CX01 • CX20 • X2
p7 = sym p6

proved : X1 • X2 • CX01 • CX20 ≈ X0 • CX01 • CX20 • X2
proved = p7
