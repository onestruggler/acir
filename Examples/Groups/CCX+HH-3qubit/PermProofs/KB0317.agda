{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0317 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316

p0 : X0 • X2 • CX20 • CX20 ≈ CX20 • X2 • CX20
p0 = by-assoc-and (under (ε) (CX20) B316.proved) Eq.refl Eq.refl

p1 : X0 • X2 • CX20 • CX20 ≈ X0 • X2
p1 = by-assoc-and (under (X0 • X2) (ε) B9.proved) Eq.refl Eq.refl

p2 : CX20 • X2 • CX20 ≈ X0 • X2
p2 = trans (sym p0) p1

p3 : CX20 • X2 • CX20 ≈ CX20 • X2 • CX20
p3 = refl

p4 : X0 • X2 ≈ X0 • X2
p4 = refl

p5 : CX20 • X2 • CX20 ≈ X0 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • X2 • CX20 ≈ X0 • X2
proved = p5
