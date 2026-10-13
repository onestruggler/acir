{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1628 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0225 as B225
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0301 as B301
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0569 as B569

p0 : CX21 • X2 • CX01 • CX20 • CX01 ≈ CX21 • X2 • CX20 • CX21
p0 = by-assoc-and (under (CX21 • X2) (ε) B301.proved) Eq.refl Eq.refl

p1 : CX21 • X2 • CX01 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20 • CX01
p1 = by-assoc-and (under (ε) (CX20 • CX01) B225.proved) Eq.refl Eq.refl

p2 : CX21 • X2 • CX20 • CX21 ≈ CX01 • CX21 • X2 • CX20 • CX01
p2 = trans (sym p0) p1

p3 : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
p3 = by-assoc-and (under (ε) (ε) B569.proved) Eq.refl Eq.refl

p4 : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
p4 = trans p3 (refl)

p5 : CX01 • CX21 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20 • CX01
p5 = refl

p6 : X1 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20 • CX01
p6 = trans (sym p4) (trans p2 p5)

p7 : CX01 • CX21 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20
p7 = sym p6

proved : CX01 • CX21 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20
proved = p7
