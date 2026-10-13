{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0614 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0303 as B303
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0309 as B309

p0 : CX01 • CX20 • CX21 • X0 ≈ CX20 • CX01 • X0
p0 = by-assoc-and (under (ε) (X0) B303.proved) Eq.refl Eq.refl

p1 : CX01 • CX20 • CX21 • X0 ≈ CX01 • CX20 • X0 • CX21
p1 = by-assoc-and (under (CX01 • CX20) (ε) B20.proved) Eq.refl Eq.refl

p2 : CX20 • CX01 • X0 ≈ CX01 • CX20 • X0 • CX21
p2 = trans (sym p0) p1

p3 : CX20 • CX01 • X0 ≈ CX20 • CX01 • X0
p3 = refl

p4 : CX01 • CX20 • X0 • CX21 ≈ CX01 • X0 • CX20 • CX21
p4 = by-assoc-and (under (CX01) (CX21) B309.proved) Eq.refl Eq.refl

p5 : CX01 • CX20 • X0 • CX21 ≈ CX01 • X0 • CX20 • CX21
p5 = trans p4 (refl)

p6 : CX20 • CX01 • X0 ≈ CX01 • X0 • CX20 • CX21
p6 = trans (sym p3) (trans p2 p5)

p7 : CX01 • X0 • CX20 • CX21 ≈ CX20 • CX01 • X0
p7 = sym p6

proved : CX01 • X0 • CX20 • CX21 ≈ CX20 • CX01 • X0
proved = p7
