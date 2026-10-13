{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0225 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30

p0 : CX21 • CX01 • X2 ≈ CX01 • CX21 • X2
p0 = by-assoc-and (under (ε) (X2) B30.proved) Eq.refl Eq.refl

p1 : CX21 • CX01 • X2 ≈ CX21 • X2 • CX01
p1 = by-assoc-and (under (CX21) (ε) B22.proved) Eq.refl Eq.refl

p2 : CX01 • CX21 • X2 ≈ CX21 • X2 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CX21 • X2 ≈ CX01 • CX21 • X2
p3 = refl

p4 : CX21 • X2 • CX01 ≈ CX21 • X2 • CX01
p4 = refl

p5 : CX01 • CX21 • X2 ≈ CX21 • X2 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX21 • X2 • CX01 ≈ CX01 • CX21 • X2
p6 = sym p5

proved : CX21 • X2 • CX01 ≈ CX01 • CX21 • X2
proved = p6
