{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0759 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 as B126
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129

p0 : CX01 • CX02 • CX21 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
p0 = by-assoc-and (under (CX01 • CX02) (ε) B129.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CX21 • CCX02 • X0 ≈ CX21 • CX02 • CCX02 • X0
p1 = by-assoc-and (under (ε) (CCX02 • X0) B126.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • X0 • CCX02 ≈ CX21 • CX02 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • X0 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
p3 = refl

p4 : CX21 • CX02 • CCX02 • X0 ≈ CX21 • CX02 • CCX02 • X0
p4 = refl

p5 : CX01 • CX02 • X0 • CCX02 ≈ CX21 • CX02 • CCX02 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : CX21 • CX02 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
p6 = sym p5

proved : CX21 • CX02 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
proved = p6
