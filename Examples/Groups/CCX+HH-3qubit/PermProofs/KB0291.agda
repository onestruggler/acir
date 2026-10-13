{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0291 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 as B126
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0189 as B189

p0 : CCX01 • CX01 • CX02 • CX21 ≈ CX01 • CCX01 • CX21
p0 = by-assoc-and (under (ε) (CX21) B189.proved) Eq.refl Eq.refl

p1 : CCX01 • CX01 • CX02 • CX21 ≈ CCX01 • CX21 • CX02
p1 = by-assoc-and (under (CCX01) (ε) B126.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • CX21 ≈ CCX01 • CX21 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • CX21 ≈ CX01 • CCX01 • CX21
p3 = refl

p4 : CCX01 • CX21 • CX02 ≈ CCX01 • CX21 • CX02
p4 = refl

p5 : CX01 • CCX01 • CX21 ≈ CCX01 • CX21 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX21 • CX02 ≈ CX01 • CCX01 • CX21
p6 = sym p5

proved : CCX01 • CX21 • CX02 ≈ CX01 • CCX01 • CX21
proved = p6
