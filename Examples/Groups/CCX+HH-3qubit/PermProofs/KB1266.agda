{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1266 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1265 as B1265

p0 : CCX01 • CX21 • CCX01 • CCX02 • CCX02 ≈ CX21 • CCX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B1265.proved) Eq.refl Eq.refl

p1 : CCX01 • CX21 • CCX01 • CCX02 • CCX02 ≈ CCX01 • CX21 • CCX01
p1 = by-assoc-and (under (CCX01 • CX21 • CCX01) (ε) B10.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 ≈ CX21 • CCX01 • CCX02
p3 = refl

p4 : CCX01 • CX21 • CCX01 ≈ CCX01 • CX21 • CCX01
p4 = refl

p5 : CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02
p6 = sym p5

proved : CCX01 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02
proved = p6
