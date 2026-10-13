{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0371 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119

p0 : CX21 • CX01 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
p0 = by-assoc-and (under (CX21) (ε) B119.proved) Eq.refl Eq.refl

p1 : CX21 • CX01 • CCX02 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
p1 = by-assoc-and (under (ε) (CCX02 • CX02) B30.proved) Eq.refl Eq.refl

p2 : CX21 • CX02 • CCX02 ≈ CX01 • CX21 • CCX02 • CX02
p2 = trans (sym p0) p1

p3 : CX21 • CX02 • CCX02 ≈ CX21 • CX02 • CCX02
p3 = refl

p4 : CX01 • CX21 • CCX02 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
p4 = refl

p5 : CX21 • CX02 • CCX02 ≈ CX01 • CX21 • CCX02 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
p6 = sym p5

proved : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
proved = p6
