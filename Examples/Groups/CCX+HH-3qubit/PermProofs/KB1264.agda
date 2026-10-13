{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1264 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0329 as B329

p0 : CCX02 • CCX01 • CX21 • CX20 ≈ CX21 • CCX01 • CCX02 • CX20
p0 = by-assoc-and (under (ε) (CX20) B329.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX01 • CX21 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
p1 = by-assoc-and (under (CCX02 • CCX01) (ε) B43.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 • CX20 ≈ CX21 • CCX01 • CCX02 • CX20
p3 = refl

p4 : CCX02 • CCX01 • CX20 • CX21 ≈ CCX02 • CCX01 • CX20 • CX21
p4 = refl

p5 : CX21 • CCX01 • CCX02 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CCX02 • CX20
p6 = sym p5

proved : CCX02 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CCX02 • CX20
proved = p6
