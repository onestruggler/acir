{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0716 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0665 as B665

p0 : CX21 • CX21 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CX20 • CCX02
p0 = by-assoc-and (under (CX21) (ε) B665.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CCX02 • CCX01 • CX20 ≈ CCX02 • CCX01 • CX20
p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CX20) B7.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CX20 • CCX02 ≈ CX21 • CCX01 • CX20 • CCX02
p3 = refl

p4 : CCX02 • CCX01 • CX20 ≈ CCX02 • CCX01 • CX20
p4 = refl

p5 : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
proved = p5
