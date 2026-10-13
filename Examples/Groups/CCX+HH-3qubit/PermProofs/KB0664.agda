{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0664 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0330 as B330

p0 : CCX01 • CX21 • CCX02 • X0 ≈ CX21 • CCX02 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0) B330.proved) Eq.refl Eq.refl

p1 : CCX01 • CX21 • CCX02 • X0 ≈ CCX01 • X0 • CCX02
p1 = by-assoc-and (under (CCX01) (ε) B129.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CCX01 • X0 ≈ CX21 • CCX02 • CCX01 • X0
p3 = refl

p4 : CCX01 • X0 • CCX02 ≈ CCX01 • X0 • CCX02
p4 = refl

p5 : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
proved = p5
