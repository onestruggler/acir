{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0390 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122

p0 : CCX01 • X2 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
p0 = by-assoc-and (under (CCX01) (ε) B122.proved) Eq.refl Eq.refl

p1 : CCX01 • X2 • CX01 • CCX02 ≈ X2 • CCX01 • CX01 • CCX02
p1 = by-assoc-and (under (ε) (CX01 • CCX02) B29.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • X2 ≈ X2 • CCX01 • CX01 • CCX02
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • X2 ≈ CCX01 • CCX02 • X2
p3 = refl

p4 : X2 • CCX01 • CX01 • CCX02 ≈ X2 • CCX01 • CX01 • CCX02
p4 = refl

p5 : CCX01 • CCX02 • X2 ≈ X2 • CCX01 • CX01 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
p6 = sym p5

proved : X2 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
proved = p6
