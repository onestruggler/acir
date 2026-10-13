{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0189 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0156 as B156

p0 : CCX01 • CCX01 • CX01 • CCX01 ≈ CCX01 • CX01 • CX02
p0 = by-assoc-and (under (CCX01) (ε) B156.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX01 • CX01 • CCX01 ≈ CX01 • CCX01
p1 = by-assoc-and (under (ε) (CX01 • CCX01) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • CX02 ≈ CCX01 • CX01 • CX02
p3 = refl

p4 : CX01 • CCX01 ≈ CX01 • CCX01
p4 = refl

p5 : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
proved = p5
