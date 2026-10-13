{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0831 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0157 as B157
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0159 as B159
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0780 as B780

p0 : CX01 • CCX01 • CX01 • X0 • CX01 ≈ CX01 • CCX01 • X0 • X1
p0 = by-assoc-and (under (CX01 • CCX01) (ε) B159.proved) Eq.refl Eq.refl

p1 : CX01 • CCX01 • CX01 • X0 • CX01 ≈ CX02 • CCX01 • X0 • CX01
p1 = by-assoc-and (under (ε) (X0 • CX01) B157.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • X0 • X1 ≈ CX02 • CCX01 • X0 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • X0 • X1 ≈ CX01 • CCX01 • X0 • X1
p3 = refl

p4 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
p4 = by-assoc-and (under (ε) (ε) B780.proved) Eq.refl Eq.refl

p5 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
p5 = trans p4 (refl)

p6 : CX01 • CCX01 • X0 • X1 ≈ X1 • CCX01 • CX01 • X0
p6 = trans (sym p3) (trans p2 p5)

proved : CX01 • CCX01 • X0 • X1 ≈ X1 • CCX01 • CX01 • X0
proved = p6
