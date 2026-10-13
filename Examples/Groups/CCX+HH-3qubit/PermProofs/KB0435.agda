{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137

p0 : CX02 • CCX01 • CX01 • X1 ≈ CX01 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1) B137.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • CX01 • X1 ≈ CX02 • CCX01 • X1 • CX01
p1 = by-assoc-and (under (CX02 • CCX01) (ε) B35.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • X1 ≈ CX02 • CCX01 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • X1 ≈ CX01 • CCX01 • X1
p3 = refl

p4 : CX02 • CCX01 • X1 • CX01 ≈ X1 • CCX01 • CX01
p4 = by-assoc-and (under (ε) (CX01) B120.proved) Eq.refl Eq.refl

p5 : CX02 • CCX01 • X1 • CX01 ≈ X1 • CCX01 • CX01
p5 = trans p4 (refl)

p6 : CX01 • CCX01 • X1 ≈ X1 • CCX01 • CX01
p6 = trans (sym p3) (trans p2 p5)

proved : CX01 • CCX01 • X1 ≈ X1 • CCX01 • CX01
proved = p6
