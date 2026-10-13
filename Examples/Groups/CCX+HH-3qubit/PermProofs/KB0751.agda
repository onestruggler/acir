{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0751 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120

p0 : CX01 • CCX02 • CX02 • CCX01 • X1 ≈ CX01 • CCX02 • X1 • CCX01
p0 = by-assoc-and (under (CX01 • CCX02) (ε) B120.proved) Eq.refl Eq.refl

p1 : CX01 • CCX02 • CX02 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1
p1 = by-assoc-and (under (ε) (CCX01 • X1) B119.proved) Eq.refl Eq.refl

p2 : CX01 • CCX02 • X1 • CCX01 ≈ CX02 • CCX02 • CCX01 • X1
p2 = trans (sym p0) p1

p3 : CX01 • CCX02 • X1 • CCX01 ≈ CX01 • X1 • CCX02 • CCX01
p3 = by-assoc-and (under (CX01) (CCX01) B28.proved) Eq.refl Eq.refl

p4 : CX01 • X1 • CCX02 • CCX01 ≈ X1 • CX01 • CCX02 • CCX01
p4 = by-assoc-and (under (ε) (CCX02 • CCX01) B35.proved) Eq.refl Eq.refl

p5 : CX01 • CCX02 • X1 • CCX01 ≈ X1 • CX01 • CCX02 • CCX01
p5 = trans p3 (trans p4 (refl))

p6 : CX02 • CCX02 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1
p6 = refl

p7 : X1 • CX01 • CCX02 • CCX01 ≈ CX02 • CCX02 • CCX01 • X1
p7 = trans (sym p5) (trans p2 p6)

p8 : CX02 • CCX02 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01
p8 = sym p7

proved : CX02 • CCX02 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01
proved = p8
