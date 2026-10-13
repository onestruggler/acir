{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0151 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120

p0 : CX02 • CX02 • CCX01 • X1 ≈ CX02 • X1 • CCX01
p0 = by-assoc-and (under (CX02) (ε) B120.proved) Eq.refl Eq.refl

p1 : CX02 • CX02 • CCX01 • X1 ≈ CCX01 • X1
p1 = by-assoc-and (under (ε) (CCX01 • X1) B8.proved) Eq.refl Eq.refl

p2 : CX02 • X1 • CCX01 ≈ CCX01 • X1
p2 = trans (sym p0) p1

p3 : CX02 • X1 • CCX01 ≈ X1 • CX02 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B23.proved) Eq.refl Eq.refl

p4 : CX02 • X1 • CCX01 ≈ X1 • CX02 • CCX01
p4 = trans p3 (refl)

p5 : CCX01 • X1 ≈ CCX01 • X1
p5 = refl

p6 : X1 • CX02 • CCX01 ≈ CCX01 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : X1 • CX02 • CCX01 ≈ CCX01 • X1
proved = p6
