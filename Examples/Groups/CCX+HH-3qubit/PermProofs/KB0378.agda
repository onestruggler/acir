{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0378 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120

p0 : CX02 • CCX01 • X1 • X0 ≈ X1 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0) B120.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • X0 ≈ CX02 • CCX01 • X0 • X1
p1 = by-assoc-and (under (CX02 • CCX01) (ε) B44.proved) Eq.refl Eq.refl

p2 : X1 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • X1
p2 = trans (sym p0) p1

p3 : X1 • CCX01 • X0 ≈ X1 • CCX01 • X0
p3 = refl

p4 : CX02 • CCX01 • X0 • X1 ≈ CX02 • CCX01 • X0 • X1
p4 = refl

p5 : X1 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • X1
p5 = trans (sym p3) (trans p2 p4)

p6 : CX02 • CCX01 • X0 • X1 ≈ X1 • CCX01 • X0
p6 = sym p5

proved : CX02 • CCX01 • X0 • X1 ≈ X1 • CCX01 • X0
proved = p6
