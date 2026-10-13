{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0780 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139

p0 : CX02 • CCX01 • X1 • CX01 • X0 ≈ CX02 • CCX01 • X0 • CX01
p0 = by-assoc-and (under (CX02 • CCX01) (ε) B139.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • CX01 • X0 ≈ X1 • CCX01 • CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B120.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • X0 • CX01 ≈ CX02 • CCX01 • X0 • CX01
p3 = refl

p4 : X1 • CCX01 • CX01 • X0 ≈ X1 • CCX01 • CX01 • X0
p4 = refl

p5 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
proved = p5
