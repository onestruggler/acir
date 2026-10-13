{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0809 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 as B124
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0149 as B149

p0 : X0 • X1 • CX01 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
p0 = by-assoc-and (under (X0 • X1) (ε) B149.proved) Eq.refl Eq.refl

p1 : X0 • X1 • CX01 • CX02 • CCX02 ≈ CX01 • X0 • CX02 • CCX02
p1 = by-assoc-and (under (ε) (CX02 • CCX02) B124.proved) Eq.refl Eq.refl

p2 : X0 • X1 • CCX02 • CX02 ≈ CX01 • X0 • CX02 • CCX02
p2 = trans (sym p0) p1

p3 : X0 • X1 • CCX02 • CX02 ≈ X0 • X1 • CCX02 • CX02
p3 = refl

p4 : CX01 • X0 • CX02 • CCX02 ≈ CX01 • X0 • CX02 • CCX02
p4 = refl

p5 : X0 • X1 • CCX02 • CX02 ≈ CX01 • X0 • CX02 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • X0 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
p6 = sym p5

proved : CX01 • X0 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
proved = p6
