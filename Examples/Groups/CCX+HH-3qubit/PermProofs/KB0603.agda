{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0603 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280

p0 : CCX01 • X0 • CX10 • X1 ≈ X0 • CX10 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1) B280.proved) Eq.refl Eq.refl

p1 : CCX01 • X0 • CX10 • X1 ≈ CCX01 • X1 • CX10
p1 = by-assoc-and (under (CCX01) (ε) B115.proved) Eq.refl Eq.refl

p2 : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
p2 = trans (sym p0) p1

p3 : X0 • CX10 • CCX01 • X1 ≈ X0 • CX10 • CCX01 • X1
p3 = refl

p4 : CCX01 • X1 • CX10 ≈ CCX01 • X1 • CX10
p4 = refl

p5 : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
proved = p5
