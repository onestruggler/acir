{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0825 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 as B124
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0151 as B151
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0157 as B157

p0 : X0 • X1 • CX01 • CCX01 • CX01 ≈ X0 • X1 • CX02 • CCX01
p0 = by-assoc-and (under (X0 • X1) (ε) B157.proved) Eq.refl Eq.refl

p1 : X0 • X1 • CX01 • CCX01 • CX01 ≈ CX01 • X0 • CCX01 • CX01
p1 = by-assoc-and (under (ε) (CCX01 • CX01) B124.proved) Eq.refl Eq.refl

p2 : X0 • X1 • CX02 • CCX01 ≈ CX01 • X0 • CCX01 • CX01
p2 = trans (sym p0) p1

p3 : X0 • X1 • CX02 • CCX01 ≈ X0 • CCX01 • X1
p3 = by-assoc-and (under (X0) (ε) B151.proved) Eq.refl Eq.refl

p4 : X0 • X1 • CX02 • CCX01 ≈ X0 • CCX01 • X1
p4 = trans p3 (refl)

p5 : CX01 • X0 • CCX01 • CX01 ≈ CX01 • X0 • CCX01 • CX01
p5 = refl

p6 : X0 • CCX01 • X1 ≈ CX01 • X0 • CCX01 • CX01
p6 = trans (sym p4) (trans p2 p5)

p7 : CX01 • X0 • CCX01 • CX01 ≈ X0 • CCX01 • X1
p7 = sym p6

proved : CX01 • X0 • CCX01 • CX01 ≈ X0 • CCX01 • X1
proved = p7
