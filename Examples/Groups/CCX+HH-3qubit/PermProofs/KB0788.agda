{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0788 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0142 as B142
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280

p0 : CX02 • CCX01 • X1 • CX10 • X1 ≈ CX02 • CCX01 • X0 • CX10
p0 = by-assoc-and (under (CX02 • CCX01) (ε) B142.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • CX10 • X1 ≈ X1 • CCX01 • CX10 • X1
p1 = by-assoc-and (under (ε) (CX10 • X1) B120.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • X0 • CX10 ≈ X1 • CCX01 • CX10 • X1
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • X0 • CX10 ≈ CX02 • X0 • CX10 • CCX01
p3 = by-assoc-and (under (CX02) (ε) B280.proved) Eq.refl Eq.refl

p4 : CX02 • CCX01 • X0 • CX10 ≈ CX02 • X0 • CX10 • CCX01
p4 = trans p3 (refl)

p5 : X1 • CCX01 • CX10 • X1 ≈ X1 • CCX01 • CX10 • X1
p5 = refl

p6 : CX02 • X0 • CX10 • CCX01 ≈ X1 • CCX01 • CX10 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : CX02 • X0 • CX10 • CCX01 ≈ X1 • CCX01 • CX10 • X1
proved = p6
