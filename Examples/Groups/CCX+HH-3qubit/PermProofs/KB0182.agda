{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0182 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0143 as B143

p0 : X0 • X1 • CX10 • CX10 ≈ CX10 • X1 • CX10
p0 = by-assoc-and (under (ε) (CX10) B143.proved) Eq.refl Eq.refl

p1 : X0 • X1 • CX10 • CX10 ≈ X0 • X1
p1 = by-assoc-and (under (X0 • X1) (ε) B5.proved) Eq.refl Eq.refl

p2 : CX10 • X1 • CX10 ≈ X0 • X1
p2 = trans (sym p0) p1

p3 : CX10 • X1 • CX10 ≈ CX10 • X1 • CX10
p3 = refl

p4 : X0 • X1 ≈ X0 • X1
p4 = refl

p5 : CX10 • X1 • CX10 ≈ X0 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • X1 • CX10 ≈ X0 • X1
proved = p5
