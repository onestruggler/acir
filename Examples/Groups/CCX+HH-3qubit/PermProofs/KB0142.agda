{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0142 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115

p0 : X0 • CX10 • X1 • X1 ≈ X1 • CX10 • X1
p0 = by-assoc-and (under (ε) (X1) B115.proved) Eq.refl Eq.refl

p1 : X0 • CX10 • X1 • X1 ≈ X0 • CX10
p1 = by-assoc-and (under (X0 • CX10) (ε) B3.proved) Eq.refl Eq.refl

p2 : X1 • CX10 • X1 ≈ X0 • CX10
p2 = trans (sym p0) p1

p3 : X1 • CX10 • X1 ≈ X1 • CX10 • X1
p3 = refl

p4 : X0 • CX10 ≈ X0 • CX10
p4 = refl

p5 : X1 • CX10 • X1 ≈ X0 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CX10 • X1 ≈ X0 • CX10
proved = p5
