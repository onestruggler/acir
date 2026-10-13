{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0441 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139

p0 : X2 • X1 • CX01 • X0 ≈ X2 • X0 • CX01
p0 = by-assoc-and (under (X2) (ε) B139.proved) Eq.refl Eq.refl

p1 : X2 • X1 • CX01 • X0 ≈ X1 • X2 • CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B19.proved) Eq.refl Eq.refl

p2 : X2 • X0 • CX01 ≈ X1 • X2 • CX01 • X0
p2 = trans (sym p0) p1

p3 : X2 • X0 • CX01 ≈ X0 • X2 • CX01
p3 = by-assoc-and (under (ε) (CX01) B18.proved) Eq.refl Eq.refl

p4 : X2 • X0 • CX01 ≈ X0 • X2 • CX01
p4 = trans p3 (refl)

p5 : X1 • X2 • CX01 • X0 ≈ X1 • X2 • CX01 • X0
p5 = refl

p6 : X0 • X2 • CX01 ≈ X1 • X2 • CX01 • X0
p6 = trans (sym p4) (trans p2 p5)

p7 : X1 • X2 • CX01 • X0 ≈ X0 • X2 • CX01
p7 = sym p6

proved : X1 • X2 • CX01 • X0 ≈ X0 • X2 • CX01
proved = p7
