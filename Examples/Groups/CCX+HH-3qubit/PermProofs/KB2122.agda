{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2122 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0224 as B224
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0441 as B441

p0 : CCX01 • X1 • X2 • CX01 • X0 ≈ CCX01 • X0 • X2 • CX01
p0 = by-assoc-and (under (CCX01) (ε) B441.proved) Eq.refl Eq.refl

p1 : CCX01 • X1 • X2 • CX01 • X0 ≈ X2 • CCX01 • X1 • CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B224.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X1 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X0 • CX01
p3 = by-assoc-and (under (ε) (CX01) B223.proved) Eq.refl Eq.refl

p4 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X0 • CX01
p4 = trans p3 (refl)

p5 : X2 • CCX01 • X1 • CX01 • X0 ≈ X2 • X1 • CX01 • CCX01 • X0
p5 = by-assoc-and (under (X2) (X0) B282.proved) Eq.refl Eq.refl

p6 : X2 • X1 • CX01 • CCX01 • X0 ≈ X1 • X2 • CX01 • CCX01 • X0
p6 = by-assoc-and (under (ε) (CX01 • CCX01 • X0) B19.proved) Eq.refl Eq.refl

p7 : X2 • CCX01 • X1 • CX01 • X0 ≈ X1 • X2 • CX01 • CCX01 • X0
p7 = trans p5 (trans p6 (refl))

p8 : X2 • CCX01 • X0 • CX01 ≈ X1 • X2 • CX01 • CCX01 • X0
p8 = trans (sym p4) (trans p2 p7)

p9 : X1 • X2 • CX01 • CCX01 • X0 ≈ X2 • CCX01 • X0 • CX01
p9 = sym p8

proved : X1 • X2 • CX01 • CCX01 • X0 ≈ X2 • CCX01 • X0 • CX01
proved = p9
