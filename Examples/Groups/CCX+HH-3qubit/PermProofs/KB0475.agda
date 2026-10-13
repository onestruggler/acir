{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0475 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0151 as B151

p0 : X2 • X1 • CX02 • CCX01 ≈ X2 • CCX01 • X1
p0 = by-assoc-and (under (X2) (ε) B151.proved) Eq.refl Eq.refl

p1 : X2 • X1 • CX02 • CCX01 ≈ X1 • X2 • CX02 • CCX01
p1 = by-assoc-and (under (ε) (CX02 • CCX01) B19.proved) Eq.refl Eq.refl

p2 : X2 • CCX01 • X1 ≈ X1 • X2 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : X2 • CCX01 • X1 ≈ X2 • CCX01 • X1
p3 = refl

p4 : X1 • X2 • CX02 • CCX01 ≈ X1 • X2 • CX02 • CCX01
p4 = refl

p5 : X2 • CCX01 • X1 ≈ X1 • X2 • CX02 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : X1 • X2 • CX02 • CCX01 ≈ X2 • CCX01 • X1
p6 = sym p5

proved : X1 • X2 • CX02 • CCX01 ≈ X2 • CCX01 • X1
proved = p6
