{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0233 as B233

p0 : CX01 • CX01 • X0 • CX01 • X0 ≈ CX01 • X1
p0 = by-assoc-and (under (CX01) (ε) B233.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • X0 • CX01 • X0 ≈ X0 • CX01 • X0
p1 = by-assoc-and (under (ε) (X0 • CX01 • X0) B1.proved) Eq.refl Eq.refl

p2 : CX01 • X1 ≈ X0 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CX01 • X1 ≈ CX01 • X1
p3 = refl

p4 : X0 • CX01 • X0 ≈ X0 • CX01 • X0
p4 = refl

p5 : CX01 • X1 ≈ X0 • CX01 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CX01 • X0 ≈ CX01 • X1
p6 = sym p5

proved : X0 • CX01 • X0 ≈ CX01 • X1
proved = p6
