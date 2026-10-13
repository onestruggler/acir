{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0819 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : X1 • CX01 • X0 • CCX01 • X0 ≈ X1 • CX01 • CX12 • CCX01
p0 = by-assoc-and (under (X1 • CX01) (ε) B153.proved) Eq.refl Eq.refl

p1 : X1 • CX01 • X0 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B139.proved) Eq.refl Eq.refl

p2 : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : X1 • CX01 • CX12 • CCX01 ≈ X1 • CX01 • CX12 • CCX01
p3 = refl

p4 : X0 • CX01 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • X0
p4 = refl

p5 : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
proved = p5
