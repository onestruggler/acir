{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0493 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0158 as B158

p0 : CCX12 • X0 • CX01 • X0 ≈ CCX12 • X1 • CX01
p0 = by-assoc-and (under (CCX12) (ε) B158.proved) Eq.refl Eq.refl

p1 : CCX12 • X0 • CX01 • X0 ≈ X0 • CCX12 • CX01 • X0
p1 = by-assoc-and (under (ε) (CX01 • X0) B46.proved) Eq.refl Eq.refl

p2 : CCX12 • X1 • CX01 ≈ X0 • CCX12 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CCX12 • X1 • CX01 ≈ CCX12 • X1 • CX01
p3 = refl

p4 : X0 • CCX12 • CX01 • X0 ≈ X0 • CCX12 • CX01 • X0
p4 = refl

p5 : CCX12 • X1 • CX01 ≈ X0 • CCX12 • CX01 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01
p6 = sym p5

proved : X0 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01
proved = p6
