{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0503 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163

p0 : CX12 • CX01 • CX12 • X0 ≈ CX01 • CX02 • X0
p0 = by-assoc-and (under (ε) (X0) B163.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • CX12 • X0 ≈ CX12 • CX01 • X0 • CX12
p1 = by-assoc-and (under (CX12 • CX01) (ε) B45.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • X0 ≈ CX12 • CX01 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • X0 ≈ CX01 • CX02 • X0
p3 = refl

p4 : CX12 • CX01 • X0 • CX12 ≈ CX12 • CX01 • X0 • CX12
p4 = refl

p5 : CX01 • CX02 • X0 ≈ CX12 • CX01 • X0 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CX01 • X0 • CX12 ≈ CX01 • CX02 • X0
p6 = sym p5

proved : CX12 • CX01 • X0 • CX12 ≈ CX01 • CX02 • X0
proved = p6
