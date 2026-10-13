{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : X2 • X0 • CCX01 • X0 ≈ X2 • CX12 • CCX01
p0 = by-assoc-and (under (X2) (ε) B153.proved) Eq.refl Eq.refl

p1 : X2 • X0 • CCX01 • X0 ≈ X0 • X2 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B18.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 ≈ X0 • X2 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : X2 • CX12 • CCX01 ≈ X2 • CX12 • CCX01
p3 = refl

p4 : X0 • X2 • CCX01 • X0 ≈ X0 • X2 • CCX01 • X0
p4 = refl

p5 : X2 • CX12 • CCX01 ≈ X0 • X2 • CCX01 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • X2 • CCX01 • X0 ≈ X2 • CX12 • CCX01
p6 = sym p5

proved : X0 • X2 • CCX01 • X0 ≈ X2 • CX12 • CCX01
proved = p6
