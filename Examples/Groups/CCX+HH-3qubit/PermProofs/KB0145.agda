{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0117 as B117

p0 : X1 • X2 • CX12 • CX12 ≈ CX12 • X1 • CX12
p0 = by-assoc-and (under (ε) (CX12) B117.proved) Eq.refl Eq.refl

p1 : X1 • X2 • CX12 • CX12 ≈ X1 • X2
p1 = by-assoc-and (under (X1 • X2) (ε) B6.proved) Eq.refl Eq.refl

p2 : CX12 • X1 • CX12 ≈ X1 • X2
p2 = trans (sym p0) p1

p3 : CX12 • X1 • CX12 ≈ CX12 • X1 • CX12
p3 = refl

p4 : X1 • X2 ≈ X1 • X2
p4 = refl

p5 : CX12 • X1 • CX12 ≈ X1 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • X1 • CX12 ≈ X1 • X2
proved = p5
