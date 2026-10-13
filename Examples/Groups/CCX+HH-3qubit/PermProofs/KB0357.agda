{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0116 as B116

p0 : CX10 • X2 • CX12 • X1 ≈ CX10 • X1 • CX12
p0 = by-assoc-and (under (CX10) (ε) B116.proved) Eq.refl Eq.refl

p1 : CX10 • X2 • CX12 • X1 ≈ X2 • CX10 • CX12 • X1
p1 = by-assoc-and (under (ε) (CX12 • X1) B21.proved) Eq.refl Eq.refl

p2 : CX10 • X1 • CX12 ≈ X2 • CX10 • CX12 • X1
p2 = trans (sym p0) p1

p3 : CX10 • X1 • CX12 ≈ CX10 • X1 • CX12
p3 = refl

p4 : X2 • CX10 • CX12 • X1 ≈ X2 • CX10 • CX12 • X1
p4 = refl

p5 : CX10 • X1 • CX12 ≈ X2 • CX10 • CX12 • X1
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CX10 • CX12 • X1 ≈ CX10 • X1 • CX12
p6 = sym p5

proved : X2 • CX10 • CX12 • X1 ≈ CX10 • X1 • CX12
proved = p6
