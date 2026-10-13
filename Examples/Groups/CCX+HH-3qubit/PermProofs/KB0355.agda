{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0355 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115

p0 : CX12 • X0 • CX10 • X1 ≈ CX12 • X1 • CX10
p0 = by-assoc-and (under (CX12) (ε) B115.proved) Eq.refl Eq.refl

p1 : CX12 • X0 • CX10 • X1 ≈ X0 • CX12 • CX10 • X1
p1 = by-assoc-and (under (ε) (CX10 • X1) B45.proved) Eq.refl Eq.refl

p2 : CX12 • X1 • CX10 ≈ X0 • CX12 • CX10 • X1
p2 = trans (sym p0) p1

p3 : CX12 • X1 • CX10 ≈ CX12 • X1 • CX10
p3 = refl

p4 : X0 • CX12 • CX10 • X1 ≈ X0 • CX10 • CX12 • X1
p4 = by-assoc-and (under (X0) (X1) B26.proved) Eq.refl Eq.refl

p5 : X0 • CX12 • CX10 • X1 ≈ X0 • CX10 • CX12 • X1
p5 = trans p4 (refl)

p6 : CX12 • X1 • CX10 ≈ X0 • CX10 • CX12 • X1
p6 = trans (sym p3) (trans p2 p5)

p7 : X0 • CX10 • CX12 • X1 ≈ CX12 • X1 • CX10
p7 = sym p6

proved : X0 • CX10 • CX12 • X1 ≈ CX12 • X1 • CX10
proved = p7
