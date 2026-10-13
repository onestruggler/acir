{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0174 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0135 as B135

p0 : CX20 • CX10 • CX12 • CX12 ≈ CX12 • CX20 • CX12
p0 = by-assoc-and (under (ε) (CX12) B135.proved) Eq.refl Eq.refl

p1 : CX20 • CX10 • CX12 • CX12 ≈ CX20 • CX10
p1 = by-assoc-and (under (CX20 • CX10) (ε) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CX20 • CX12 ≈ CX20 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CX20 • CX12 ≈ CX12 • CX20 • CX12
p3 = refl

p4 : CX20 • CX10 ≈ CX20 • CX10
p4 = refl

p5 : CX12 • CX20 • CX12 ≈ CX20 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX20 • CX12 ≈ CX20 • CX10
proved = p5
