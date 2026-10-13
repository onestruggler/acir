{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0343 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0237 as B237

p0 : CX20 • CX12 • CX21 • CX21 ≈ CX12 • CX21 • CX10 • CX21
p0 = by-assoc-and (under (ε) (CX21) B237.proved) Eq.refl Eq.refl

p1 : CX20 • CX12 • CX21 • CX21 ≈ CX20 • CX12
p1 = by-assoc-and (under (CX20 • CX12) (ε) B7.proved) Eq.refl Eq.refl

p2 : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CX21 • CX10 • CX21 ≈ CX12 • CX21 • CX10 • CX21
p3 = refl

p4 : CX20 • CX12 ≈ CX20 • CX12
p4 = refl

p5 : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
proved = p5
