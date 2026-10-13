{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0344 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0174 as B174
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0210 as B210
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0343 as B343

p0 : CX12 • CX12 • CX21 • CX10 • CX21 ≈ CX12 • CX20 • CX12
p0 = by-assoc-and (under (CX12) (ε) B343.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX21
p1 = by-assoc-and (under (ε) (CX21 • CX10 • CX21) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CX20 • CX12 ≈ CX21 • CX10 • CX21
p2 = trans (sym p0) p1

p3 : CX12 • CX20 • CX12 ≈ CX20 • CX10
p3 = by-assoc-and (under (ε) (ε) B174.proved) Eq.refl Eq.refl

p4 : CX20 • CX10 ≈ CX10 • CX20
p4 = by-assoc-and (under (ε) (ε) B210.proved) Eq.refl Eq.refl

p5 : CX12 • CX20 • CX12 ≈ CX10 • CX20
p5 = trans p3 (trans p4 (refl))

p6 : CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX21
p6 = refl

p7 : CX10 • CX20 ≈ CX21 • CX10 • CX21
p7 = trans (sym p5) (trans p2 p6)

p8 : CX21 • CX10 • CX21 ≈ CX10 • CX20
p8 = sym p7

proved : CX21 • CX10 • CX21 ≈ CX10 • CX20
proved = p8
