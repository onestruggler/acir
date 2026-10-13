{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32

p0 : CX12 • CCX12 ≈ CCX12 • CX10 • CX12
p0 = by-assoc-and (axiom r044) Eq.refl Eq.refl

p1 : CX12 • CCX12 ≈ CX12 • CCX12
p1 = refl

p2 : CCX12 • CX10 • CX12 ≈ CX10 • CCX12 • CX12
p2 = by-assoc-and (under (ε) (CX12) B32.proved) Eq.refl Eq.refl

p3 : CCX12 • CX10 • CX12 ≈ CX10 • CCX12 • CX12
p3 = trans p2 (refl)

p4 : CX12 • CCX12 ≈ CX10 • CCX12 • CX12
p4 = trans (sym p1) (trans p0 p3)

p5 : CX10 • CCX12 • CX12 ≈ CX12 • CCX12
p5 = sym p4

proved : CX10 • CCX12 • CX12 ≈ CX12 • CCX12
proved = p5
