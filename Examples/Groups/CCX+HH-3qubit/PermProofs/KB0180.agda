{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0180 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141

p0 : CX10 • CX10 • CCX12 • CX12 ≈ CX10 • CX12 • CCX12
p0 = by-assoc-and (under (CX10) (ε) B141.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • CCX12 • CX12 ≈ CCX12 • CX12
p1 = by-assoc-and (under (ε) (CCX12 • CX12) B5.proved) Eq.refl Eq.refl

p2 : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CX12 • CCX12 ≈ CX10 • CX12 • CCX12
p3 = refl

p4 : CCX12 • CX12 ≈ CCX12 • CX12
p4 = refl

p5 : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
proved = p5
