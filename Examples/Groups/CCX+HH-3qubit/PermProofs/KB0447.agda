{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0447 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141

p0 : CX10 • CCX12 • CX12 • CX02 ≈ CX12 • CCX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B141.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
p1 = by-assoc-and (under (CX10 • CCX12) (ε) B27.proved) Eq.refl Eq.refl

p2 : CX12 • CCX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CCX12 • CX02 ≈ CX12 • CCX12 • CX02
p3 = refl

p4 : CX10 • CCX12 • CX02 • CX12 ≈ CX10 • CCX12 • CX02 • CX12
p4 = refl

p5 : CX12 • CCX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
p6 = sym p5

proved : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
proved = p6
