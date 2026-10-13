{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0198 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0175 as B175

p0 : CX20 • CX12 • CX20 • CX20 ≈ CX10 • CX12 • CX20
p0 = by-assoc-and (under (ε) (CX20) B175.proved) Eq.refl Eq.refl

p1 : CX20 • CX12 • CX20 • CX20 ≈ CX20 • CX12
p1 = by-assoc-and (under (CX20 • CX12) (ε) B9.proved) Eq.refl Eq.refl

p2 : CX10 • CX12 • CX20 ≈ CX20 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CX12 • CX20 ≈ CX10 • CX12 • CX20
p3 = refl

p4 : CX20 • CX12 ≈ CX20 • CX12
p4 = refl

p5 : CX10 • CX12 • CX20 ≈ CX20 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CX12 • CX20 ≈ CX20 • CX12
proved = p5
