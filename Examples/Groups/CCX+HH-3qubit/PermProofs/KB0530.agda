{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0530 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0170 as B170

p0 : CX02 • X1 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
p0 = by-assoc-and (under (CX02) (ε) B170.proved) Eq.refl Eq.refl

p1 : CX02 • X1 • CX20 • CCX12 ≈ X1 • CX02 • CX20 • CCX12
p1 = by-assoc-and (under (ε) (CX20 • CCX12) B23.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • X1 ≈ X1 • CX02 • CX20 • CCX12
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • X1 ≈ CX02 • CCX12 • X1
p3 = refl

p4 : X1 • CX02 • CX20 • CCX12 ≈ X1 • CX02 • CX20 • CCX12
p4 = refl

p5 : CX02 • CCX12 • X1 ≈ X1 • CX02 • CX20 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : X1 • CX02 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
p6 = sym p5

proved : X1 • CX02 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
proved = p6
