{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2310 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0526 as B526

p0 : CCX02 • X1 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
p0 = by-assoc-and (under (CCX02) (ε) B526.proved) Eq.refl Eq.refl

p1 : CCX02 • X1 • CX02 • CCX12 • X1 ≈ X1 • CCX02 • CX02 • CCX12 • X1
p1 = by-assoc-and (under (ε) (CX02 • CCX12 • X1) B28.proved) Eq.refl Eq.refl

p2 : CCX02 • CX02 • CX20 • CCX12 ≈ X1 • CCX02 • CX02 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : CCX02 • CX02 • CX20 • CCX12 ≈ CCX02 • CX02 • CX20 • CCX12
p3 = refl

p4 : X1 • CCX02 • CX02 • CCX12 • X1 ≈ X1 • CCX02 • CX02 • CCX12 • X1
p4 = refl

p5 : CCX02 • CX02 • CX20 • CCX12 ≈ X1 • CCX02 • CX02 • CCX12 • X1
p5 = trans (sym p3) (trans p2 p4)

p6 : X1 • CCX02 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
p6 = sym p5

proved : X1 • CCX02 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
proved = p6
