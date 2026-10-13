{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0288 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 as B138
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0170 as B170

p0 : X1 • CX20 • CCX12 • CX21 ≈ CCX12 • X1 • CX21
p0 = by-assoc-and (under (ε) (CX21) B170.proved) Eq.refl Eq.refl

p1 : X1 • CX20 • CCX12 • CX21 ≈ X1 • CX21 • CCX12
p1 = by-assoc-and (under (X1) (ε) B138.proved) Eq.refl Eq.refl

p2 : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • X1 • CX21 ≈ CCX12 • X1 • CX21
p3 = refl

p4 : X1 • CX21 • CCX12 ≈ X1 • CX21 • CCX12
p4 = refl

p5 : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
proved = p5
