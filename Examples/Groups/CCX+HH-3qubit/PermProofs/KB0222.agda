{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0222 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27

p0 : CX12 • CX02 • X1 ≈ CX02 • CX12 • X1
p0 = by-assoc-and (under (ε) (X1) B27.proved) Eq.refl Eq.refl

p1 : CX12 • CX02 • X1 ≈ CX12 • X1 • CX02
p1 = by-assoc-and (under (CX12) (ε) B23.proved) Eq.refl Eq.refl

p2 : CX02 • CX12 • X1 ≈ CX12 • X1 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CX12 • X1 ≈ CX02 • CX12 • X1
p3 = refl

p4 : CX12 • X1 • CX02 ≈ CX12 • X1 • CX02
p4 = refl

p5 : CX02 • CX12 • X1 ≈ CX12 • X1 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • X1 • CX02 ≈ CX02 • CX12 • X1
p6 = sym p5

proved : CX12 • X1 • CX02 ≈ CX02 • CX12 • X1
proved = p6
