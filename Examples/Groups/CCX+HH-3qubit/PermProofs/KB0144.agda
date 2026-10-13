{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0144 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0116 as B116

p0 : X2 • CX12 • X1 • X1 ≈ X1 • CX12 • X1
p0 = by-assoc-and (under (ε) (X1) B116.proved) Eq.refl Eq.refl

p1 : X2 • CX12 • X1 • X1 ≈ X2 • CX12
p1 = by-assoc-and (under (X2 • CX12) (ε) B3.proved) Eq.refl Eq.refl

p2 : X1 • CX12 • X1 ≈ X2 • CX12
p2 = trans (sym p0) p1

p3 : X1 • CX12 • X1 ≈ X1 • CX12 • X1
p3 = refl

p4 : X2 • CX12 ≈ X2 • CX12
p4 = refl

p5 : X1 • CX12 • X1 ≈ X2 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CX12 • X1 ≈ X2 • CX12
proved = p5
