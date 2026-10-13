{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0116 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36

import Examples.Groups.CCX+HH-3qubit.Tietze.drel69 as Tdrel69
p0 : X1 • CX12 ≈ CX12 • X2 • X1
p0 = Tdrel69.proved

p1 : X1 • CX12 ≈ X1 • CX12
p1 = refl

p2 : CX12 • X2 • X1 ≈ X2 • CX12 • X1
p2 = by-assoc-and (under (ε) (X1) B36.proved) Eq.refl Eq.refl

p3 : CX12 • X2 • X1 ≈ X2 • CX12 • X1
p3 = trans p2 (refl)

p4 : X1 • CX12 ≈ X2 • CX12 • X1
p4 = trans (sym p1) (trans p0 p3)

p5 : X2 • CX12 • X1 ≈ X1 • CX12
p5 = sym p4

proved : X2 • CX12 • X1 ≈ X1 • CX12
proved = p5
