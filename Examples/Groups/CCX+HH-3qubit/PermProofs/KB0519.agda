{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0519 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0167 as B167

p0 : CX01 • X2 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
p0 = by-assoc-and (under (CX01) (ε) B167.proved) Eq.refl Eq.refl

p1 : CX01 • X2 • CCX12 • X2 ≈ X2 • CX01 • CCX12 • X2
p1 = by-assoc-and (under (ε) (CCX12 • X2) B22.proved) Eq.refl Eq.refl

p2 : CX01 • CX10 • CCX12 ≈ X2 • CX01 • CCX12 • X2
p2 = trans (sym p0) p1

p3 : CX01 • CX10 • CCX12 ≈ CX01 • CX10 • CCX12
p3 = refl

p4 : X2 • CX01 • CCX12 • X2 ≈ X2 • CX01 • CCX12 • X2
p4 = refl

p5 : CX01 • CX10 • CCX12 ≈ X2 • CX01 • CCX12 • X2
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CX01 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
p6 = sym p5

proved : X2 • CX01 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
proved = p6
