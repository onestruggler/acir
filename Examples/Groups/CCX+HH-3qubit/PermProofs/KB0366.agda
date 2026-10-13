{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140

p0 : CX12 • CCX01 • CX10 • X0 ≈ CX10 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0) B118.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • CX10 • X0 ≈ CX12 • CCX01 • X0 • CX10
p1 = by-assoc-and (under (CX12 • CCX01) (ε) B47.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • X0 ≈ CX10 • CCX01 • X0
p3 = refl

p4 : CX12 • CCX01 • X0 • CX10 ≈ X0 • CCX01 • CX10
p4 = by-assoc-and (under (ε) (CX10) B140.proved) Eq.refl Eq.refl

p5 : CX12 • CCX01 • X0 • CX10 ≈ X0 • CCX01 • CX10
p5 = trans p4 (refl)

p6 : CX10 • CCX01 • X0 ≈ X0 • CCX01 • CX10
p6 = trans (sym p3) (trans p2 p5)

proved : CX10 • CCX01 • X0 ≈ X0 • CCX01 • CX10
proved = p6
