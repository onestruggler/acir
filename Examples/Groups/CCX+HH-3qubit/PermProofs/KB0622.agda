{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0622 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307

p0 : CX12 • CCX02 • CX12 • CCX01 • CX10 ≈ CCX01 • CCX02 • CX10
p0 = by-assoc-and (under (ε) (CX10) B307.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • CX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
p1 = by-assoc-and (under (CX12 • CCX02) (ε) B118.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • CX10 ≈ CCX01 • CCX02 • CX10
p3 = refl

p4 : CX12 • CCX02 • CX10 • CCX01 ≈ CX12 • CCX02 • CX10 • CCX01
p4 = refl

p5 : CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CCX02 • CX10 • CCX01 ≈ CCX01 • CCX02 • CX10
p6 = sym p5

proved : CX12 • CCX02 • CX10 • CCX01 ≈ CCX01 • CCX02 • CX10
proved = p6
