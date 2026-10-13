{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0294 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0198 as B198
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0202 as B202

p0 : CCX01 • CX10 • CX12 • CX20 ≈ CX10 • CCX01 • CX20
p0 = by-assoc-and (under (ε) (CX20) B202.proved) Eq.refl Eq.refl

p1 : CCX01 • CX10 • CX12 • CX20 ≈ CCX01 • CX20 • CX12
p1 = by-assoc-and (under (CCX01) (ε) B198.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CX20 ≈ CCX01 • CX20 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CX20 ≈ CX10 • CCX01 • CX20
p3 = refl

p4 : CCX01 • CX20 • CX12 ≈ CCX01 • CX20 • CX12
p4 = refl

p5 : CX10 • CCX01 • CX20 ≈ CCX01 • CX20 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX20 • CX12 ≈ CX10 • CCX01 • CX20
p6 = sym p5

proved : CCX01 • CX20 • CX12 ≈ CX10 • CCX01 • CX20
proved = p6
