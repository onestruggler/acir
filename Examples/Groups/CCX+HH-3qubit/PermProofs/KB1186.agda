{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1186 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0294 as B294

p0 : CCX01 • CX20 • CX12 • X2 ≈ CX10 • CCX01 • CX20 • X2
p0 = by-assoc-and (under (ε) (X2) B294.proved) Eq.refl Eq.refl

p1 : CCX01 • CX20 • CX12 • X2 ≈ CCX01 • CX20 • X2 • CX12
p1 = by-assoc-and (under (CCX01 • CX20) (ε) B36.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CX20 • X2 ≈ CCX01 • CX20 • X2 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CX20 • X2 ≈ CX10 • CCX01 • CX20 • X2
p3 = refl

p4 : CCX01 • CX20 • X2 • CX12 ≈ CCX01 • CX20 • X2 • CX12
p4 = refl

p5 : CX10 • CCX01 • CX20 • X2 ≈ CCX01 • CX20 • X2 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX20 • X2 • CX12 ≈ CX10 • CCX01 • CX20 • X2
p6 = sym p5

proved : CCX01 • CX20 • X2 • CX12 ≈ CX10 • CCX01 • CX20 • X2
proved = p6
