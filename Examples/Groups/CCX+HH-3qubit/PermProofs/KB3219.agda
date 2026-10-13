{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3219 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0210 as B210
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 as B325
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0336 as B336
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1364 as B1364

p0 : CCX01 • CX20 • CCX12 • CCX02 • CX10 ≈ CCX01 • CX20 • CX10 • CCX02 • CCX12
p0 = by-assoc-and (under (CCX01 • CX20) (ε) B336.proved) Eq.refl Eq.refl

p1 : CCX01 • CX20 • CCX12 • CCX02 • CX10 ≈ CX20 • CCX12 • CCX01 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CCX02 • CX10) B325.proved) Eq.refl Eq.refl

p2 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CX20 • CCX12 • CCX01 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CCX01 • CX10 • CX20 • CCX02 • CCX12
p3 = by-assoc-and (under (CCX01) (CCX02 • CCX12) B210.proved) Eq.refl Eq.refl

p4 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CCX01 • CX10 • CX20 • CCX02 • CCX12
p4 = trans p3 (refl)

p5 : CX20 • CCX12 • CCX01 • CCX02 • CX10 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
p5 = by-assoc-and (under (CX20) (ε) B1364.proved) Eq.refl Eq.refl

p6 : CX20 • CCX12 • CCX01 • CCX02 • CX10 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
p6 = trans p5 (refl)

p7 : CCX01 • CX10 • CX20 • CCX02 • CCX12 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
p7 = trans (sym p4) (trans p2 p6)

proved : CCX01 • CX10 • CX20 • CCX02 • CCX12 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
proved = p7
