{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0323 as B323

p0 : CX20 • CCX12 • CCX01 • CX20 • CX20 ≈ CCX01 • CCX12 • CX20
p0 = by-assoc-and (under (ε) (CX20) B323.proved) Eq.refl Eq.refl

p1 : CX20 • CCX12 • CCX01 • CX20 • CX20 ≈ CX20 • CCX12 • CCX01
p1 = by-assoc-and (under (CX20 • CCX12 • CCX01) (ε) B9.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CX20 ≈ CX20 • CCX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CX20 ≈ CCX01 • CX20 • CCX12
p3 = by-assoc-and (under (CCX01) (ε) B40.proved) Eq.refl Eq.refl

p4 : CCX01 • CCX12 • CX20 ≈ CCX01 • CX20 • CCX12
p4 = trans p3 (refl)

p5 : CX20 • CCX12 • CCX01 ≈ CX20 • CCX12 • CCX01
p5 = refl

p6 : CCX01 • CX20 • CCX12 ≈ CX20 • CCX12 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CCX01 • CX20 • CCX12 ≈ CX20 • CCX12 • CCX01
proved = p6
