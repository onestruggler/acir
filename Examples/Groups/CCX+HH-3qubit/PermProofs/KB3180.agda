{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3180 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 as B325
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2831 as B2831

p0 : CCX01 • CCX02 • CCX01 • CX20 • CCX12 ≈ CCX01 • CCX02 • CX20 • CCX12 • CCX01
p0 = by-assoc-and (under (CCX01 • CCX02) (ε) B325.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • CX20 • CCX12 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
p1 = by-assoc-and (under (ε) (CX20 • CCX12) B214.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12 • CCX01
p3 = refl

p4 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
p4 = by-assoc-and (under (ε) (ε) B2831.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
p5 = trans p4 (refl)

p6 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21
p6 = trans (sym p3) (trans p2 p5)

proved : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21
proved = p6
