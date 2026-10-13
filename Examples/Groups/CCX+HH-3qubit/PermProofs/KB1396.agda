{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1396 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0338 as B338
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1335 as B1335

p0 : CCX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX01 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B1335.proved) Eq.refl Eq.refl

p1 : CCX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
p1 = by-assoc-and (under (CCX01) (ε) B338.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX01 • CCX12
p3 = refl

p4 : CCX01 • CCX12 • CCX02 ≈ CCX01 • CCX12 • CCX02
p4 = refl

p5 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
proved = p5
