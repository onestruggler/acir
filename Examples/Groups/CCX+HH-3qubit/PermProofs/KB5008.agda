{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5008 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0291 as B291
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1266 as B1266

p0 : CCX01 • CX21 • CCX01 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX02 • CCX12 • CCX01
p0 = by-assoc-and (under (ε) (CCX12 • CCX01) B1266.proved) Eq.refl Eq.refl

p1 : CCX01 • CX21 • CCX01 • CCX12 • CCX01 ≈ CCX01 • CX21 • CX02 • CCX12 • CX02
p1 = by-assoc-and (under (CCX01 • CX21) (ε) B211.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CCX01 • CX21 • CX02 • CCX12 • CX02
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX02 • CCX12 • CCX01
p3 = refl

p4 : CCX01 • CX21 • CX02 • CCX12 • CX02 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
p4 = by-assoc-and (under (ε) (CCX12 • CX02) B291.proved) Eq.refl Eq.refl

p5 : CCX01 • CX21 • CX02 • CCX12 • CX02 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
p5 = trans p4 (refl)

p6 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
p6 = trans (sym p3) (trans p2 p5)

proved : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
proved = p6
