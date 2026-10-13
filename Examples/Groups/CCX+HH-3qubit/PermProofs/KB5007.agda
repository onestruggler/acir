{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5007 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1266 as B1266

p0 : CCX01 • CCX12 • CCX01 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01 • CCX02
p0 = by-assoc-and (under (CCX01 • CCX12) (ε) B1266.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX01 • CX21 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
p1 = by-assoc-and (under (ε) (CX21 • CCX01) B211.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CCX01 • CCX12 • CX21 • CCX01 • CCX02
p3 = refl

p4 : CX02 • CCX12 • CX02 • CX21 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
p4 = refl

p5 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
proved = p5
