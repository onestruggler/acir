{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1250 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0321 as B321

p0 : CCX01 • CCX12 • CX02 • CX01 ≈ CX02 • CCX12 • CCX01 • CX01
p0 = by-assoc-and (under (ε) (CX01) B321.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CX02 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
p1 = by-assoc-and (under (CCX01 • CCX12) (ε) B25.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CCX01 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CCX01 • CX01 ≈ CX02 • CCX12 • CCX01 • CX01
p3 = refl

p4 : CCX01 • CCX12 • CX01 • CX02 ≈ CCX01 • CCX12 • CX01 • CX02
p4 = refl

p5 : CX02 • CCX12 • CCX01 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CCX12 • CX01 • CX02 ≈ CX02 • CCX12 • CCX01 • CX01
p6 = sym p5

proved : CCX01 • CCX12 • CX01 • CX02 ≈ CX02 • CCX12 • CCX01 • CX01
proved = p6
