{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0340 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0216 as B216

p0 : CCX02 • CCX02 • CCX12 • CCX02 ≈ CCX02 • CX01 • CCX12 • CX01
p0 = by-assoc-and (under (CCX02) (ε) B216.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02
p1 = by-assoc-and (under (ε) (CCX12 • CCX02) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • CX01 • CCX12 • CX01 ≈ CCX12 • CCX02
p2 = trans (sym p0) p1

p3 : CCX02 • CX01 • CCX12 • CX01 ≈ CX01 • CCX02 • CCX12 • CX01
p3 = by-assoc-and (under (ε) (CCX12 • CX01) B38.proved) Eq.refl Eq.refl

p4 : CCX02 • CX01 • CCX12 • CX01 ≈ CX01 • CCX02 • CCX12 • CX01
p4 = trans p3 (refl)

p5 : CCX12 • CCX02 ≈ CCX12 • CCX02
p5 = refl

p6 : CX01 • CCX02 • CCX12 • CX01 ≈ CCX12 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CX01 • CCX02 • CCX12 • CX01 ≈ CCX12 • CCX02
proved = p6
