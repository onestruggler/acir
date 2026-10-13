{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0149 as B149
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0340 as B340

p0 : CX02 • CX01 • CCX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
p0 = by-assoc-and (under (CX02) (ε) B340.proved) Eq.refl Eq.refl

p1 : CX02 • CX01 • CCX02 • CCX12 • CX01 ≈ CX01 • CX02 • CCX02 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CX01) B25.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CCX02 ≈ CX01 • CX02 • CCX02 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CCX02
p3 = refl

p4 : CX01 • CX02 • CCX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CX01
p4 = by-assoc-and (under (ε) (CCX12 • CX01) B149.proved) Eq.refl Eq.refl

p5 : CX01 • CX02 • CCX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CX01
p5 = trans p4 (refl)

p6 : CX02 • CCX12 • CCX02 ≈ CCX02 • CX02 • CCX12 • CX01
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
p7 = sym p6

proved : CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
proved = p7
