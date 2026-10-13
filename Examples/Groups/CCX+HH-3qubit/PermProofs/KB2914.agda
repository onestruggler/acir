{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2914 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 as B138
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0661 as B661
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1265 as B1265

p0 : CX20 • CCX12 • CCX01 • CX21 • CCX01 • CCX02 ≈ CX20 • CCX12 • CX21 • CCX01
p0 = by-assoc-and (under (CX20 • CCX12) (ε) B1265.proved) Eq.refl Eq.refl

p1 : CX20 • CCX12 • CCX01 • CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
p1 = by-assoc-and (under (ε) (CCX01 • CCX02) B661.proved) Eq.refl Eq.refl

p2 : CX20 • CCX12 • CX21 • CCX01 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
p2 = trans (sym p0) p1

p3 : CX20 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX12 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B138.proved) Eq.refl Eq.refl

p4 : CX20 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX12 • CCX01
p4 = trans p3 (refl)

p5 : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
p5 = refl

p6 : CX21 • CCX12 • CCX01 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX12 • CCX01
p7 = sym p6

proved : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX12 • CCX01
proved = p7
