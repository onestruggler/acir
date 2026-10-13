{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0176 as B176
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0218 as B218

p0 : CX20 • CCX01 • CX20 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
p0 = by-assoc-and (under (ε) (CX21 • CCX02) B218.proved) Eq.refl Eq.refl

p1 : CX20 • CCX01 • CX20 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
p1 = by-assoc-and (under (CX20 • CCX01) (ε) B176.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
p3 = refl

p4 : CX20 • CCX01 • CCX02 • CX20 ≈ CX20 • CCX01 • CCX02 • CX20
p4 = refl

p5 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
proved = p5
