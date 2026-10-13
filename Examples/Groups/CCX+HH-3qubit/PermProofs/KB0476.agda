{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0476 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0024 as B24
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0085 as B85
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0151 as B151

p0 : CX20 • X1 • CX02 • CCX01 ≈ CX20 • CCX01 • X1
p0 = by-assoc-and (under (CX20) (ε) B151.proved) Eq.refl Eq.refl

p1 : CX20 • X1 • CX02 • CCX01 ≈ X1 • CX20 • CX02 • CCX01
p1 = by-assoc-and (under (ε) (CX02 • CCX01) B24.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • X1 ≈ X1 • CX20 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • X1 ≈ CX20 • CCX01 • X1
p3 = refl

p4 : X1 • CX20 • CX02 • CCX01 ≈ X1 • CX02 • SWAP02 • CCX01
p4 = by-assoc-and (under (X1) (CCX01) B85.proved) Eq.refl Eq.refl

p5 : X1 • CX02 • SWAP02 • CCX01 ≈ X1 • CX02 • CCX12 • SWAP02
p5 = by-assoc-and (under (X1 • CX02) (ε) B104.proved) Eq.refl Eq.refl

p6 : X1 • CX20 • CX02 • CCX01 ≈ X1 • CX02 • CCX12 • SWAP02
p6 = trans p4 (trans p5 (refl))

p7 : CX20 • CCX01 • X1 ≈ X1 • CX02 • CCX12 • SWAP02
p7 = trans (sym p3) (trans p2 p6)

p8 : X1 • CX02 • CCX12 • SWAP02 ≈ CX20 • CCX01 • X1
p8 = sym p7

proved : X1 • CX02 • CCX12 • SWAP02 ≈ CX20 • CCX01 • X1
proved = p8
