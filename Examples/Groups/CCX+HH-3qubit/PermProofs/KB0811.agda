{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0811 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0085 as B85
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 as B105
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0132 as B132
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322

p0 : CX20 • CCX12 • X1 • CCX01 • X1 ≈ CX20 • CCX12 • CX02 • CCX01
p0 = by-assoc-and (under (CX20 • CCX12) (ε) B150.proved) Eq.refl Eq.refl

p1 : CX20 • CCX12 • X1 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1
p1 = by-assoc-and (under (ε) (CCX01 • X1) B132.proved) Eq.refl Eq.refl

p2 : CX20 • CCX12 • CX02 • CCX01 ≈ X1 • CCX12 • CCX01 • X1
p2 = trans (sym p0) p1

p3 : CX20 • CCX12 • CX02 • CCX01 ≈ CX20 • CX02 • CCX01 • CCX12
p3 = by-assoc-and (under (CX20) (ε) B322.proved) Eq.refl Eq.refl

p4 : CX20 • CX02 • CCX01 • CCX12 ≈ CX02 • SWAP02 • CCX01 • CCX12
p4 = by-assoc-and (under (ε) (CCX01 • CCX12) B85.proved) Eq.refl Eq.refl

p5 : CX02 • SWAP02 • CCX01 • CCX12 ≈ CX02 • CCX12 • SWAP02 • CCX12
p5 = by-assoc-and (under (CX02) (CCX12) B104.proved) Eq.refl Eq.refl

p6 : CX02 • CCX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CCX01 • SWAP02
p6 = by-assoc-and (under (CX02 • CCX12) (ε) B105.proved) Eq.refl Eq.refl

p7 : CX20 • CCX12 • CX02 • CCX01 ≈ CX02 • CCX12 • CCX01 • SWAP02
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

p8 : X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1
p8 = refl

p9 : CX02 • CCX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1
p9 = trans (sym p7) (trans p2 p8)

proved : CX02 • CCX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1
proved = p9
