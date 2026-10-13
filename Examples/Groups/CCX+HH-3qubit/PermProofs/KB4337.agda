{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4337 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0076 as B76
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0085 as B85
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 as B93
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0827 as B827

p0 : CX20 • CX02 • CCX01 • CCX02 • X2 ≈ CX20 • X2 • CX01 • CCX01 • CCX02
p0 = by-assoc-and (under (CX20) (ε) B827.proved) Eq.refl Eq.refl

p1 : CX20 • CX02 • CCX01 • CCX02 • X2 ≈ CX02 • SWAP02 • CCX01 • CCX02 • X2
p1 = by-assoc-and (under (ε) (CCX01 • CCX02 • X2) B85.proved) Eq.refl Eq.refl

p2 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • SWAP02 • CCX01 • CCX02 • X2
p2 = trans (sym p0) p1

p3 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX20 • X2 • CX01 • CCX01 • CCX02
p3 = refl

p4 : CX02 • SWAP02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX12 • SWAP02 • CCX02 • X2
p4 = by-assoc-and (under (CX02) (CCX02 • X2) B104.proved) Eq.refl Eq.refl

p5 : CX02 • CCX12 • SWAP02 • CCX02 • X2 ≈ CX02 • CCX12 • CCX02 • SWAP02 • X2
p5 = by-assoc-and (under (CX02 • CCX12) (X2) B76.proved) Eq.refl Eq.refl

p6 : CX02 • CCX12 • CCX02 • SWAP02 • X2 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
p6 = by-assoc-and (under (CX02 • CCX12 • CCX02) (ε) B93.proved) Eq.refl Eq.refl

p7 : CX02 • SWAP02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
p7 = trans p4 (trans p5 (trans p6 (refl)))

p8 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
p8 = trans (sym p3) (trans p2 p7)

proved : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
proved = p8
