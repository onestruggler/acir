{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0818 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 as B80
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308

p0 : CX21 • CCX02 • X0 • CCX01 • X0 ≈ CX21 • CCX02 • CX12 • CCX01
p0 = by-assoc-and (under (CX21 • CCX02) (ε) B153.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B129.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX12 • CCX01 ≈ X0 • CCX02 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX12 • CCX01 ≈ CX21 • CX12 • CCX01 • CCX02
p3 = by-assoc-and (under (CX21) (ε) B308.proved) Eq.refl Eq.refl

p4 : CX21 • CX12 • CCX01 • CCX02 ≈ CX12 • SWAP12 • CCX01 • CCX02
p4 = by-assoc-and (under (ε) (CCX01 • CCX02) B80.proved) Eq.refl Eq.refl

p5 : CX12 • SWAP12 • CCX01 • CCX02 ≈ CX12 • CCX02 • SWAP12 • CCX02
p5 = by-assoc-and (under (CX12) (CCX02) B107.proved) Eq.refl Eq.refl

p6 : CX12 • CCX02 • SWAP12 • CCX02 ≈ CX12 • CCX02 • CCX01 • SWAP12
p6 = by-assoc-and (under (CX12 • CCX02) (ε) B108.proved) Eq.refl Eq.refl

p7 : CX21 • CCX02 • CX12 • CCX01 ≈ CX12 • CCX02 • CCX01 • SWAP12
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

p8 : X0 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0
p8 = refl

p9 : CX12 • CCX02 • CCX01 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0
p9 = trans (sym p7) (trans p2 p8)

proved : CX12 • CCX02 • CCX01 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0
proved = p9
