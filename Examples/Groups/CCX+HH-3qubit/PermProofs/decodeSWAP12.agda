{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0079 as B79
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515

p0 : SWAP12 ≈ SWAP12
p0 = refl

p1 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p3 : X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
p3 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX02 • CCX01) B515.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01
p4 = by-assoc-and (under (CX12 • CX21) (CCX02 • CCX01) B308.proved) Eq.refl Eq.refl

p5 : CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ SWAP12 • CCX01 • CCX02 • CCX02 • CCX01
p5 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX02 • CCX01) B79.proved) Eq.refl Eq.refl

p6 : SWAP12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX02 • SWAP12 • CCX02 • CCX02 • CCX01
p6 = by-assoc-and (under (ε) (CCX02 • CCX02 • CCX01) B107.proved) Eq.refl Eq.refl

p7 : CCX02 • SWAP12 • CCX02 • CCX02 • CCX01 ≈ CCX02 • CCX01 • SWAP12 • CCX02 • CCX01
p7 = by-assoc-and (under (CCX02) (CCX02 • CCX01) B108.proved) Eq.refl Eq.refl

p8 : CCX02 • CCX01 • SWAP12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01 • SWAP12 • CCX01
p8 = by-assoc-and (under (CCX02 • CCX01) (CCX01) B108.proved) Eq.refl Eq.refl

p9 : CCX02 • CCX01 • CCX01 • SWAP12 • CCX01 ≈ CCX02 • SWAP12 • CCX01
p9 = by-assoc-and (under (CCX02) (SWAP12 • CCX01) B11.proved) Eq.refl Eq.refl

p10 : CCX02 • SWAP12 • CCX01 ≈ CCX02 • CCX02 • SWAP12
p10 = by-assoc-and (under (CCX02) (ε) B107.proved) Eq.refl Eq.refl

p11 : CCX02 • CCX02 • SWAP12 ≈ SWAP12
p11 = by-assoc-and (under (ε) (SWAP12) B10.proved) Eq.refl Eq.refl

p12 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ SWAP12
p12 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (refl)))))))))))

proved : SWAP12 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01
proved = trans p0 (sym p12)
