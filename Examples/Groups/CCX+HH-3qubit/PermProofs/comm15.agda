{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm15 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0079 as B79
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0445 as B445
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0742 as B742

p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX02 • CCX01) B515.proved) Eq.refl Eq.refl

p3 : CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01
p3 = by-assoc-and (under (CX12 • CX21) (CCX02 • CCX01) B308.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ SWAP12 • CCX01 • CCX02 • CCX02 • CCX01
p4 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX02 • CCX01) B79.proved) Eq.refl Eq.refl

p5 : SWAP12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX02 • SWAP12 • CCX02 • CCX02 • CCX01
p5 = by-assoc-and (under (ε) (CCX02 • CCX02 • CCX01) B107.proved) Eq.refl Eq.refl

p6 : CCX02 • SWAP12 • CCX02 • CCX02 • CCX01 ≈ CCX02 • CCX01 • SWAP12 • CCX02 • CCX01
p6 = by-assoc-and (under (CCX02) (CCX02 • CCX01) B108.proved) Eq.refl Eq.refl

p7 : CCX02 • CCX01 • SWAP12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01 • SWAP12 • CCX01
p7 = by-assoc-and (under (CCX02 • CCX01) (CCX01) B108.proved) Eq.refl Eq.refl

p8 : CCX02 • CCX01 • CCX01 • SWAP12 • CCX01 ≈ CCX02 • SWAP12 • CCX01
p8 = by-assoc-and (under (CCX02) (SWAP12 • CCX01) B11.proved) Eq.refl Eq.refl

p9 : CCX02 • SWAP12 • CCX01 ≈ CCX02 • CCX02 • SWAP12
p9 = by-assoc-and (under (CCX02) (ε) B107.proved) Eq.refl Eq.refl

p10 : CCX02 • CCX02 • SWAP12 ≈ SWAP12
p10 = by-assoc-and (under (ε) (SWAP12) B10.proved) Eq.refl Eq.refl

p11 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ SWAP12
p11 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))))))

p12 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p12 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p13 : CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0
p13 = by-assoc-and (under (CX12 • CCX02) (CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p14 : CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • CCX02 • CCX01 • X0
p14 = by-assoc-and (under (CX12 • CCX02) (CCX02 • CCX01 • X0) B121.proved) Eq.refl Eq.refl

p15 : CX12 • CCX02 • CCX01 • X0 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0 • CCX01 • X0
p15 = by-assoc-and (under (CX12) (CCX01 • X0) B742.proved) Eq.refl Eq.refl

p16 : CX12 • CX21 • CCX01 • X0 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12 • CCX01 • X0
p16 = by-assoc-and (under (ε) (CCX01 • X0) B445.proved) Eq.refl Eq.refl

p17 : X0 • CCX02 • SWAP12 • CCX01 • X0 ≈ X0 • CCX02 • CCX02 • SWAP12 • X0
p17 = by-assoc-and (under (X0 • CCX02) (X0) B107.proved) Eq.refl Eq.refl

p18 : X0 • CCX02 • CCX02 • SWAP12 • X0 ≈ X0 • SWAP12 • X0
p18 = by-assoc-and (under (X0) (SWAP12 • X0) B10.proved) Eq.refl Eq.refl

p19 : X0 • SWAP12 • X0 ≈ X0 • X0 • SWAP12
p19 = by-assoc-and (under (X0) (ε) B15.proved) Eq.refl Eq.refl

p20 : X0 • X0 • SWAP12 ≈ SWAP12
p20 = by-assoc-and (under (ε) (SWAP12) B12.proved) Eq.refl Eq.refl

p21 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ SWAP12
p21 = trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (refl)))))))))

proved : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0
proved = trans p11 (sym p21)
