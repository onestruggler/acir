{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeX1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0158 as B158
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1438 as B1438
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1439 as B1439

p0 : X1 ≈ X1
p0 = refl

p1 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p3 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p3 = by-assoc-and (under (ε) (CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B515.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p4 = by-assoc-and (under (CX12 • CX21 • CCX02) (X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p5 : CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p5 = by-assoc-and (under (CX12) (CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B129.proved) Eq.refl Eq.refl

p6 : CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p6 = by-assoc-and (under (ε) (CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p7 : X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • CCX02 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p7 = by-assoc-and (under (X0) (X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B1438.proved) Eq.refl Eq.refl

p8 : X0 • X1 • CCX01 • CX01 • CCX02 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • X1 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p8 = by-assoc-and (under (X0 • X1 • CCX01 • CX01) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B28.proved) Eq.refl Eq.refl

p9 : X0 • X1 • CCX01 • CX01 • X1 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • X1 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p9 = by-assoc-and (under (X0 • X1 • CCX01) (CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B35.proved) Eq.refl Eq.refl

p10 : X0 • X1 • CCX01 • X1 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • CCX01 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p10 = by-assoc-and (under (X0) (CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p11 : X0 • CX02 • CCX01 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p11 = by-assoc-and (under (X0) (CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B137.proved) Eq.refl Eq.refl

p12 : X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p12 = by-assoc-and (under (X0 • CX01 • CCX01 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B12.proved) Eq.refl Eq.refl

p13 : X0 • CX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p13 = by-assoc-and (under (X0 • CX01) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p14 : X0 • CX01 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p14 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p15 : X0 • CX01 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • X0 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p15 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02 • X0) (CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p16 : X0 • CX01 • CX12 • CCX02 • X0 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p16 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02) (CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B12.proved) Eq.refl Eq.refl

p17 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p17 = by-assoc-and (under (X0 • CX01) (CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p18 : X0 • CX01 • CCX01 • CCX02 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p18 = by-assoc-and (under (X0 • CX01 • CCX01) (CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B10.proved) Eq.refl Eq.refl

p19 : X0 • CX01 • CCX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p19 = by-assoc-and (under (X0 • CX01) (X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B11.proved) Eq.refl Eq.refl

p20 : X0 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p20 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B158.proved) Eq.refl Eq.refl

p21 : X1 • CX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX01 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p21 = by-assoc-and (under (X1 • CX01) (X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p22 : X1 • CX01 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p22 = by-assoc-and (under (X1) (CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B1439.proved) Eq.refl Eq.refl

p23 : X1 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p23 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p24 : CX02 • CCX01 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX12 • CCX02 • CX12 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p24 = by-assoc-and (under (CX02) (CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p25 : CX02 • CX12 • CCX02 • CX12 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01
p25 = by-assoc-and (under (CX02) (X1 • CCX01 • CCX01 • CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p26 : CX02 • CCX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p26 = by-assoc-and (under (CX02 • CCX01) (CCX01 • CCX01 • CCX02 • CCX01) B28.proved) Eq.refl Eq.refl

p27 : CX02 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
p27 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) B120.proved) Eq.refl Eq.refl

p28 : X1 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
p28 = by-assoc-and (under (X1) (CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p29 : X1 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX02 • CCX02 • CCX01
p29 = by-assoc-and (under (X1) (CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p30 : X1 • CCX01 • CCX02 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX01
p30 = by-assoc-and (under (X1 • CCX01) (CCX01) B10.proved) Eq.refl Eq.refl

p31 : X1 • CCX01 • CCX01 ≈ X1
p31 = by-assoc-and (under (X1) (ε) B11.proved) Eq.refl Eq.refl

p32 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1
p32 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (refl)))))))))))))))))))))))))))))))

proved : X1 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
proved = trans p0 (sym p32)
