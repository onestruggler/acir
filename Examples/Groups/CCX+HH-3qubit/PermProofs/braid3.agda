{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.braid3 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0074 as B74
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0090 as B90
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0097 as B97
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0112 as B112
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0231 as B231
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0310 as B310
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0314 as B314
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0326 as B326
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 as B357
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 as B366
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0416 as B416
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0423 as B423
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 as B435
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0480 as B480
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0562 as B562
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0596 as B596
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 as B623
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0788 as B788
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0805 as B805
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0836 as B836
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0963 as B963
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1107 as B1107

p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B481.proved) Eq.refl Eq.refl

p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B118.proved) Eq.refl Eq.refl

p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B29.proved) Eq.refl Eq.refl

p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p5 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B21.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p6 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B366.proved) Eq.refl Eq.refl

p7 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p7 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p8 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p8 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p9 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p9 = by-assoc-and (under (X2 • CX10) (CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B963.proved) Eq.refl Eq.refl

p10 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p10 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B26.proved) Eq.refl Eq.refl

p11 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX10 • X1 • CX12 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p11 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B357.proved) Eq.refl Eq.refl

p12 : X2 • CX10 • CX12 • CCX02 • CX10 • X1 • CX12 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X1 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p12 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B805.proved) Eq.refl Eq.refl

p13 : X2 • CX10 • CX12 • CCX02 • X0 • X1 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p13 = by-assoc-and (under (X2 • CX10 • CX12) (CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B231.proved) Eq.refl Eq.refl

p14 : X2 • CX10 • CX12 • X1 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p14 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B357.proved) Eq.refl Eq.refl

p15 : CX10 • X1 • CX12 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • CCX02 • X0 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p15 = by-assoc-and (under (CX10 • X1) (CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B623.proved) Eq.refl Eq.refl

p16 : CX10 • X1 • CCX01 • CCX02 • X0 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • CCX02 • X1 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p16 = by-assoc-and (under (CX10 • X1 • CCX01 • CCX02) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B115.proved) Eq.refl Eq.refl

p17 : CX10 • X1 • CCX01 • CCX02 • X1 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • X1 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p17 = by-assoc-and (under (CX10 • X1 • CCX01) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B28.proved) Eq.refl Eq.refl

p18 : CX10 • X1 • CCX01 • X1 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CX02 • CCX01 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p18 = by-assoc-and (under (CX10) (CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B150.proved) Eq.refl Eq.refl

p19 : CX10 • CX02 • CCX01 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX01 • CX10 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p19 = by-assoc-and (under (ε) (CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B314.proved) Eq.refl Eq.refl

p20 : CX02 • CCX01 • CX10 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX01 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p20 = by-assoc-and (under (CX02 • CCX01) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B219.proved) Eq.refl Eq.refl

p21 : CX02 • CCX01 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p21 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B137.proved) Eq.refl Eq.refl

p22 : CX01 • CCX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p22 = by-assoc-and (under (CX01 • CCX01 • CCX12) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B221.proved) Eq.refl Eq.refl

p23 : CX01 • CCX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p23 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B153.proved) Eq.refl Eq.refl

p24 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p24 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01) (X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p25 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p25 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01) (CCX02 • CX10 • X0 • CCX01 • X2 • X0) B118.proved) Eq.refl Eq.refl

p26 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • X2 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p26 = by-assoc-and (under (CX01 • CCX01) (CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) B562.proved) Eq.refl Eq.refl

p27 : CX01 • CCX01 • X2 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • X2 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p27 = by-assoc-and (under (CX01) (CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) B29.proved) Eq.refl Eq.refl

p28 : CX01 • X2 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p28 = by-assoc-and (under (ε) (CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) B22.proved) Eq.refl Eq.refl

p29 : X2 • CX01 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX01 • CCX12 • CCX01 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p29 = by-assoc-and (under (X2 • CX01 • CCX01 • CCX12) (CCX02 • CX10 • X0 • CCX01 • X2 • X0) B74.proved) Eq.refl Eq.refl

p30 : X2 • CX01 • CCX01 • CCX12 • CCX01 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX02 • CCX12 • CX02 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p30 = by-assoc-and (under (X2 • CX01) (SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) B211.proved) Eq.refl Eq.refl

p31 : X2 • CX01 • CX02 • CCX12 • CX02 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX02 • CCX12 • CX02 • CCX12 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0
p31 = by-assoc-and (under (X2 • CX01 • CX02 • CCX12 • CX02) (CX10 • X0 • CCX01 • X2 • X0) B90.proved) Eq.refl Eq.refl

p32 : X2 • CX01 • CX02 • CCX12 • CX02 • CCX12 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0
p32 = by-assoc-and (under (X2 • CX01) (SWAP01 • CX10 • X0 • CCX01 • X2 • X0) B326.proved) Eq.refl Eq.refl

p33 : X2 • CX01 • CCX12 • CCX01 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • CX01 • SWAP01 • X0 • CCX01 • X2 • X0
p33 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01) (X0 • CCX01 • X2 • X0) B112.proved) Eq.refl Eq.refl

p34 : X2 • CX01 • CCX12 • CCX01 • CX01 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • CX01 • X1 • SWAP01 • CCX01 • X2 • X0
p34 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01 • CX01) (CCX01 • X2 • X0) B97.proved) Eq.refl Eq.refl

p35 : X2 • CX01 • CCX12 • CCX01 • CX01 • X1 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • X1 • CX01 • SWAP01 • CCX01 • X2 • X0
p35 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01) (SWAP01 • CCX01 • X2 • X0) B35.proved) Eq.refl Eq.refl

p36 : X2 • CX01 • CCX12 • CCX01 • X1 • CX01 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • SWAP01 • CCX01 • X2 • X0
p36 = by-assoc-and (under (X2 • CX01 • CCX12) (SWAP01 • CCX01 • X2 • X0) B282.proved) Eq.refl Eq.refl

p37 : X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • SWAP01 • X2 • X0
p37 = by-assoc-and (under (X2 • CX01 • CCX12 • X1 • CX01 • CCX01) (X2 • X0) B74.proved) Eq.refl Eq.refl

p38 : X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • SWAP01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • X2 • X0
p38 = by-assoc-and (under (X2 • CX01 • CCX12 • X1 • CX01) (SWAP01 • X2 • X0) B11.proved) Eq.refl Eq.refl

p39 : X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • X2 • X0 ≈ X2 • CX01 • CX10 • CCX12 • CX01 • X0 • X2 • X0
p39 = by-assoc-and (under (X2 • CX01) (X2 • X0) B1107.proved) Eq.refl Eq.refl

p40 : X2 • CX01 • CX10 • CCX12 • CX01 • X0 • X2 • X0 ≈ CX01 • CCX12 • X2 • CX01 • X0 • X2 • X0
p40 = by-assoc-and (under (ε) (CX01 • X0 • X2 • X0) B423.proved) Eq.refl Eq.refl

p41 : CX01 • CCX12 • X2 • CX01 • X0 • X2 • X0 ≈ CX01 • CCX12 • X2 • X2 • CX01 • X0 • X0
p41 = by-assoc-and (under (CX01 • CCX12 • X2) (X0) B221.proved) Eq.refl Eq.refl

p42 : CX01 • CCX12 • X2 • X2 • CX01 • X0 • X0 ≈ CX01 • CCX12 • CX01 • X0 • X0
p42 = by-assoc-and (under (CX01 • CCX12) (CX01 • X0 • X0) B4.proved) Eq.refl Eq.refl

p43 : CX01 • CCX12 • CX01 • X0 • X0 ≈ CX01 • CCX12 • CX01
p43 = by-assoc-and (under (CX01 • CCX12 • CX01) (ε) B12.proved) Eq.refl Eq.refl

p44 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX12 • CX01
p44 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (refl))))))))))))))))))))))))))))))))))))))))))))

p45 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p45 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B150.proved) Eq.refl Eq.refl

p46 : CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p46 = by-assoc-and (under (CX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B223.proved) Eq.refl Eq.refl

p47 : CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p47 = by-assoc-and (under (ε) (CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B33.proved) Eq.refl Eq.refl

p48 : X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p48 = by-assoc-and (under (ε) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B416.proved) Eq.refl Eq.refl

p49 : CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p49 = by-assoc-and (under (ε) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B480.proved) Eq.refl Eq.refl

p50 : X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p50 = by-assoc-and (under (X0 • CX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B45.proved) Eq.refl Eq.refl

p51 : X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p51 = by-assoc-and (under (ε) (CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B161.proved) Eq.refl Eq.refl

p52 : X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p52 = by-assoc-and (under (X2 • CX02 • CX12) (X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B215.proved) Eq.refl Eq.refl

p53 : X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p53 = by-assoc-and (under (X2 • CX02) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B26.proved) Eq.refl Eq.refl

p54 : X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p54 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) B310.proved) Eq.refl Eq.refl

p55 : X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1
p55 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02) (CCX01 • X2 • X0 • X1 • CCX01 • X1) B47.proved) Eq.refl Eq.refl

p56 : X2 • CX10 • CX02 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1
p56 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02 • X0 • CX10) (X0 • X1 • CCX01 • X1) B29.proved) Eq.refl Eq.refl

p57 : X2 • CX10 • CX02 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
p57 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02 • X0) (CCX01 • X0 • X1 • CCX01 • X1) B21.proved) Eq.refl Eq.refl

p58 : X2 • CX10 • CX02 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • X2 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
p58 = by-assoc-and (under (X2 • CX10) (CX10 • CCX01 • X0 • X1 • CCX01 • X1) B836.proved) Eq.refl Eq.refl

p59 : X2 • CX10 • X2 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • X2 • CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
p59 = by-assoc-and (under (X2) (CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1) B21.proved) Eq.refl Eq.refl

p60 : X2 • X2 • CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
p60 = by-assoc-and (under (ε) (CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1) B4.proved) Eq.refl Eq.refl

p61 : CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • X1 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1
p61 = by-assoc-and (under (CX10 • CCX02) (X0 • X1 • CCX01 • X1) B788.proved) Eq.refl Eq.refl

p62 : CX10 • CCX02 • X1 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1
p62 = by-assoc-and (under (CX10) (CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1) B28.proved) Eq.refl Eq.refl

p63 : CX10 • X1 • CCX02 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • CX10 • X0 • X1 • X1 • CCX01 • X1
p63 = by-assoc-and (under (CX10 • X1 • CCX02 • CCX01 • CX10) (X1 • CCX01 • X1) B44.proved) Eq.refl Eq.refl

p64 : CX10 • X1 • CCX02 • CCX01 • CX10 • X0 • X1 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • X0 • CX10 • X1 • X1 • CCX01 • X1
p64 = by-assoc-and (under (CX10 • X1 • CCX02 • CCX01) (X1 • X1 • CCX01 • X1) B47.proved) Eq.refl Eq.refl

p65 : CX10 • X1 • CCX02 • CCX01 • X0 • CX10 • X1 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • X0 • CX10 • CCX01 • X1 • X1 • CCX01 • X1
p65 = by-assoc-and (under (CX10 • X1 • CCX02) (X1 • X1 • CCX01 • X1) B280.proved) Eq.refl Eq.refl

p66 : CX10 • X1 • CCX02 • X0 • CX10 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • CX10 • X1 • CCX01 • X1 • X1 • CCX01 • X1
p66 = by-assoc-and (under (CX10) (CCX01 • X1 • X1 • CCX01 • X1) B596.proved) Eq.refl Eq.refl

p67 : CX10 • CCX02 • CX10 • X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X1 • CCX01 • X1
p67 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • X1 • CCX01 • X1) B219.proved) Eq.refl Eq.refl

p68 : CX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X1 • CCX01 • X1
p68 = by-assoc-and (under (CX01 • CCX12) (CCX01 • X1 • X1 • CCX01 • X1) B35.proved) Eq.refl Eq.refl

p69 : CX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • X1 • CCX01 • CX01 • X1 • CCX01 • X1
p69 = by-assoc-and (under (CX01 • CCX12 • X1) (X1 • CCX01 • X1) B435.proved) Eq.refl Eq.refl

p70 : CX01 • CCX12 • X1 • X1 • CCX01 • CX01 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CCX01 • CX01 • X1 • CCX01 • X1
p70 = by-assoc-and (under (CX01 • CCX12) (CCX01 • CX01 • X1 • CCX01 • X1) B3.proved) Eq.refl Eq.refl

p71 : CX01 • CCX12 • CCX01 • CX01 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CCX01 • X1 • CX01 • CCX01 • X1
p71 = by-assoc-and (under (CX01 • CCX12 • CCX01) (CCX01 • X1) B35.proved) Eq.refl Eq.refl

p72 : CX01 • CCX12 • CCX01 • X1 • CX01 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • X1
p72 = by-assoc-and (under (CX01 • CCX12) (CCX01 • X1) B282.proved) Eq.refl Eq.refl

p73 : CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • X1
p73 = by-assoc-and (under (CX01 • CCX12 • X1 • CX01) (X1) B11.proved) Eq.refl Eq.refl

p74 : CX01 • CCX12 • X1 • CX01 • X1 ≈ CX01 • CCX12 • X1 • X1 • CX01
p74 = by-assoc-and (under (CX01 • CCX12 • X1) (ε) B35.proved) Eq.refl Eq.refl

p75 : CX01 • CCX12 • X1 • X1 • CX01 ≈ CX01 • CCX12 • CX01
p75 = by-assoc-and (under (CX01 • CCX12) (CX01) B3.proved) Eq.refl Eq.refl

p76 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CX01
p76 = trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (trans p52 (trans p53 (trans p54 (trans p55 (trans p56 (trans p57 (trans p58 (trans p59 (trans p60 (trans p61 (trans p62 (trans p63 (trans p64 (trans p65 (trans p66 (trans p67 (trans p68 (trans p69 (trans p70 (trans p71 (trans p72 (trans p73 (trans p74 (trans p75 (refl)))))))))))))))))))))))))))))))

proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
proved = trans p44 (sym p76)
