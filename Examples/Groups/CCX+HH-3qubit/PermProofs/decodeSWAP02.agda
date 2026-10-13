{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP02 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0024 as B24
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 as B34
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0076 as B76
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0091 as B91
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 as B93
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0094 as B94
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0105 as B105
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0252 as B252
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0259 as B259
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0288 as B288
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0294 as B294
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0330 as B330
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0338 as B338
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0355 as B355
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 as B357
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0423 as B423
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0429 as B429
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 as B435
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0439 as B439
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0487 as B487
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0503 as B503
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0512 as B512
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0566 as B566
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0916 as B916
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0965 as B965
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1050 as B1050
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1097 as B1097
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1107 as B1107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1605 as B1605
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 as B1658
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 as B1661
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2062 as B2062
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2682 as B2682
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2829 as B2829
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2850 as B2850
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2897 as B2897
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 as B3094
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3121 as B3121
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3219 as B3219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3579 as B3579
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4008 as B4008
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4158 as B4158
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5023 as B5023
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5146 as B5146
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5463 as B5463

p0 : SWAP02 ≈ SWAP02
p0 = refl

p1 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B481.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B215.proved) Eq.refl Eq.refl

p3 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p3 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B118.proved) Eq.refl Eq.refl

p4 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B47.proved) Eq.refl Eq.refl

p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p5 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B3094.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p6 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B36.proved) Eq.refl Eq.refl

p7 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p7 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B21.proved) Eq.refl Eq.refl

p8 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p8 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B3579.proved) Eq.refl Eq.refl

p9 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p9 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B357.proved) Eq.refl Eq.refl

p10 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p10 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B44.proved) Eq.refl Eq.refl

p11 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p11 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p12 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p12 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B47.proved) Eq.refl Eq.refl

p13 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p13 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B355.proved) Eq.refl Eq.refl

p14 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p14 = by-assoc-and (under (CX10) (CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B2829.proved) Eq.refl Eq.refl

p15 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p15 = by-assoc-and (under (ε) (CX12 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B1661.proved) Eq.refl Eq.refl

p16 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p16 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B26.proved) Eq.refl Eq.refl

p17 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p17 = by-assoc-and (under (CX02) (CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B1658.proved) Eq.refl Eq.refl

p18 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p18 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B25.proved) Eq.refl Eq.refl

p19 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p19 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B163.proved) Eq.refl Eq.refl

p20 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p20 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • CX02) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B153.proved) Eq.refl Eq.refl

p21 : CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p21 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B164.proved) Eq.refl Eq.refl

p22 : CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX10 • CCX01 • CCX12 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p22 = by-assoc-and (under (CX01) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B2682.proved) Eq.refl Eq.refl

p23 : CX01 • CX10 • CCX01 • CCX12 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX10 • CX02 • CCX12 • CX01 • X0 • CX12 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p23 = by-assoc-and (under (CX01 • CX10) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B4158.proved) Eq.refl Eq.refl

p24 : CX01 • CX10 • CX02 • CCX12 • CX01 • X0 • CX12 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • X0 • CX12 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p24 = by-assoc-and (under (CX01) (CX01 • X0 • CX12 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B315.proved) Eq.refl Eq.refl

p25 : CX01 • CX02 • CCX12 • CX12 • CX01 • X0 • CX12 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p25 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B503.proved) Eq.refl Eq.refl

p26 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • X0 • X2 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p26 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B5463.proved) Eq.refl Eq.refl

p27 : CX01 • CX02 • CCX12 • X0 • X2 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX12 • X2 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p27 = by-assoc-and (under (CX01 • CX02) (X2 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B46.proved) Eq.refl Eq.refl

p28 : CX01 • CX02 • X0 • CCX12 • X2 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p28 = by-assoc-and (under (CX01) (CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B916.proved) Eq.refl Eq.refl

p29 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X0 • X1 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p29 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01) (X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B44.proved) Eq.refl Eq.refl

p30 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X0 • X1 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p30 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X0) (CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B44.proved) Eq.refl Eq.refl

p31 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X1 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p31 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01) (X1 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B12.proved) Eq.refl Eq.refl

p32 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • CCX01 • X1 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • X1 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p32 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B186.proved) Eq.refl Eq.refl

p33 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX02 • X1 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CCX02 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p33 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (CX02 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B28.proved) Eq.refl Eq.refl

p34 : CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CCX02 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • X0 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p34 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B4008.proved) Eq.refl Eq.refl

p35 : CX01 • X0 • CX02 • CX10 • CCX12 • X0 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • CX10 • X0 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p35 = by-assoc-and (under (CX01 • X0 • CX02 • CX10) (CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B46.proved) Eq.refl Eq.refl

p36 : CX01 • X0 • CX02 • CX10 • X0 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X0 • CX02 • X0 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p36 = by-assoc-and (under (CX01 • X0 • CX02) (CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B47.proved) Eq.refl Eq.refl

p37 : CX01 • X0 • CX02 • X0 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • X2 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p37 = by-assoc-and (under (CX01) (CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B161.proved) Eq.refl Eq.refl

p38 : CX01 • X2 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX01 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p38 = by-assoc-and (under (ε) (CX02 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B22.proved) Eq.refl Eq.refl

p39 : X2 • CX01 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • X2 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p39 = by-assoc-and (under (ε) (CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B2062.proved) Eq.refl Eq.refl

p40 : CX01 • CX02 • CCX12 • X2 • CCX01 • CCX02 • X2 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p40 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B487.proved) Eq.refl Eq.refl

p41 : CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CCX02 • CX02 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p41 = by-assoc-and (under (CX01) (CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B2897.proved) Eq.refl Eq.refl

p42 : CX01 • CCX01 • CCX12 • CCX02 • CX02 • CX21 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CX21 • CX02 • CCX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p42 = by-assoc-and (under (CX01 • CCX01 • CCX12) (CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B429.proved) Eq.refl Eq.refl

p43 : CX01 • CCX01 • CCX12 • CX21 • CX02 • CCX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CX21 • CX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p43 = by-assoc-and (under (CX01 • CCX01 • CCX12 • CX21 • CX02) (CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B10.proved) Eq.refl Eq.refl

p44 : CX01 • CCX01 • CCX12 • CX21 • CX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CX21 • X1 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p44 = by-assoc-and (under (CX01 • CCX01 • CCX12 • CX21) (CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B120.proved) Eq.refl Eq.refl

p45 : CX01 • CCX01 • CCX12 • CX21 • X1 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • X1 • CX21 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p45 = by-assoc-and (under (CX01 • CCX01 • CCX12) (CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B34.proved) Eq.refl Eq.refl

p46 : CX01 • CCX01 • CCX12 • X1 • CX21 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • X1 • CX21 • CCX12 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p46 = by-assoc-and (under (CX01 • CCX01) (CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B288.proved) Eq.refl Eq.refl

p47 : CX01 • CCX01 • X1 • CX21 • CCX12 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • CX21 • CCX12 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p47 = by-assoc-and (under (ε) (CX21 • CCX12 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B435.proved) Eq.refl Eq.refl

p48 : X1 • CCX01 • CX01 • CX21 • CCX12 • CCX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • CX21 • CCX12 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p48 = by-assoc-and (under (X1 • CCX01 • CX01 • CX21 • CCX12) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B11.proved) Eq.refl Eq.refl

p49 : X1 • CCX01 • CX01 • CX21 • CCX12 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • X1 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p49 = by-assoc-and (under (X1 • CCX01 • CX01) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B439.proved) Eq.refl Eq.refl

p50 : X1 • CCX01 • CX01 • X1 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • X1 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p50 = by-assoc-and (under (X1 • CCX01) (CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B35.proved) Eq.refl Eq.refl

p51 : X1 • CCX01 • X1 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p51 = by-assoc-and (under (ε) (CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p52 : CX02 • CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p52 = by-assoc-and (under (ε) (CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B137.proved) Eq.refl Eq.refl

p53 : CX01 • CCX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • X0 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p53 = by-assoc-and (under (CX01 • CCX01 • CCX12) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B20.proved) Eq.refl Eq.refl

p54 : CX01 • CCX01 • CCX12 • X0 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • X0 • CCX12 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p54 = by-assoc-and (under (CX01 • CCX01) (CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B46.proved) Eq.refl Eq.refl

p55 : CX01 • CCX01 • X0 • CCX12 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • X0 • CX21 • CCX01 • CCX12 • X2 • CX20 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p55 = by-assoc-and (under (CX01 • CCX01 • X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B5146.proved) Eq.refl Eq.refl

p56 : CX01 • CCX01 • X0 • CX21 • CCX01 • CCX12 • X2 • CX20 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • X0 • CX21 • CCX01 • X2 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p56 = by-assoc-and (under (CX01 • CCX01 • X0 • CX21 • CCX01) (CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B566.proved) Eq.refl Eq.refl

p57 : CX01 • CCX01 • X0 • CX21 • CCX01 • X2 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • X0 • CX21 • X2 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p57 = by-assoc-and (under (CX01 • CCX01 • X0 • CX21) (CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B29.proved) Eq.refl Eq.refl

p58 : CX01 • CCX01 • X0 • CX21 • X2 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • X0 • CX21 • CX02 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p58 = by-assoc-and (under (ε) (CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B1605.proved) Eq.refl Eq.refl

p59 : CCX01 • X0 • CX21 • CX02 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • X0 • CX21 • CX02 • CX20 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p59 = by-assoc-and (under (CCX01 • X0 • CX21 • CX02) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B3219.proved) Eq.refl Eq.refl

p60 : CCX01 • X0 • CX21 • CX02 • CX20 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • X0 • CX02 • CX20 • CX01 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p60 = by-assoc-and (under (CCX01 • X0) (CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B259.proved) Eq.refl Eq.refl

p61 : CCX01 • X0 • CX02 • CX20 • CX01 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CX20 • X2 • CX01 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p61 = by-assoc-and (under (ε) (CX01 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B1097.proved) Eq.refl Eq.refl

p62 : CX02 • CCX01 • CX20 • X2 • CX01 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CX20 • CX21 • X2 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p62 = by-assoc-and (under (ε) (CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B3121.proved) Eq.refl Eq.refl

p63 : CX01 • CCX01 • CX20 • CX21 • X2 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CX20 • CX12 • X1 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p63 = by-assoc-and (under (CX01 • CCX01 • CX20) (CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B252.proved) Eq.refl Eq.refl

p64 : CX01 • CCX01 • CX20 • CX12 • X1 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX10 • CCX01 • CX20 • X1 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p64 = by-assoc-and (under (CX01) (X1 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B294.proved) Eq.refl Eq.refl

p65 : CX01 • CX10 • CCX01 • CX20 • X1 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX10 • CCX01 • X1 • CX20 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p65 = by-assoc-and (under (CX01 • CX10 • CCX01) (SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B24.proved) Eq.refl Eq.refl

p66 : CX01 • CX10 • CCX01 • X1 • CX20 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CCX01 • CX01 • CX10 • CX20 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p66 = by-assoc-and (under (ε) (CX20 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B1050.proved) Eq.refl Eq.refl

p67 : X0 • CCX01 • CX01 • CX10 • CX20 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX10 • CCX01 • CX21 • SWAP02 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p67 = by-assoc-and (under (X0) (CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B2850.proved) Eq.refl Eq.refl

p68 : X0 • CX10 • CCX01 • CX21 • SWAP02 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX10 • CCX01 • CX21 • CCX02 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p68 = by-assoc-and (under (X0 • CX10 • CCX01 • CX21) (CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B76.proved) Eq.refl Eq.refl

p69 : X0 • CX10 • CCX01 • CX21 • CCX02 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX10 • CX21 • CCX02 • CCX01 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p69 = by-assoc-and (under (X0 • CX10) (SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B330.proved) Eq.refl Eq.refl

p70 : X0 • CX10 • CX21 • CCX02 • CCX01 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CCX02 • X0 • CCX01 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p70 = by-assoc-and (under (ε) (CCX01 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B512.proved) Eq.refl Eq.refl

p71 : CX10 • CCX02 • X0 • CCX01 • SWAP02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CCX02 • X0 • CCX01 • CCX01 • SWAP02 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p71 = by-assoc-and (under (CX10 • CCX02 • X0 • CCX01) (CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B105.proved) Eq.refl Eq.refl

p72 : CX10 • CCX02 • X0 • CCX01 • CCX01 • SWAP02 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CCX02 • X0 • SWAP02 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p72 = by-assoc-and (under (CX10 • CCX02 • X0) (SWAP02 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B11.proved) Eq.refl Eq.refl

p73 : CX10 • CCX02 • X0 • SWAP02 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CCX02 • X0 • CCX12 • SWAP02 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p73 = by-assoc-and (under (CX10 • CCX02 • X0) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B104.proved) Eq.refl Eq.refl

p74 : CX10 • CCX02 • X0 • CCX12 • SWAP02 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • CCX02 • X0 • CCX12 • X2 • SWAP02 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p74 = by-assoc-and (under (CX10 • CCX02 • X0 • CCX12) (CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B94.proved) Eq.refl Eq.refl

p75 : CX10 • CCX02 • X0 • CCX12 • X2 • SWAP02 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01 • SWAP02 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p75 = by-assoc-and (under (ε) (SWAP02 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B5023.proved) Eq.refl Eq.refl

p76 : X2 • CCX02 • CCX12 • X1 • SWAP01 • SWAP02 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01 • CCX12 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01
p76 = by-assoc-and (under (X2 • CCX02 • CCX12 • X1 • SWAP01) (X2 • X0 • CCX01 • CCX02 • CCX01) B104.proved) Eq.refl Eq.refl

p77 : X2 • CCX02 • CCX12 • X1 • SWAP01 • CCX12 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CCX02 • CCX12 • X1 • CCX02 • SWAP01 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01
p77 = by-assoc-and (under (X2 • CCX02 • CCX12 • X1) (SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01) B91.proved) Eq.refl Eq.refl

p78 : X2 • CCX02 • CCX12 • X1 • CCX02 • SWAP01 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01
p78 = by-assoc-and (under (X2) (SWAP01 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01) B965.proved) Eq.refl Eq.refl

p79 : X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX01 • CX10 • CCX12 • CX01 • X0 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01
p79 = by-assoc-and (under (X2 • CX01) (SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01) B1107.proved) Eq.refl Eq.refl

p80 : X2 • CX01 • CX10 • CCX12 • CX01 • X0 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • X2 • CX01 • X0 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01
p80 = by-assoc-and (under (ε) (CX01 • X0 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01) B423.proved) Eq.refl Eq.refl

p81 : CX01 • CCX12 • X2 • CX01 • X0 • SWAP02 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • X2 • CX01 • X0 • X0 • SWAP02 • X0 • CCX01 • CCX02 • CCX01
p81 = by-assoc-and (under (CX01 • CCX12 • X2 • CX01 • X0) (X0 • CCX01 • CCX02 • CCX01) B93.proved) Eq.refl Eq.refl

p82 : CX01 • CCX12 • X2 • CX01 • X0 • X0 • SWAP02 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • X2 • CX01 • SWAP02 • X0 • CCX01 • CCX02 • CCX01
p82 = by-assoc-and (under (CX01 • CCX12 • X2 • CX01) (SWAP02 • X0 • CCX01 • CCX02 • CCX01) B12.proved) Eq.refl Eq.refl

p83 : CX01 • CCX12 • X2 • CX01 • SWAP02 • X0 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • X2 • CX01 • X2 • SWAP02 • CCX01 • CCX02 • CCX01
p83 = by-assoc-and (under (CX01 • CCX12 • X2 • CX01) (CCX01 • CCX02 • CCX01) B94.proved) Eq.refl Eq.refl

p84 : CX01 • CCX12 • X2 • CX01 • X2 • SWAP02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • X2 • X2 • CX01 • SWAP02 • CCX01 • CCX02 • CCX01
p84 = by-assoc-and (under (CX01 • CCX12 • X2) (SWAP02 • CCX01 • CCX02 • CCX01) B22.proved) Eq.refl Eq.refl

p85 : CX01 • CCX12 • X2 • X2 • CX01 • SWAP02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • CX01 • SWAP02 • CCX01 • CCX02 • CCX01
p85 = by-assoc-and (under (CX01 • CCX12) (CX01 • SWAP02 • CCX01 • CCX02 • CCX01) B4.proved) Eq.refl Eq.refl

p86 : CX01 • CCX12 • CX01 • SWAP02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CCX12 • SWAP02 • CCX02 • CCX01
p86 = by-assoc-and (under (CX01 • CCX12 • CX01) (CCX02 • CCX01) B104.proved) Eq.refl Eq.refl

p87 : CX01 • CCX12 • CX01 • CCX12 • SWAP02 • CCX02 • CCX01 ≈ CCX12 • CCX02 • SWAP02 • CCX02 • CCX01
p87 = by-assoc-and (under (ε) (SWAP02 • CCX02 • CCX01) B338.proved) Eq.refl Eq.refl

p88 : CCX12 • CCX02 • SWAP02 • CCX02 • CCX01 ≈ CCX12 • CCX02 • CCX02 • SWAP02 • CCX01
p88 = by-assoc-and (under (CCX12 • CCX02) (CCX01) B76.proved) Eq.refl Eq.refl

p89 : CCX12 • CCX02 • CCX02 • SWAP02 • CCX01 ≈ CCX12 • SWAP02 • CCX01
p89 = by-assoc-and (under (CCX12) (SWAP02 • CCX01) B10.proved) Eq.refl Eq.refl

p90 : CCX12 • SWAP02 • CCX01 ≈ CCX12 • CCX12 • SWAP02
p90 = by-assoc-and (under (CCX12) (ε) B104.proved) Eq.refl Eq.refl

p91 : CCX12 • CCX12 • SWAP02 ≈ SWAP02
p91 = by-assoc-and (under (ε) (SWAP02) B14.proved) Eq.refl Eq.refl

p92 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ SWAP02
p92 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (trans p52 (trans p53 (trans p54 (trans p55 (trans p56 (trans p57 (trans p58 (trans p59 (trans p60 (trans p61 (trans p62 (trans p63 (trans p64 (trans p65 (trans p66 (trans p67 (trans p68 (trans p69 (trans p70 (trans p71 (trans p72 (trans p73 (trans p74 (trans p75 (trans p76 (trans p77 (trans p78 (trans p79 (trans p80 (trans p81 (trans p82 (trans p83 (trans p84 (trans p85 (trans p86 (trans p87 (trans p88 (trans p89 (trans p90 (trans p91 (refl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

proved : SWAP02 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
proved = trans p0 (sym p92)
