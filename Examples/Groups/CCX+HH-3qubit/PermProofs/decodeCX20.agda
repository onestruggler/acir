{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX20 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0017 as B17
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0041 as B41
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0076 as B76
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0078 as B78
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0080 as B80
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0093 as B93
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0104 as B104
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0107 as B107
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0108 as B108
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0223 as B223
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0303 as B303
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0305 as B305
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0309 as B309
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0310 as B310
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0316 as B316
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0416 as B416
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0423 as B423
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 as B435
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0439 as B439
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0476 as B476
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0480 as B480
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0514 as B514
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0566 as B566
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0614 as B614
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0657 as B657
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0774 as B774
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0813 as B813
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0814 as B814
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0862 as B862
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0874 as B874
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0921 as B921
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1186 as B1186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1231 as B1231
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1241 as B1241
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1352 as B1352
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1353 as B1353
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1630 as B1630
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1823 as B1823
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1890 as B1890
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1925 as B1925
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2217 as B2217
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3219 as B3219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3825 as B3825
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3874 as B3874
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3939 as B3939
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4012 as B4012
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4039 as B4039
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4082 as B4082
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4312 as B4312
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4337 as B4337
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5008 as B5008
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5146 as B5146
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5483 as B5483

p0 : CX20 ≈ CX20
p0 = refl

p1 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p1 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B150.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p2 = by-assoc-and (under (CX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B223.proved) Eq.refl Eq.refl

p3 : CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p3 = by-assoc-and (under (ε) (CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B33.proved) Eq.refl Eq.refl

p4 : X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p4 = by-assoc-and (under (ε) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B416.proved) Eq.refl Eq.refl

p5 : CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p5 = by-assoc-and (under (ε) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B480.proved) Eq.refl Eq.refl

p6 : X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p6 = by-assoc-and (under (X0 • CX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B45.proved) Eq.refl Eq.refl

p7 : X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p7 = by-assoc-and (under (ε) (CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B161.proved) Eq.refl Eq.refl

p8 : X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p8 = by-assoc-and (under (X2 • CX02 • CX12) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B215.proved) Eq.refl Eq.refl

p9 : X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p9 = by-assoc-and (under (X2 • CX02) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B26.proved) Eq.refl Eq.refl

p10 : X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p10 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B310.proved) Eq.refl Eq.refl

p11 : X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX01 • CX12 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p11 = by-assoc-and (under (X2) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1890.proved) Eq.refl Eq.refl

p12 : X2 • CX01 • CX12 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX01 • CX10 • CCX12 • CCX01 • CX01 • X0 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p12 = by-assoc-and (under (X2 • CX01) (X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4312.proved) Eq.refl Eq.refl

p13 : X2 • CX01 • CX10 • CCX12 • CCX01 • CX01 • X0 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • X2 • CCX01 • CX01 • X0 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p13 = by-assoc-and (under (ε) (CCX01 • CX01 • X0 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B423.proved) Eq.refl Eq.refl

p14 : CX01 • CCX12 • X2 • CCX01 • CX01 • X0 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • X2 • CCX01 • X2 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p14 = by-assoc-and (under (CX01 • CCX12 • X2 • CCX01) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B221.proved) Eq.refl Eq.refl

p15 : CX01 • CCX12 • X2 • CCX01 • X2 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • X2 • X2 • CCX01 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p15 = by-assoc-and (under (CX01 • CCX12 • X2) (CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B29.proved) Eq.refl Eq.refl

p16 : CX01 • CCX12 • X2 • X2 • CCX01 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p16 = by-assoc-and (under (CX01 • CCX12) (CCX01 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4.proved) Eq.refl Eq.refl

p17 : CX01 • CCX12 • CCX01 • CX01 • X0 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p17 = by-assoc-and (under (CX01 • CCX12 • CCX01 • CX01) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p18 : CX01 • CCX12 • CCX01 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • CX12 • CX01 • X0 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p18 = by-assoc-and (under (CX01 • CCX12) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B813.proved) Eq.refl Eq.refl

p19 : CX01 • CCX12 • CX12 • CX01 • X0 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • CX12 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p19 = by-assoc-and (under (CX01 • CCX12 • CX12 • CX01) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p20 : CX01 • CCX12 • CX12 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01 • X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p20 = by-assoc-and (under (CX01 • CCX12) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B814.proved) Eq.refl Eq.refl

p21 : CX01 • CCX12 • CCX01 • CX01 • X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CCX12 • X0 • CX02 • CCX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p21 = by-assoc-and (under (CX01 • CCX12) (X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4039.proved) Eq.refl Eq.refl

p22 : CX01 • CCX12 • X0 • CX02 • CCX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • X0 • CCX12 • CX02 • CCX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p22 = by-assoc-and (under (CX01) (CX02 • CCX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B46.proved) Eq.refl Eq.refl

p23 : CX01 • X0 • CCX12 • CX02 • CCX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X1 • CCX02 • CCX12 • CX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p23 = by-assoc-and (under (ε) (CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4082.proved) Eq.refl Eq.refl

p24 : X0 • X1 • CCX02 • CCX12 • CX02 • CX12 • X1 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X1 • CCX02 • CCX12 • CX02 • CX12 • X0 • X1 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p24 = by-assoc-and (under (X0 • X1 • CCX02 • CCX12 • CX02 • CX12) (X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B44.proved) Eq.refl Eq.refl

p25 : X0 • X1 • CCX02 • CCX12 • CX02 • CX12 • X0 • X1 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X1 • CCX02 • CCX12 • CX02 • X0 • CX12 • X1 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p25 = by-assoc-and (under (X0 • X1 • CCX02 • CCX12 • CX02) (X1 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B45.proved) Eq.refl Eq.refl

p26 : X0 • X1 • CCX02 • CCX12 • CX02 • X0 • CX12 • X1 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X1 • CCX02 • CCX12 • X0 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p26 = by-assoc-and (under (X0 • X1 • CCX02 • CCX12) (X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B921.proved) Eq.refl Eq.refl

p27 : X0 • X1 • CCX02 • CCX12 • X0 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X1 • CCX02 • X0 • CCX12 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p27 = by-assoc-and (under (X0 • X1 • CCX02) (X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B46.proved) Eq.refl Eq.refl

p28 : X0 • X1 • CCX02 • X0 • CCX12 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX21 • CCX02 • CCX12 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p28 = by-assoc-and (under (ε) (CCX12 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B514.proved) Eq.refl Eq.refl

p29 : X1 • CX21 • CCX02 • CCX12 • X1 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X1 • CX20 • CCX02 • CCX12 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p29 = by-assoc-and (under (X1) (CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B874.proved) Eq.refl Eq.refl

p30 : X1 • X1 • CX20 • CCX02 • CCX12 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CCX12 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p30 = by-assoc-and (under (ε) (CX20 • CCX02 • CCX12 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3.proved) Eq.refl Eq.refl

p31 : CX20 • CCX02 • CCX12 • CX02 • CX12 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CCX12 • CX02 • X0 • CX12 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p31 = by-assoc-and (under (CX20 • CCX02 • CCX12 • CX02) (CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B45.proved) Eq.refl Eq.refl

p32 : CX20 • CCX02 • CCX12 • CX02 • X0 • CX12 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CCX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p32 = by-assoc-and (under (CX20 • CCX02 • CCX12 • CX02) (X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B121.proved) Eq.refl Eq.refl

p33 : CX20 • CCX02 • CCX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • CCX12 • X0 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p33 = by-assoc-and (under (CX20 • CCX02) (X0 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B322.proved) Eq.refl Eq.refl

p34 : CX20 • CCX02 • CX02 • CCX01 • CCX12 • X0 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • X0 • CCX12 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p34 = by-assoc-and (under (CX20 • CCX02 • CX02 • CCX01) (X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B46.proved) Eq.refl Eq.refl

p35 : CX20 • CCX02 • CX02 • CCX01 • X0 • CCX12 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • X0 • X0 • CCX12 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p35 = by-assoc-and (under (CX20 • CCX02 • CX02 • CCX01 • X0) (CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B46.proved) Eq.refl Eq.refl

p36 : CX20 • CCX02 • CX02 • CCX01 • X0 • X0 • CCX12 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p36 = by-assoc-and (under (CX20 • CCX02 • CX02 • CCX01) (CCX12 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p37 : CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CX02 • CCX12 • CX02 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p37 = by-assoc-and (under (CX20 • CCX02 • CX02) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B211.proved) Eq.refl Eq.refl

p38 : CX20 • CCX02 • CX02 • CX02 • CCX12 • CX02 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CCX12 • CX02 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p38 = by-assoc-and (under (CX20 • CCX02) (CCX12 • CX02 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B8.proved) Eq.refl Eq.refl

p39 : CX20 • CCX02 • CCX12 • CX02 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p39 = by-assoc-and (under (CX20 • CCX02) (CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B322.proved) Eq.refl Eq.refl

p40 : CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX02 • X1 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p40 = by-assoc-and (under (CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX02) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B186.proved) Eq.refl Eq.refl

p41 : CX20 • CCX02 • CX02 • CCX01 • CCX12 • CCX02 • X1 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CX02 • CCX01 • CCX12 • X1 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p41 = by-assoc-and (under (CX20 • CCX02 • CX02 • CCX01 • CCX12) (CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B28.proved) Eq.refl Eq.refl

p42 : CX20 • CCX02 • CX02 • CCX01 • CCX12 • X1 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CCX02 • CCX12 • X1 • CCX01 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p42 = by-assoc-and (under (CX20 • CCX02) (CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B657.proved) Eq.refl Eq.refl

p43 : CX20 • CCX02 • CCX12 • X1 • CCX01 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX21 • CCX02 • CCX12 • CCX01 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p43 = by-assoc-and (under (ε) (CCX01 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B774.proved) Eq.refl Eq.refl

p44 : X1 • CX21 • CCX02 • CCX12 • CCX01 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX21 • CCX01 • CCX02 • CCX12 • CCX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p44 = by-assoc-and (under (X1 • CX21) (CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B5483.proved) Eq.refl Eq.refl

p45 : X1 • CX21 • CCX01 • CCX02 • CCX12 • CCX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01 • CX21 • CCX12 • CX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p45 = by-assoc-and (under (X1) (CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B5008.proved) Eq.refl Eq.refl

p46 : X1 • CX01 • CCX01 • CX21 • CCX12 • CX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01 • CX21 • CCX12 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p46 = by-assoc-and (under (X1 • CX01 • CCX01 • CX21 • CCX12) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B8.proved) Eq.refl Eq.refl

p47 : X1 • CX01 • CCX01 • CX21 • CCX12 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01 • X1 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p47 = by-assoc-and (under (X1 • CX01 • CCX01) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B439.proved) Eq.refl Eq.refl

p48 : X1 • CX01 • CCX01 • X1 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X1 • CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p48 = by-assoc-and (under (X1) (CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B435.proved) Eq.refl Eq.refl

p49 : X1 • X1 • CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p49 = by-assoc-and (under (ε) (CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3.proved) Eq.refl Eq.refl

p50 : CCX01 • CX01 • CCX12 • CX21 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • CCX12 • X0 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p50 = by-assoc-and (under (CCX01 • CX01 • CCX12) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B20.proved) Eq.refl Eq.refl

p51 : CCX01 • CX01 • CCX12 • X0 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • X0 • CCX12 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p51 = by-assoc-and (under (CCX01 • CX01) (CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B46.proved) Eq.refl Eq.refl

p52 : CCX01 • CX01 • X0 • CCX12 • CX21 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • X0 • CX21 • CCX01 • CCX12 • X2 • CX20 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p52 = by-assoc-and (under (CCX01 • CX01 • X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B5146.proved) Eq.refl Eq.refl

p53 : CCX01 • CX01 • X0 • CX21 • CCX01 • CCX12 • X2 • CX20 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • X0 • CX21 • CCX01 • X2 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p53 = by-assoc-and (under (CCX01 • CX01 • X0 • CX21 • CCX01) (CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B566.proved) Eq.refl Eq.refl

p54 : CCX01 • CX01 • X0 • CX21 • CCX01 • X2 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • CX01 • X0 • CX21 • X2 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p54 = by-assoc-and (under (CCX01 • CX01 • X0 • CX21) (CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B29.proved) Eq.refl Eq.refl

p55 : CCX01 • CX01 • X0 • CX21 • X2 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CCX01 • X0 • X2 • CX01 • CX21 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p55 = by-assoc-and (under (CCX01) (CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B862.proved) Eq.refl Eq.refl

p56 : CCX01 • X0 • X2 • CX01 • CX21 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CCX01 • X0 • CX01 • CX21 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p56 = by-assoc-and (under (ε) (CX01 • CX21 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B223.proved) Eq.refl Eq.refl

p57 : X2 • CCX01 • X0 • CX01 • CX21 • CCX01 • CX10 • CX20 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CCX01 • X0 • CX01 • CX21 • CX20 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p57 = by-assoc-and (under (X2 • CCX01 • X0 • CX01 • CX21) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3219.proved) Eq.refl Eq.refl

p58 : X2 • CCX01 • X0 • CX01 • CX21 • CX20 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CCX01 • X0 • CX01 • CX20 • CX21 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p58 = by-assoc-and (under (X2 • CCX01 • X0 • CX01) (CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B43.proved) Eq.refl Eq.refl

p59 : X2 • CCX01 • X0 • CX01 • CX20 • CX21 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01 • CX20 • X2 • CX21 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p59 = by-assoc-and (under (ε) (CX21 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3825.proved) Eq.refl Eq.refl

p60 : X1 • CX01 • CCX01 • CX20 • X2 • CX21 • CX12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01 • CX20 • X2 • CX12 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p60 = by-assoc-and (under (X1 • CX01 • CCX01 • CX20 • X2) (CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B80.proved) Eq.refl Eq.refl

p61 : X1 • CX01 • CCX01 • CX20 • X2 • CX12 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CX10 • CCX01 • CX20 • X2 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p61 = by-assoc-and (under (X1 • CX01) (SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1186.proved) Eq.refl Eq.refl

p62 : X1 • CX01 • CX10 • CCX01 • CX20 • X2 • SWAP12 • CCX02 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CX10 • CCX01 • CX20 • X2 • CCX01 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p62 = by-assoc-and (under (X1 • CX01 • CX10 • CCX01 • CX20 • X2) (CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B108.proved) Eq.refl Eq.refl

p63 : X1 • CX01 • CX10 • CCX01 • CX20 • X2 • CCX01 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • CX10 • CX20 • CCX01 • CCX12 • X2 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p63 = by-assoc-and (under (X1 • CX01 • CX10) (SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1352.proved) Eq.refl Eq.refl

p64 : X1 • CX01 • CX10 • CX20 • CCX01 • CCX12 • X2 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CX01 • X2 • CX20 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p64 = by-assoc-and (under (X1 • CX01) (SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3939.proved) Eq.refl Eq.refl

p65 : X1 • CX01 • X2 • CX20 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX01 • CX20 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p65 = by-assoc-and (under (X1) (CX20 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B22.proved) Eq.refl Eq.refl

p66 : X1 • X2 • CX01 • CX20 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • CX20 • X2 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p66 = by-assoc-and (under (ε) (CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1231.proved) Eq.refl Eq.refl

p67 : X0 • CX01 • CX20 • X2 • CCX01 • X0 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • X2 • CX20 • CX12 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p67 = by-assoc-and (under (X0 • CX01) (CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1925.proved) Eq.refl Eq.refl

p68 : X0 • CX01 • X2 • CX20 • CX12 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CX12 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p68 = by-assoc-and (under (X0) (CX20 • CX12 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B22.proved) Eq.refl Eq.refl

p69 : X0 • X2 • CX01 • CX20 • CX12 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • CX12 • X1 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p69 = by-assoc-and (under (ε) (CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1823.proved) Eq.refl Eq.refl

p70 : CX01 • CX20 • CX12 • X1 • CCX01 • CCX12 • SWAP12 • CCX12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • CX12 • X1 • CCX01 • CCX12 • CCX12 • SWAP12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p70 = by-assoc-and (under (CX01 • CX20 • CX12 • X1 • CCX01 • CCX12) (CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B78.proved) Eq.refl Eq.refl

p71 : CX01 • CX20 • CX12 • X1 • CCX01 • CCX12 • CCX12 • SWAP12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • CX12 • X1 • CCX01 • SWAP12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p71 = by-assoc-and (under (CX01 • CX20 • CX12 • X1 • CCX01) (SWAP12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B14.proved) Eq.refl Eq.refl

p72 : CX01 • CX20 • CX12 • X1 • CCX01 • SWAP12 • CCX01 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • CX12 • X1 • CCX01 • CCX02 • SWAP12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p72 = by-assoc-and (under (CX01 • CX20 • CX12 • X1 • CCX01) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B107.proved) Eq.refl Eq.refl

p73 : CX01 • CX20 • CX12 • X1 • CCX01 • CCX02 • SWAP12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • CX12 • X1 • CCX01 • CCX02 • X0 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p73 = by-assoc-and (under (CX01 • CX20 • CX12 • X1 • CCX01 • CCX02) (CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B15.proved) Eq.refl Eq.refl

p74 : CX01 • CX20 • CX12 • X1 • CCX01 • CCX02 • X0 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX20 • X0 • CX21 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p74 = by-assoc-and (under (CX01 • CX20) (SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B3874.proved) Eq.refl Eq.refl

p75 : CX01 • CX20 • X0 • CX21 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • X0 • CX20 • CX21 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p75 = by-assoc-and (under (CX01) (CX21 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B309.proved) Eq.refl Eq.refl

p76 : CX01 • X0 • CX20 • CX21 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • CX01 • X0 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p76 = by-assoc-and (under (ε) (X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B614.proved) Eq.refl Eq.refl

p77 : CX20 • CX01 • X0 • X2 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • X2 • CX01 • X0 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p77 = by-assoc-and (under (CX20) (CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B221.proved) Eq.refl Eq.refl

p78 : CX20 • X2 • CX01 • X0 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX01 • CX21 • X2 • CX20 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p78 = by-assoc-and (under (ε) (CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1241.proved) Eq.refl Eq.refl

p79 : CX01 • CX21 • X2 • CX20 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX20 • CX01 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p79 = by-assoc-and (under (ε) (CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1630.proved) Eq.refl Eq.refl

p80 : X1 • X2 • CX20 • CX01 • CCX02 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX01 • CCX02 • CX20 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p80 = by-assoc-and (under (X1 • X2) (CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B305.proved) Eq.refl Eq.refl

p81 : X1 • X2 • CX01 • CCX02 • CX20 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CCX02 • X2 • CX20 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p81 = by-assoc-and (under (X1) (CX20 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B122.proved) Eq.refl Eq.refl

p82 : X1 • CCX02 • X2 • CX20 • CCX01 • SWAP12 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • CCX02 • X2 • CX20 • CCX01 • CCX02 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p82 = by-assoc-and (under (X1 • CCX02 • X2 • CX20 • CCX01) (X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B107.proved) Eq.refl Eq.refl

p83 : X1 • CCX02 • X2 • CX20 • CCX01 • CCX02 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX01 • CX20 • CCX01 • CX21 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p83 = by-assoc-and (under (X1) (SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4012.proved) Eq.refl Eq.refl

p84 : X1 • X2 • CX01 • CX20 • CCX01 • CX21 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • CX20 • X2 • CCX01 • CX21 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p84 = by-assoc-and (under (ε) (CCX01 • CX21 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1231.proved) Eq.refl Eq.refl

p85 : X0 • CX01 • CX20 • X2 • CCX01 • CX21 • SWAP12 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • CX20 • X2 • CCX01 • CX12 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p85 = by-assoc-and (under (X0 • CX01 • CX20 • X2 • CCX01) (X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B41.proved) Eq.refl Eq.refl

p86 : X0 • CX01 • CX20 • X2 • CCX01 • CX12 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • CX20 • X2 • CX12 • CCX01 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p86 = by-assoc-and (under (X0 • CX01 • CX20 • X2) (CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B31.proved) Eq.refl Eq.refl

p87 : X0 • CX01 • CX20 • X2 • CX12 • CCX01 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX01 • X2 • CX20 • CCX01 • X0 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p87 = by-assoc-and (under (X0 • CX01) (CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B2217.proved) Eq.refl Eq.refl

p88 : X0 • CX01 • X2 • CX20 • CCX01 • X0 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CCX01 • X0 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p88 = by-assoc-and (under (X0) (CX20 • CCX01 • X0 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B22.proved) Eq.refl Eq.refl

p89 : X0 • X2 • CX01 • CX20 • CCX01 • X0 • CX21 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CCX01 • X0 • CX21 • X0 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p89 = by-assoc-and (under (X0 • X2 • CX01 • CX20 • CCX01 • X0 • CX21) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B18.proved) Eq.refl Eq.refl

p90 : X0 • X2 • CX01 • CX20 • CCX01 • X0 • CX21 • X0 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CCX01 • X0 • X0 • CX21 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p90 = by-assoc-and (under (X0 • X2 • CX01 • CX20 • CCX01 • X0) (X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B20.proved) Eq.refl Eq.refl

p91 : X0 • X2 • CX01 • CX20 • CCX01 • X0 • X0 • CX21 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CCX01 • CX21 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p91 = by-assoc-and (under (X0 • X2 • CX01 • CX20 • CCX01) (CX21 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p92 : X0 • X2 • CX01 • CX20 • CCX01 • CX21 • X2 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX01 • CX20 • CX21 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p92 = by-assoc-and (under (X0 • X2 • CX01 • CX20) (CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B1353.proved) Eq.refl Eq.refl

p93 : X0 • X2 • CX01 • CX20 • CX21 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ X0 • X2 • CX20 • CX01 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p93 = by-assoc-and (under (X0 • X2) (CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B303.proved) Eq.refl Eq.refl

p94 : X0 • X2 • CX20 • CX01 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20 • X2 • CX01 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p94 = by-assoc-and (under (ε) (CX01 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B316.proved) Eq.refl Eq.refl

p95 : CX20 • X2 • CX01 • CCX01 • CCX02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p95 = by-assoc-and (under (ε) (X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B4337.proved) Eq.refl Eq.refl

p96 : CX02 • CCX12 • CCX02 • X0 • SWAP02 • X2 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • CCX02 • X0 • X0 • SWAP02 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p96 = by-assoc-and (under (CX02 • CCX12 • CCX02 • X0) (CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B93.proved) Eq.refl Eq.refl

p97 : CX02 • CCX12 • CCX02 • X0 • X0 • SWAP02 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • CCX02 • SWAP02 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
p97 = by-assoc-and (under (CX02 • CCX12 • CCX02) (SWAP02 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p98 : CX02 • CCX12 • CCX02 • SWAP02 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • CCX02 • CCX02 • SWAP02 • CCX01 • X1 • CCX01 • X1 • CCX01
p98 = by-assoc-and (under (CX02 • CCX12 • CCX02) (CCX01 • X1 • CCX01 • X1 • CCX01) B76.proved) Eq.refl Eq.refl

p99 : CX02 • CCX12 • CCX02 • CCX02 • SWAP02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • SWAP02 • CCX01 • X1 • CCX01 • X1 • CCX01
p99 = by-assoc-and (under (CX02 • CCX12) (SWAP02 • CCX01 • X1 • CCX01 • X1 • CCX01) B10.proved) Eq.refl Eq.refl

p100 : CX02 • CCX12 • SWAP02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX12 • CCX12 • SWAP02 • X1 • CCX01 • X1 • CCX01
p100 = by-assoc-and (under (CX02 • CCX12) (X1 • CCX01 • X1 • CCX01) B104.proved) Eq.refl Eq.refl

p101 : CX02 • CCX12 • CCX12 • SWAP02 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • SWAP02 • X1 • CCX01 • X1 • CCX01
p101 = by-assoc-and (under (CX02) (SWAP02 • X1 • CCX01 • X1 • CCX01) B14.proved) Eq.refl Eq.refl

p102 : CX02 • SWAP02 • X1 • CCX01 • X1 • CCX01 ≈ CX02 • X1 • SWAP02 • CCX01 • X1 • CCX01
p102 = by-assoc-and (under (CX02) (CCX01 • X1 • CCX01) B17.proved) Eq.refl Eq.refl

p103 : CX02 • X1 • SWAP02 • CCX01 • X1 • CCX01 ≈ X1 • CX02 • SWAP02 • CCX01 • X1 • CCX01
p103 = by-assoc-and (under (ε) (SWAP02 • CCX01 • X1 • CCX01) B23.proved) Eq.refl Eq.refl

p104 : X1 • CX02 • SWAP02 • CCX01 • X1 • CCX01 ≈ X1 • CX02 • CCX12 • SWAP02 • X1 • CCX01
p104 = by-assoc-and (under (X1 • CX02) (X1 • CCX01) B104.proved) Eq.refl Eq.refl

p105 : X1 • CX02 • CCX12 • SWAP02 • X1 • CCX01 ≈ CX20 • CCX01 • X1 • X1 • CCX01
p105 = by-assoc-and (under (ε) (X1 • CCX01) B476.proved) Eq.refl Eq.refl

p106 : CX20 • CCX01 • X1 • X1 • CCX01 ≈ CX20 • CCX01 • CCX01
p106 = by-assoc-and (under (CX20 • CCX01) (CCX01) B3.proved) Eq.refl Eq.refl

p107 : CX20 • CCX01 • CCX01 ≈ CX20
p107 = by-assoc-and (under (CX20) (ε) B11.proved) Eq.refl Eq.refl

p108 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 ≈ CX20
p108 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (trans p52 (trans p53 (trans p54 (trans p55 (trans p56 (trans p57 (trans p58 (trans p59 (trans p60 (trans p61 (trans p62 (trans p63 (trans p64 (trans p65 (trans p66 (trans p67 (trans p68 (trans p69 (trans p70 (trans p71 (trans p72 (trans p73 (trans p74 (trans p75 (trans p76 (trans p77 (trans p78 (trans p79 (trans p80 (trans p81 (trans p82 (trans p83 (trans p84 (trans p85 (trans p86 (trans p87 (trans p88 (trans p89 (trans p90 (trans p91 (trans p92 (trans p93 (trans p94 (trans p95 (trans p96 (trans p97 (trans p98 (trans p99 (trans p100 (trans p101 (trans p102 (trans p103 (trans p104 (trans p105 (trans p106 (trans p107 (refl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

proved : CX20 ≈ X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01
proved = trans p0 (sym p108)
