{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm03 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0229 as B229
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0442 as B442
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0605 as B605
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0835 as B835
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0884 as B884
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0916 as B916
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 as B1658
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2234 as B2234
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 as B3094
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3112 as B3112

p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p1 = by-assoc-and (under (X0 • CX02 • CCX01) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p2 = by-assoc-and (under (X0 • CX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B29.proved) Eq.refl Eq.refl

p3 : X0 • CX02 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CX02 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p3 = by-assoc-and (under (X0) (CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B33.proved) Eq.refl Eq.refl

p4 : X0 • X2 • CX02 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • X0 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p4 = by-assoc-and (under (ε) (CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B125.proved) Eq.refl Eq.refl

p5 : CX02 • X0 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p5 = by-assoc-and (under (CX02 • X0) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B11.proved) Eq.refl Eq.refl

p6 : CX02 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p6 = by-assoc-and (under (CX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p7 : CX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p7 = by-assoc-and (under (CX02) (X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p8 : CX02 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p8 = by-assoc-and (under (CX02) (X0 • CCX01 • X2 • X0) B219.proved) Eq.refl Eq.refl

p9 : CX02 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p9 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) B25.proved) Eq.refl Eq.refl

p10 : CX01 • CX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CCX01 • X0
p10 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • X0) (X0) B29.proved) Eq.refl Eq.refl

p11 : CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CCX01 • X0
p11 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0) B221.proved) Eq.refl Eq.refl

p12 : CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • CX12 • CCX01
p12 = by-assoc-and (under (CX01 • CX02 • CCX12 • X2 • CX01) (ε) B153.proved) Eq.refl Eq.refl

p13 : CX01 • CX02 • CCX12 • X2 • CX01 • CX12 • CCX01 ≈ CX01 • CX02 • X2 • CX12 • CCX12 • CCX01 • CX01
p13 = by-assoc-and (under (CX01 • CX02) (ε) B3112.proved) Eq.refl Eq.refl

p14 : CX01 • CX02 • X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01
p14 = by-assoc-and (under (CX01) (CX12 • CCX12 • CCX01 • CX01) B33.proved) Eq.refl Eq.refl

p15 : CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01
p15 = by-assoc-and (under (ε) (CX02 • CX12 • CCX12 • CCX01 • CX01) B22.proved) Eq.refl Eq.refl

p16 : X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
p16 = by-assoc-and (under (X2) (CCX12 • CCX01 • CX01) B164.proved) Eq.refl Eq.refl

p17 : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
p17 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (refl)))))))))))))))))

p18 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
p18 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) B481.proved) Eq.refl Eq.refl

p19 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
p19 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) B215.proved) Eq.refl Eq.refl

p20 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
p20 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) B118.proved) Eq.refl Eq.refl

p21 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
p21 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) B47.proved) Eq.refl Eq.refl

p22 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
p22 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • X1 • CCX01 • X1 • X0) B3094.proved) Eq.refl Eq.refl

p23 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0
p23 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • X1 • CCX01 • X1 • X0) B36.proved) Eq.refl Eq.refl

p24 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0
p24 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • X1 • CCX01 • X1 • X0) B21.proved) Eq.refl Eq.refl

p25 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0
p25 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10) (X0 • X1 • CCX01 • X1 • X0) B45.proved) Eq.refl Eq.refl

p26 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
p26 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (CX12 • X0 • X1 • CCX01 • X1 • X0) B47.proved) Eq.refl Eq.refl

p27 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
p27 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) B18.proved) Eq.refl Eq.refl

p28 : X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
p28 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) B12.proved) Eq.refl Eq.refl

p29 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
p29 = by-assoc-and (under (ε) (CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) B2234.proved) Eq.refl Eq.refl

p30 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0
p30 = by-assoc-and (under (CX02) (CX12 • X0 • X1 • CCX01 • X1 • X0) B1658.proved) Eq.refl Eq.refl

p31 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0
p31 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0) B25.proved) Eq.refl Eq.refl

p32 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • X1 • CCX01 • X1 • X0
p32 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • X1 • CCX01 • X1 • X0) B163.proved) Eq.refl Eq.refl

p33 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X1 • CX02 • X0 • CCX01 • X1 • X0
p33 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01) (CCX01 • X1 • X0) B229.proved) Eq.refl Eq.refl

p34 : CX01 • CX02 • CCX12 • CX01 • X1 • CX02 • X0 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • X1 • CX01 • CX02 • X0 • CCX01 • X1 • X0
p34 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX02 • X0 • CCX01 • X1 • X0) B35.proved) Eq.refl Eq.refl

p35 : CX01 • CX02 • CCX12 • X1 • CX01 • CX02 • X0 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX02 • X0 • CX01 • CCX01 • X1 • X0
p35 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X1 • X0) B442.proved) Eq.refl Eq.refl

p36 : CX01 • CX02 • CCX12 • CX02 • X0 • CX01 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • X0 • X2 • CCX01 • CX01 • X1 • X0
p36 = by-assoc-and (under (CX01 • CX02 • CCX12) (X1 • X0) B835.proved) Eq.refl Eq.refl

p37 : CX01 • CX02 • CCX12 • X0 • X2 • CCX01 • CX01 • X1 • X0 ≈ CX01 • CX02 • X0 • CCX12 • X2 • CCX01 • CX01 • X1 • X0
p37 = by-assoc-and (under (CX01 • CX02) (X2 • CCX01 • CX01 • X1 • X0) B46.proved) Eq.refl Eq.refl

p38 : CX01 • CX02 • X0 • CCX12 • X2 • CCX01 • CX01 • X1 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • CX01 • X1 • X0
p38 = by-assoc-and (under (CX01) (CCX01 • CX01 • X1 • X0) B916.proved) Eq.refl Eq.refl

p39 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • CX01 • X1 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X1 • CX01 • X0
p39 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX01) (X0) B35.proved) Eq.refl Eq.refl

p40 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X1 • CX01 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CX01 • CCX01 • X0
p40 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (X0) B282.proved) Eq.refl Eq.refl

p41 : CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CX01 • CCX01 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X0 • CX01
p41 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (ε) B605.proved) Eq.refl Eq.refl

p42 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X0 • CX01 ≈ CX01 • X0 • CX02 • X0 • CX12 • CCX12 • CCX01 • CX01
p42 = by-assoc-and (under (CX01 • X0 • CX02) (CX01) B884.proved) Eq.refl Eq.refl

p43 : CX01 • X0 • CX02 • X0 • CX12 • CCX12 • CCX01 • CX01 ≈ CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01
p43 = by-assoc-and (under (CX01) (CX12 • CCX12 • CCX01 • CX01) B161.proved) Eq.refl Eq.refl

p44 : CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01
p44 = by-assoc-and (under (ε) (CX02 • CX12 • CCX12 • CCX01 • CX01) B22.proved) Eq.refl Eq.refl

p45 : X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
p45 = by-assoc-and (under (X2) (CCX12 • CCX01 • CX01) B164.proved) Eq.refl Eq.refl

p46 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
p46 = trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (refl))))))))))))))))))))))))))))

proved : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
proved = trans p17 (sym p46)
