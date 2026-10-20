{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeSWAP01 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; SWAP01 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0016 as B16
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0074 as B74
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0091 as B91
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0097 as B97
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0355 as B355
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 as B357
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0412 as B412
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0493 as B493
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0777 as B777
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0783 as B783
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0910 as B910
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1419 as B1419
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 as B1658
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 as B1661
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2681 as B2681
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2682 as B2682
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2829 as B2829
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 as B3094
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3098 as B3098
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3579 as B3579

p0 : SWAP01 ≈ SWAP01
p0 = refl

p1 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B481.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p2 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p3 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p3 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B118.proved) Eq.refl Eq.refl

p4 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p5 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B3094.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p6 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p7 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p7 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B21.proved) Eq.refl Eq.refl

p8 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p8 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B3579.proved) Eq.refl Eq.refl

p9 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p9 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B357.proved) Eq.refl Eq.refl

p10 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p10 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B44.proved) Eq.refl Eq.refl

p11 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p11 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p12 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p12 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p13 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p13 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B355.proved) Eq.refl Eq.refl

p14 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p14 = by-assoc-and (under (CX10) (CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B2829.proved) Eq.refl Eq.refl

p15 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p15 = by-assoc-and (under (ε) (CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B1661.proved) Eq.refl Eq.refl

p16 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p16 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B26.proved) Eq.refl Eq.refl

p17 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p17 = by-assoc-and (under (CX02) (CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B1658.proved) Eq.refl Eq.refl

p18 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p18 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B25.proved) Eq.refl Eq.refl

p19 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p19 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B163.proved) Eq.refl Eq.refl

p20 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p20 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • CX02) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B153.proved) Eq.refl Eq.refl

p21 : CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p21 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B164.proved) Eq.refl Eq.refl

p22 : CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CCX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p22 = by-assoc-and (under (CX01) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B2682.proved) Eq.refl Eq.refl

p23 : CX01 • CX10 • CCX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CCX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p23 = by-assoc-and (under (CX01 • CX10 • CCX01 • CCX12) (CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B35.proved) Eq.refl Eq.refl

p24 : CX01 • CX10 • CCX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CX02 • CCX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p24 = by-assoc-and (under (CX01 • CX10) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B3098.proved) Eq.refl Eq.refl

p25 : CX01 • CX10 • CX02 • CCX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p25 = by-assoc-and (under (CX01) (X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B315.proved) Eq.refl Eq.refl

p26 : CX01 • CX02 • CCX12 • CX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX12 • X1 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p26 = by-assoc-and (under (CX01 • CX02 • CCX12) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B412.proved) Eq.refl Eq.refl

p27 : CX01 • CX02 • CCX12 • CX01 • CX12 • X1 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p27 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • CX12) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B3.proved) Eq.refl Eq.refl

p28 : CX01 • CX02 • CCX12 • CX01 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p28 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p29 : CX01 • CX02 • CCX12 • CX01 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p29 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • X0) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p30 : CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p30 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B221.proved) Eq.refl Eq.refl

p31 : CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X0 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p31 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B910.proved) Eq.refl Eq.refl

p32 : CX01 • CX02 • CCX12 • X0 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • X0 • CCX12 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p32 = by-assoc-and (under (CX01 • CX02) (CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B46.proved) Eq.refl Eq.refl

p33 : CX01 • CX02 • X0 • CCX12 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • X0 • CCX12 • CX01 • X0 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p33 = by-assoc-and (under (CX01 • CX02 • X0 • CCX12 • CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B783.proved) Eq.refl Eq.refl

p34 : CX01 • CX02 • X0 • CCX12 • CX01 • X0 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X1 • CX01 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p34 = by-assoc-and (under (CX01 • CX02) (X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B493.proved) Eq.refl Eq.refl

p35 : CX01 • CX02 • CCX12 • X1 • CX01 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X1 • X1 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p35 = by-assoc-and (under (CX01 • CX02 • CCX12 • X1) (X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B35.proved) Eq.refl Eq.refl

p36 : CX01 • CX02 • CCX12 • X1 • X1 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p36 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B3.proved) Eq.refl Eq.refl

p37 : CX01 • CX02 • CCX12 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p37 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B22.proved) Eq.refl Eq.refl

p38 : CX01 • CX02 • CCX12 • X2 • CX01 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p38 = by-assoc-and (under (CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B2681.proved) Eq.refl Eq.refl

p39 : CX01 • CCX01 • CCX12 • X2 • CX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX02 • X2 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0
p39 = by-assoc-and (under (CX01 • CCX01) (CCX12 • X0 • CCX01 • X2 • X0) B1419.proved) Eq.refl Eq.refl

p40 : CX01 • CCX01 • CCX02 • X2 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • CCX02 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0
p40 = by-assoc-and (under (ε) (SWAP01 • CCX12 • X0 • CCX01 • X2 • X0) B777.proved) Eq.refl Eq.refl

p41 : X2 • CX02 • CCX01 • CCX02 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • CCX02 • CCX02 • SWAP01 • X0 • CCX01 • X2 • X0
p41 = by-assoc-and (under (X2 • CX02 • CCX01 • CCX02) (X0 • CCX01 • X2 • X0) B91.proved) Eq.refl Eq.refl

p42 : X2 • CX02 • CCX01 • CCX02 • CCX02 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • SWAP01 • X0 • CCX01 • X2 • X0
p42 = by-assoc-and (under (X2 • CX02 • CCX01) (SWAP01 • X0 • CCX01 • X2 • X0) B10.proved) Eq.refl Eq.refl

p43 : X2 • CX02 • CCX01 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • X1 • SWAP01 • CCX01 • X2 • X0
p43 = by-assoc-and (under (X2 • CX02 • CCX01) (CCX01 • X2 • X0) B97.proved) Eq.refl Eq.refl

p44 : X2 • CX02 • CCX01 • X1 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • X1 • CCX01 • SWAP01 • CCX01 • X2 • X0
p44 = by-assoc-and (under (X2) (SWAP01 • CCX01 • X2 • X0) B120.proved) Eq.refl Eq.refl

p45 : X2 • X1 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X1 • X2 • CCX01 • SWAP01 • CCX01 • X2 • X0
p45 = by-assoc-and (under (ε) (CCX01 • SWAP01 • CCX01 • X2 • X0) B19.proved) Eq.refl Eq.refl

p46 : X1 • X2 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X1 • X2 • CCX01 • CCX01 • SWAP01 • X2 • X0
p46 = by-assoc-and (under (X1 • X2 • CCX01) (X2 • X0) B74.proved) Eq.refl Eq.refl

p47 : X1 • X2 • CCX01 • CCX01 • SWAP01 • X2 • X0 ≈ X1 • X2 • SWAP01 • X2 • X0
p47 = by-assoc-and (under (X1 • X2) (SWAP01 • X2 • X0) B11.proved) Eq.refl Eq.refl

p48 : X1 • X2 • SWAP01 • X2 • X0 ≈ X1 • X2 • X2 • SWAP01 • X0
p48 = by-assoc-and (under (X1 • X2) (X0) B16.proved) Eq.refl Eq.refl

p49 : X1 • X2 • X2 • SWAP01 • X0 ≈ X1 • SWAP01 • X0
p49 = by-assoc-and (under (X1) (SWAP01 • X0) B4.proved) Eq.refl Eq.refl

p50 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
p50 = by-assoc-and (under (X1) (ε) B97.proved) Eq.refl Eq.refl

p51 : X1 • X1 • SWAP01 ≈ SWAP01
p51 = by-assoc-and (under (ε) (SWAP01) B3.proved) Eq.refl Eq.refl

p52 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ SWAP01
p52 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (refl)))))))))))))))))))))))))))))))))))))))))))))))))))

proved : SWAP01 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
proved = trans p0 (sym p52)
