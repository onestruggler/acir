{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm13 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0225 as B225
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0355 as B355
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 as B357
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 as B366
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0862 as B862
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1209 as B1209
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1366 as B1366
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 as B1658
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 as B1661
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2829 as B2829
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 as B3094
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3123 as B3123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3579 as B3579
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3965 as B3965
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4079 as B4079
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB4332 as B4332
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5458 as B5458

p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B214.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p2 = by-assoc-and (under (ε) (CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B515.proved) Eq.refl Eq.refl

p3 : CX12 • CX21 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • X0 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p4 = by-assoc-and (under (CX12) (CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B129.proved) Eq.refl Eq.refl

p5 : CX12 • X0 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p5 = by-assoc-and (under (ε) (CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p6 : X0 • CX12 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p6 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p7 : X0 • CX12 • CCX02 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CX12 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p7 = by-assoc-and (under (X0 • CX12) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B1209.proved) Eq.refl Eq.refl

p8 : X0 • CX12 • CX12 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p8 = by-assoc-and (under (X0) (CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B6.proved) Eq.refl Eq.refl

p9 : X0 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CCX02 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p9 = by-assoc-and (under (X0 • CCX01 • CCX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p10 : X0 • CCX01 • CCX02 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • X0 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
p10 = by-assoc-and (under (X0 • CCX01) (CCX12 • X0 • CCX01 • X2 • X0) B4079.proved) Eq.refl Eq.refl

p11 : X0 • CCX01 • X0 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX01 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
p11 = by-assoc-and (under (ε) (CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0) B153.proved) Eq.refl Eq.refl

p12 : CX12 • CCX01 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX21 • X2 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
p12 = by-assoc-and (under (ε) (CX01 • CCX12 • X0 • CCX01 • X2 • X0) B3123.proved) Eq.refl Eq.refl

p13 : CX10 • CCX01 • CCX12 • CX21 • X2 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • CCX12 • X0 • CCX01 • X2 • X0
p13 = by-assoc-and (under (CX10 • CCX01 • CCX12) (CCX12 • X0 • CCX01 • X2 • X0) B225.proved) Eq.refl Eq.refl

p14 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • X0 • CCX12 • CCX01 • X2 • X0
p14 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01 • CX21 • X2) (CCX01 • X2 • X0) B46.proved) Eq.refl Eq.refl

p15 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • X0 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X0 • X2 • CCX12 • CCX01 • X2 • X0
p15 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01 • CX21) (CCX12 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p16 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X0 • X2 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • X0 • CX21 • X2 • CCX12 • CCX01 • X2 • X0
p16 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01) (X2 • CCX12 • CCX01 • X2 • X0) B20.proved) Eq.refl Eq.refl

p17 : CX10 • CCX01 • CCX12 • CX01 • X0 • CX21 • X2 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • X0 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
p17 = by-assoc-and (under (CX10 • CCX01 • CCX12) (CCX12 • CCX01 • X2 • X0) B862.proved) Eq.refl Eq.refl

p18 : CX10 • CCX01 • CCX12 • X0 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • X0 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
p18 = by-assoc-and (under (CX10 • CCX01) (X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) B46.proved) Eq.refl Eq.refl

p19 : CX10 • CCX01 • X0 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CX10 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
p19 = by-assoc-and (under (ε) (CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) B366.proved) Eq.refl Eq.refl

p20 : X0 • CCX01 • CX10 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • CCX01 • X2 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
p20 = by-assoc-and (under (X0 • CCX01) (CX01 • CX21 • CCX12 • CCX01 • X2 • X0) B131.proved) Eq.refl Eq.refl

p21 : X0 • CCX01 • X2 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
p21 = by-assoc-and (under (X0) (CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) B29.proved) Eq.refl Eq.refl

p22 : X0 • X2 • CCX01 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • CCX01 • X2 • X0
p22 = by-assoc-and (under (X0 • X2 • CCX01) (CCX01 • X2 • X0) B1366.proved) Eq.refl Eq.refl

p23 : X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
p23 = by-assoc-and (under (X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02) (X0) B29.proved) Eq.refl Eq.refl

p24 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
p24 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (refl))))))))))))))))))))))))

p25 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p25 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B481.proved) Eq.refl Eq.refl

p26 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p26 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B215.proved) Eq.refl Eq.refl

p27 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p27 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B118.proved) Eq.refl Eq.refl

p28 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p28 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B47.proved) Eq.refl Eq.refl

p29 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p29 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B3094.proved) Eq.refl Eq.refl

p30 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p30 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B36.proved) Eq.refl Eq.refl

p31 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p31 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B21.proved) Eq.refl Eq.refl

p32 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p32 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B3579.proved) Eq.refl Eq.refl

p33 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p33 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B357.proved) Eq.refl Eq.refl

p34 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
p34 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (X0 • CCX01 • CCX02 • CCX01 • X0) B44.proved) Eq.refl Eq.refl

p35 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
p35 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p36 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
p36 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0) B47.proved) Eq.refl Eq.refl

p37 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
p37 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0) B355.proved) Eq.refl Eq.refl

p38 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
p38 = by-assoc-and (under (CX10) (CX10 • X0 • CCX01 • CCX02 • CCX01 • X0) B2829.proved) Eq.refl Eq.refl

p39 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
p39 = by-assoc-and (under (ε) (CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0) B1661.proved) Eq.refl Eq.refl

p40 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p40 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (X0 • CCX01 • CCX02 • CCX01 • X0) B26.proved) Eq.refl Eq.refl

p41 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p41 = by-assoc-and (under (CX02) (CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) B1658.proved) Eq.refl Eq.refl

p42 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p42 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) B25.proved) Eq.refl Eq.refl

p43 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X0
p43 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • CCX01 • CCX02 • CCX01 • X0) B163.proved) Eq.refl Eq.refl

p44 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X0 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0
p44 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0) B5458.proved) Eq.refl Eq.refl

p45 : CX01 • CX02 • CCX12 • X0 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0 ≈ CX01 • CX02 • X0 • CCX12 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0
p45 = by-assoc-and (under (CX01 • CX02) (X1 • CCX01 • CCX02 • X2 • CCX01 • X0) B46.proved) Eq.refl Eq.refl

p46 : CX01 • CX02 • X0 • CCX12 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0 ≈ CX01 • X0 • X2 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0
p46 = by-assoc-and (under (CX01) (CCX02 • X2 • CCX01 • X0) B3965.proved) Eq.refl Eq.refl

p47 : CX01 • X0 • X2 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0 ≈ X2 • CX01 • X0 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0
p47 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0) B221.proved) Eq.refl Eq.refl

p48 : X2 • CX01 • X0 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0 ≈ X2 • X0 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
p48 = by-assoc-and (under (X2) (CCX02 • X2 • CCX01 • X0) B4332.proved) Eq.refl Eq.refl

p49 : X2 • X0 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
p49 = by-assoc-and (under (ε) (CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0) B18.proved) Eq.refl Eq.refl

p50 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
p50 = trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (refl)))))))))))))))))))))))))

proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
proved = trans p24 (sym p50)
