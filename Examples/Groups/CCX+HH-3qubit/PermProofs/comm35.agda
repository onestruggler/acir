{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm35 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0015 as B15
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 as B163
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 as B285
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0341 as B341
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0355 as B355
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0357 as B357
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0383 as B383
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0901 as B901
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0904 as B904
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 as B1658
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1661 as B1661
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1720 as B1720
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1871 as B1871
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2230 as B2230
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2829 as B2829
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2897 as B2897
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 as B3094
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3229 as B3229
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3579 as B3579
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3873 as B3873
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5021 as B5021
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5198 as B5198
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB5514 as B5514

p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B481.proved) Eq.refl Eq.refl

p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B215.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B118.proved) Eq.refl Eq.refl

p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) B47.proved) Eq.refl Eq.refl

p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • CCX01 • CCX02 • CCX01
p4 = by-assoc-and (under (X2 • CX10) (X2 • X0 • CCX01 • CCX02 • CCX01) B3094.proved) Eq.refl Eq.refl

p5 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • CCX01 • CCX02 • CCX01
p5 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • CCX01 • CCX02 • CCX01) B36.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01
p6 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • CCX01 • CCX02 • CCX01) B21.proved) Eq.refl Eq.refl

p7 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01
p7 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • CCX01 • CCX02 • CCX01) B3579.proved) Eq.refl Eq.refl

p8 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01
p8 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01) B357.proved) Eq.refl Eq.refl

p9 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • CCX01 • CCX02 • CCX01
p9 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (CCX01 • CCX02 • CCX01) B44.proved) Eq.refl Eq.refl

p10 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • CCX01 • CCX02 • CCX01
p10 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • CCX01 • CCX02 • CCX01) B45.proved) Eq.refl Eq.refl

p11 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • CCX01 • CCX02 • CCX01
p11 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • CCX01 • CCX02 • CCX01) B47.proved) Eq.refl Eq.refl

p12 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • CCX01 • CCX02 • CCX01
p12 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) B355.proved) Eq.refl Eq.refl

p13 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01
p13 = by-assoc-and (under (CX10) (CX10 • CCX01 • CCX02 • CCX01) B2829.proved) Eq.refl Eq.refl

p14 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01
p14 = by-assoc-and (under (ε) (CX12 • CX10 • CCX01 • CCX02 • CCX01) B1661.proved) Eq.refl Eq.refl

p15 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • CCX01 • CCX02 • CCX01
p15 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (CCX01 • CCX02 • CCX01) B26.proved) Eq.refl Eq.refl

p16 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01
p16 = by-assoc-and (under (CX02) (CX12 • CCX01 • CCX02 • CCX01) B1658.proved) Eq.refl Eq.refl

p17 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01
p17 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01) B25.proved) Eq.refl Eq.refl

p18 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • CCX01 • CCX02 • CCX01
p18 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • CCX02 • CCX01) B163.proved) Eq.refl Eq.refl

p19 : CX01 • CX02 • CCX12 • CX01 • CX02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CCX01
p19 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX02 • CCX01) B123.proved) Eq.refl Eq.refl

p20 : CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CCX02 • CX02 • CCX01
p20 = by-assoc-and (under (CX01) (CCX01) B2897.proved) Eq.refl Eq.refl

p21 : CX01 • CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CX01 • CCX12 • CX01 • CX02 • CCX12
p21 = by-assoc-and (under (CX01) (ε) B5514.proved) Eq.refl Eq.refl

p22 : CX01 • CX01 • CCX12 • CX01 • CX02 • CCX12 ≈ CCX12 • CX01 • CX02 • CCX12
p22 = by-assoc-and (under (ε) (CCX12 • CX01 • CX02 • CCX12) B13.proved) Eq.refl Eq.refl

p23 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX12 • CX01 • CX02 • CCX12
p23 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (refl)))))))))))))))))))))))

p24 : CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p24 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B214.proved) Eq.refl Eq.refl

p25 : CX12 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p25 = by-assoc-and (under (CX12 • CCX02) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p26 : CX12 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p26 = by-assoc-and (under (CX12 • CCX02 • X0) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p27 : CX12 • CCX02 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p27 = by-assoc-and (under (CX12 • CCX02) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B383.proved) Eq.refl Eq.refl

p28 : CX12 • CCX02 • X2 • CCX01 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p28 = by-assoc-and (under (ε) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B5021.proved) Eq.refl Eq.refl

p29 : X0 • CCX02 • CCX01 • X1 • SWAP12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X1 • X0 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p29 = by-assoc-and (under (X0 • CCX02 • CCX01 • X1) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B15.proved) Eq.refl Eq.refl

p30 : X0 • CCX02 • CCX01 • X1 • X0 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X0 • X1 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p30 = by-assoc-and (under (X0 • CCX02 • CCX01) (SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B44.proved) Eq.refl Eq.refl

p31 : X0 • CCX02 • CCX01 • X0 • X1 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X0 • CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p31 = by-assoc-and (under (X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B5198.proved) Eq.refl Eq.refl

p32 : X0 • X0 • CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p32 = by-assoc-and (under (ε) (CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p33 : CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
p33 = by-assoc-and (under (CX12 • CCX02 • X2 • CCX01) (X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p34 : CX12 • CCX02 • X2 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p34 = by-assoc-and (under (CX12 • CCX02 • X2 • CCX01) (X0 • CCX01 • X2 • X0) B219.proved) Eq.refl Eq.refl

p35 : CX12 • CCX02 • X2 • CCX01 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX12 • X2 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p35 = by-assoc-and (under (CX12) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) B901.proved) Eq.refl Eq.refl

p36 : CX12 • X2 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p36 = by-assoc-and (under (ε) (CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p37 : X2 • CX12 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX12 • CCX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p37 = by-assoc-and (under (X2) (CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0) B285.proved) Eq.refl Eq.refl

p38 : X2 • CX01 • CX12 • CCX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CCX02 • X2 • CX12 • CCX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
p38 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) B1720.proved) Eq.refl Eq.refl

p39 : CCX02 • X2 • CX12 • CCX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CCX02 • X2 • CX12 • CX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0
p39 = by-assoc-and (under (CCX02 • X2 • CX12) (X0 • CCX01 • X2 • X0) B341.proved) Eq.refl Eq.refl

p40 : CCX02 • X2 • CX12 • CX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 ≈ X2 • CCX02 • CX02 • CX12 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0
p40 = by-assoc-and (under (ε) (CCX12 • CCX02 • X0 • CCX01 • X2 • X0) B904.proved) Eq.refl Eq.refl

p41 : X2 • CCX02 • CX02 • CX12 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 ≈ X2 • CCX02 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X0 • X2 • X0
p41 = by-assoc-and (under (X2 • CCX02 • CX02) (X2 • X0) B3873.proved) Eq.refl Eq.refl

p42 : X2 • CCX02 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X0 • X2 • X0 ≈ CX02 • CCX02 • CCX12 • X2 • CCX01 • CCX02 • X0 • X2 • X0
p42 = by-assoc-and (under (ε) (CCX01 • CCX02 • X0 • X2 • X0) B1871.proved) Eq.refl Eq.refl

p43 : CX02 • CCX02 • CCX12 • X2 • CCX01 • CCX02 • X0 • X2 • X0 ≈ CX02 • CCX02 • CCX12 • CCX01 • CX01 • CCX02 • X0 • X0
p43 = by-assoc-and (under (CX02 • CCX02 • CCX12) (X0) B2230.proved) Eq.refl Eq.refl

p44 : CX02 • CCX02 • CCX12 • CCX01 • CX01 • CCX02 • X0 • X0 ≈ CX02 • CX02 • CCX12 • CX01 • CX02 • CCX12 • X0 • X0
p44 = by-assoc-and (under (CX02) (X0 • X0) B3229.proved) Eq.refl Eq.refl

p45 : CX02 • CX02 • CCX12 • CX01 • CX02 • CCX12 • X0 • X0 ≈ CCX12 • CX01 • CX02 • CCX12 • X0 • X0
p45 = by-assoc-and (under (ε) (CCX12 • CX01 • CX02 • CCX12 • X0 • X0) B8.proved) Eq.refl Eq.refl

p46 : CCX12 • CX01 • CX02 • CCX12 • X0 • X0 ≈ CCX12 • CX01 • CX02 • X0 • CCX12 • X0
p46 = by-assoc-and (under (CCX12 • CX01 • CX02) (X0) B46.proved) Eq.refl Eq.refl

p47 : CCX12 • CX01 • CX02 • X0 • CCX12 • X0 ≈ CCX12 • CX01 • CX02 • X0 • X0 • CCX12
p47 = by-assoc-and (under (CCX12 • CX01 • CX02 • X0) (ε) B46.proved) Eq.refl Eq.refl

p48 : CCX12 • CX01 • CX02 • X0 • X0 • CCX12 ≈ CCX12 • CX01 • CX02 • CCX12
p48 = by-assoc-and (under (CCX12 • CX01 • CX02) (CCX12) B12.proved) Eq.refl Eq.refl

p49 : CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CCX12 • CX01 • CX02 • CCX12
p49 = trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (refl)))))))))))))))))))))))))

proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
proved = trans p23 (sym p49)
