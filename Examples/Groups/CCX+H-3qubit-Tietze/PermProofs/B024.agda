{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B024 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0006 ; module KB0011 ; module KB0012 ; module KB0026 ; module KB0027 ; module KB0029 ; module KB0033 ; module KB0035 ; module KB0036 ; module KB0037 ; module KB0046 ; module KB0118 ; module KB0125 ; module KB0129 ; module KB0144 ; module KB0153 ; module KB0164 ; module KB0215 ; module KB0219 ; module KB0308)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0020 ; module KB0022 ; module KB0025 ; module KB0281 ; module KB0282 ; module KB0407)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0018 ; module KB0045 ; module KB0150 ; module KB0161 ; module KB0214 ; module KB0221)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0131 ; module KB0152 ; module KB0366)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0079 ; module KB0107 ; module KB0108)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0225 ; module KB0862)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0481 ; module KB0605)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0163 ; module KB0355 ; module KB0357 ; module KB1658 ; module KB1661 ; module KB2829 ; module KB3094 ; module KB3579)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0916)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0229)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0515)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B016 using (module KB3965)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0378 ; module KB0385 ; module KB0442 ; module KB0483)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0815 ; module KB0835 ; module KB0884 ; module KB0890 ; module KB1209 ; module KB1329 ; module KB1366 ; module KB2234 ; module KB3112 ; module KB3123)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B021 using (module KB4079 ; module KB4332 ; module KB5458)

module comm03 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p1 = by-assoc-and (under (X0 • CX02 • CCX01) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX02 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p2 = by-assoc-and (under (X0 • CX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p3 : X0 • CX02 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CX02 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p3 = by-assoc-and (under (X0) (CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0033.proved) Eq.refl Eq.refl

  p4 : X0 • X2 • CX02 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • X0 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p4 = by-assoc-and (under (ε) (CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0125.proved) Eq.refl Eq.refl

  p5 : CX02 • X0 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p5 = by-assoc-and (under (CX02 • X0) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0011.proved) Eq.refl Eq.refl

  p6 : CX02 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p6 = by-assoc-and (under (CX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p7 : CX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p7 = by-assoc-and (under (CX02) (X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p8 : CX02 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p8 = by-assoc-and (under (CX02) (X0 • CCX01 • X2 • X0) KB0219.proved) Eq.refl Eq.refl

  p9 : CX02 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p9 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) KB0025.proved) Eq.refl Eq.refl

  p10 : CX01 • CX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CCX01 • X0
  p10 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • X0) (X0) KB0029.proved) Eq.refl Eq.refl

  p11 : CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CCX01 • X0
  p11 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0) KB0221.proved) Eq.refl Eq.refl

  p12 : CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • CX12 • CCX01
  p12 = by-assoc-and (under (CX01 • CX02 • CCX12 • X2 • CX01) (ε) KB0153.proved) Eq.refl Eq.refl

  p13 : CX01 • CX02 • CCX12 • X2 • CX01 • CX12 • CCX01 ≈ CX01 • CX02 • X2 • CX12 • CCX12 • CCX01 • CX01
  p13 = by-assoc-and (under (CX01 • CX02) (ε) KB3112.proved) Eq.refl Eq.refl

  p14 : CX01 • CX02 • X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01
  p14 = by-assoc-and (under (CX01) (CX12 • CCX12 • CCX01 • CX01) KB0033.proved) Eq.refl Eq.refl

  p15 : CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01
  p15 = by-assoc-and (under (ε) (CX02 • CX12 • CCX12 • CCX01 • CX01) KB0022.proved) Eq.refl Eq.refl

  p16 : X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
  p16 = by-assoc-and (under (X2) (CCX12 • CCX01 • CX01) KB0164.proved) Eq.refl Eq.refl

  p17 : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
  p17 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (refl)))))))))))))))))

  p18 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  p18 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0481.proved) Eq.refl Eq.refl

  p19 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  p19 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0215.proved) Eq.refl Eq.refl

  p20 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  p20 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0118.proved) Eq.refl Eq.refl

  p21 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  p21 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0047.proved) Eq.refl Eq.refl

  p22 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  p22 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • X1 • CCX01 • X1 • X0) KB3094.proved) Eq.refl Eq.refl

  p23 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0
  p23 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • X1 • CCX01 • X1 • X0) KB0036.proved) Eq.refl Eq.refl

  p24 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0
  p24 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0021.proved) Eq.refl Eq.refl

  p25 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p25 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10) (X0 • X1 • CCX01 • X1 • X0) KB0045.proved) Eq.refl Eq.refl

  p26 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p26 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (CX12 • X0 • X1 • CCX01 • X1 • X0) KB0047.proved) Eq.refl Eq.refl

  p27 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p27 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) KB0018.proved) Eq.refl Eq.refl

  p28 : X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p28 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) KB0012.proved) Eq.refl Eq.refl

  p29 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p29 = by-assoc-and (under (ε) (CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0) KB2234.proved) Eq.refl Eq.refl

  p30 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p30 = by-assoc-and (under (CX02) (CX12 • X0 • X1 • CCX01 • X1 • X0) KB1658.proved) Eq.refl Eq.refl

  p31 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p31 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0) KB0025.proved) Eq.refl Eq.refl

  p32 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • X1 • CCX01 • X1 • X0
  p32 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • X1 • CCX01 • X1 • X0) KB0163.proved) Eq.refl Eq.refl

  p33 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • X1 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X1 • CX02 • X0 • CCX01 • X1 • X0
  p33 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01) (CCX01 • X1 • X0) KB0229.proved) Eq.refl Eq.refl

  p34 : CX01 • CX02 • CCX12 • CX01 • X1 • CX02 • X0 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • X1 • CX01 • CX02 • X0 • CCX01 • X1 • X0
  p34 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX02 • X0 • CCX01 • X1 • X0) KB0035.proved) Eq.refl Eq.refl

  p35 : CX01 • CX02 • CCX12 • X1 • CX01 • CX02 • X0 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • CX02 • X0 • CX01 • CCX01 • X1 • X0
  p35 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X1 • X0) KB0442.proved) Eq.refl Eq.refl

  p36 : CX01 • CX02 • CCX12 • CX02 • X0 • CX01 • CCX01 • X1 • X0 ≈ CX01 • CX02 • CCX12 • X0 • X2 • CCX01 • CX01 • X1 • X0
  p36 = by-assoc-and (under (CX01 • CX02 • CCX12) (X1 • X0) KB0835.proved) Eq.refl Eq.refl

  p37 : CX01 • CX02 • CCX12 • X0 • X2 • CCX01 • CX01 • X1 • X0 ≈ CX01 • CX02 • X0 • CCX12 • X2 • CCX01 • CX01 • X1 • X0
  p37 = by-assoc-and (under (CX01 • CX02) (X2 • CCX01 • CX01 • X1 • X0) KB0046.proved) Eq.refl Eq.refl

  p38 : CX01 • CX02 • X0 • CCX12 • X2 • CCX01 • CX01 • X1 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • CX01 • X1 • X0
  p38 = by-assoc-and (under (CX01) (CCX01 • CX01 • X1 • X0) KB0916.proved) Eq.refl Eq.refl

  p39 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • CX01 • X1 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X1 • CX01 • X0
  p39 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12 • CCX01) (X0) KB0035.proved) Eq.refl Eq.refl

  p40 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X1 • CX01 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CX01 • CCX01 • X0
  p40 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (X0) KB0282.proved) Eq.refl Eq.refl

  p41 : CX01 • X0 • CX02 • CX10 • CCX12 • X1 • CX01 • CCX01 • X0 ≈ CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X0 • CX01
  p41 = by-assoc-and (under (CX01 • X0 • CX02 • CX10 • CCX12) (ε) KB0605.proved) Eq.refl Eq.refl

  p42 : CX01 • X0 • CX02 • CX10 • CCX12 • CCX01 • X0 • CX01 ≈ CX01 • X0 • CX02 • X0 • CX12 • CCX12 • CCX01 • CX01
  p42 = by-assoc-and (under (CX01 • X0 • CX02) (CX01) KB0884.proved) Eq.refl Eq.refl

  p43 : CX01 • X0 • CX02 • X0 • CX12 • CCX12 • CCX01 • CX01 ≈ CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01
  p43 = by-assoc-and (under (CX01) (CX12 • CCX12 • CCX01 • CX01) KB0161.proved) Eq.refl Eq.refl

  p44 : CX01 • X2 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01
  p44 = by-assoc-and (under (ε) (CX02 • CX12 • CCX12 • CCX01 • CX01) KB0022.proved) Eq.refl Eq.refl

  p45 : X2 • CX01 • CX02 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
  p45 = by-assoc-and (under (X2) (CCX12 • CCX01 • CX01) KB0164.proved) Eq.refl Eq.refl

  p46 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12 • CX01 • CCX12 • CCX01 • CX01
  p46 = trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (refl))))))))))))))))))))))))))))

  proved : X0 • X1 • CCX01 • X1 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X1 • CCX01 • X1 • X0
  proved = trans p17 (sym p46)

module comm04 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0 • X1 • CCX01 • X1
  p0 = by-assoc-and (under (X0) (X0 • X1 • CCX01 • X1) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X0 • X1 • CCX01 • X0 • CCX01 • X1
  p1 = by-assoc-and (under (X0) (CCX01 • X1) KB0378.proved) Eq.refl Eq.refl

  p2 : X0 • X1 • CCX01 • X0 • CCX01 • X1 ≈ X1 • CX12 • CCX01 • CCX01 • X1
  p2 = by-assoc-and (under (ε) (CCX01 • X1) KB0483.proved) Eq.refl Eq.refl

  p3 : X1 • CX12 • CCX01 • CCX01 • X1 ≈ X1 • CX12 • X1
  p3 = by-assoc-and (under (X1 • CX12) (X1) KB0011.proved) Eq.refl Eq.refl

  p4 : X1 • CX12 • X1 ≈ X2 • CX12
  p4 = by-assoc-and (under (ε) (ε) KB0144.proved) Eq.refl Eq.refl

  p5 : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X2 • CX12
  p5 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (refl)))))

  p6 : X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0
  p6 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) KB0150.proved) Eq.refl Eq.refl

  p7 : CX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X1 • CCX01 • X0 • CCX01 • X1 • X0
  p7 = by-assoc-and (under (ε) (CCX01 • X1 • X0) KB0378.proved) Eq.refl Eq.refl

  p8 : X1 • CCX01 • X0 • CCX01 • X1 • X0 ≈ X1 • X0 • CX12 • X1 • X0
  p8 = by-assoc-and (under (X1) (X1 • X0) KB0152.proved) Eq.refl Eq.refl

  p9 : X1 • X0 • CX12 • X1 • X0 ≈ X0 • X1 • CX12 • X1 • X0
  p9 = by-assoc-and (under (ε) (CX12 • X1 • X0) KB0044.proved) Eq.refl Eq.refl

  p10 : X0 • X1 • CX12 • X1 • X0 ≈ X0 • X2 • CX12 • X0
  p10 = by-assoc-and (under (X0) (X0) KB0144.proved) Eq.refl Eq.refl

  p11 : X0 • X2 • CX12 • X0 ≈ X0 • X2 • X0 • CX12
  p11 = by-assoc-and (under (X0 • X2) (ε) KB0045.proved) Eq.refl Eq.refl

  p12 : X0 • X2 • X0 • CX12 ≈ X0 • X0 • X2 • CX12
  p12 = by-assoc-and (under (X0) (CX12) KB0018.proved) Eq.refl Eq.refl

  p13 : X0 • X0 • X2 • CX12 ≈ X2 • CX12
  p13 = by-assoc-and (under (ε) (X2 • CX12) KB0012.proved) Eq.refl Eq.refl

  p14 : X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12
  p14 = trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (refl))))))))

  proved : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0
  proved = trans p5 (sym p14)

module comm05 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • X0 • CX12 • CCX02 • CCX01
  p1 = by-assoc-and (under (X0 • CX02) (CCX02 • CCX01) KB0152.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • X0 • CX12 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
  p2 = by-assoc-and (under (ε) (CX12 • CCX02 • CCX01) KB0161.proved) Eq.refl Eq.refl

  p3 : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
  p3 = trans p0 (trans p1 (trans p2 (refl)))

  p4 : CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0
  p4 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) KB0214.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0
  p5 = by-assoc-and (under (CX12 • CCX02) (X1 • CCX01 • X1 • X0) KB0045.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CX02 • CCX01 • X0
  p6 = by-assoc-and (under (CX12 • CCX02 • X0 • CX12) (X0) KB0150.proved) Eq.refl Eq.refl

  p7 : CX12 • CCX02 • X0 • CX12 • CX02 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX02 • CX12 • CCX01 • X0
  p7 = by-assoc-and (under (CX12 • CCX02 • X0) (CCX01 • X0) KB0027.proved) Eq.refl Eq.refl

  p8 : CX12 • CCX02 • X0 • CX02 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • CX02 • X0
  p8 = by-assoc-and (under (CX12 • CCX02) (X0) KB0385.proved) Eq.refl Eq.refl

  p9 : CX12 • CCX02 • CCX01 • X0 • CX02 • X0 ≈ CX12 • CCX02 • CCX01 • X2 • CX02
  p9 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) KB0161.proved) Eq.refl Eq.refl

  p10 : CX12 • CCX02 • CCX01 • X2 • CX02 ≈ CX12 • CCX02 • X2 • CCX01 • CX02
  p10 = by-assoc-and (under (CX12 • CCX02) (CX02) KB0029.proved) Eq.refl Eq.refl

  p11 : CX12 • CCX02 • X2 • CCX01 • CX02 ≈ CX12 • CCX02 • X2 • CX02 • CCX01
  p11 = by-assoc-and (under (CX12 • CCX02 • X2) (ε) KB0037.proved) Eq.refl Eq.refl

  p12 : CX12 • CCX02 • X2 • CX02 • CCX01 ≈ CX12 • X2 • CX02 • CCX02 • CCX01
  p12 = by-assoc-and (under (CX12) (CCX01) KB0281.proved) Eq.refl Eq.refl

  p13 : CX12 • X2 • CX02 • CCX02 • CCX01 ≈ X2 • CX12 • CX02 • CCX02 • CCX01
  p13 = by-assoc-and (under (ε) (CX02 • CCX02 • CCX01) KB0036.proved) Eq.refl Eq.refl

  p14 : X2 • CX12 • CX02 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
  p14 = by-assoc-and (under (X2) (CCX02 • CCX01) KB0027.proved) Eq.refl Eq.refl

  p15 : CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
  p15 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (refl)))))))))))

  proved : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0
  proved = trans p3 (sym p15)

module comm06 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX01
  p0 = by-assoc-and (under (X0) (X0 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • CCX01 ≈ X0 • CX02 • X0 • CX12
  p1 = by-assoc-and (under (X0 • CX02) (ε) KB0152.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • X0 • CX12 ≈ X2 • CX02 • CX12
  p2 = by-assoc-and (under (ε) (CX12) KB0161.proved) Eq.refl Eq.refl

  p3 : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ X2 • CX02 • CX12
  p3 = trans p0 (trans p1 (trans p2 (refl)))

  p4 : CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X1 • CX02 • X0 • CX12 • X1 • X0
  p4 = by-assoc-and (under (ε) (X1 • X0) KB0815.proved) Eq.refl Eq.refl

  p5 : X1 • CX02 • X0 • CX12 • X1 • X0 ≈ X0 • CX02 • CX12 • X1 • X1 • X0
  p5 = by-assoc-and (under (ε) (X1 • X0) KB0890.proved) Eq.refl Eq.refl

  p6 : X0 • CX02 • CX12 • X1 • X1 • X0 ≈ X0 • CX02 • CX12 • X0
  p6 = by-assoc-and (under (X0 • CX02 • CX12) (X0) KB0003.proved) Eq.refl Eq.refl

  p7 : X0 • CX02 • CX12 • X0 ≈ X0 • CX02 • X0 • CX12
  p7 = by-assoc-and (under (X0 • CX02) (ε) KB0045.proved) Eq.refl Eq.refl

  p8 : X0 • CX02 • X0 • CX12 ≈ X2 • CX02 • CX12
  p8 = by-assoc-and (under (ε) (CX12) KB0161.proved) Eq.refl Eq.refl

  p9 : CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02 • CX12
  p9 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (refl)))))

  proved : X0 • X1 • CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01 • X1 • X0
  proved = trans p3 (sym p9)

module comm13 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p2 = by-assoc-and (under (ε) (CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • X0 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p4 = by-assoc-and (under (CX12) (CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0129.proved) Eq.refl Eq.refl

  p5 : CX12 • X0 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p5 = by-assoc-and (under (ε) (CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p6 : X0 • CX12 • CCX02 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CCX02 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p6 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p7 : X0 • CX12 • CCX02 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CX12 • CX12 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p7 = by-assoc-and (under (X0 • CX12) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB1209.proved) Eq.refl Eq.refl

  p8 : X0 • CX12 • CX12 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p8 = by-assoc-and (under (X0) (CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0006.proved) Eq.refl Eq.refl

  p9 : X0 • CCX01 • CCX02 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CCX02 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p9 = by-assoc-and (under (X0 • CCX01 • CCX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p10 : X0 • CCX01 • CCX02 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX01 • X0 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
  p10 = by-assoc-and (under (X0 • CCX01) (CCX12 • X0 • CCX01 • X2 • X0) KB4079.proved) Eq.refl Eq.refl

  p11 : X0 • CCX01 • X0 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX01 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
  p11 = by-assoc-and (under (ε) (CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0) KB0153.proved) Eq.refl Eq.refl

  p12 : CX12 • CCX01 • CX21 • X2 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX21 • X2 • CX01 • CCX12 • X0 • CCX01 • X2 • X0
  p12 = by-assoc-and (under (ε) (CX01 • CCX12 • X0 • CCX01 • X2 • X0) KB3123.proved) Eq.refl Eq.refl

  p13 : CX10 • CCX01 • CCX12 • CX21 • X2 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • CCX12 • X0 • CCX01 • X2 • X0
  p13 = by-assoc-and (under (CX10 • CCX01 • CCX12) (CCX12 • X0 • CCX01 • X2 • X0) KB0225.proved) Eq.refl Eq.refl

  p14 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • X0 • CCX12 • CCX01 • X2 • X0
  p14 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01 • CX21 • X2) (CCX01 • X2 • X0) KB0046.proved) Eq.refl Eq.refl

  p15 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X2 • X0 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • CX21 • X0 • X2 • CCX12 • CCX01 • X2 • X0
  p15 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01 • CX21) (CCX12 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p16 : CX10 • CCX01 • CCX12 • CX01 • CX21 • X0 • X2 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • CX01 • X0 • CX21 • X2 • CCX12 • CCX01 • X2 • X0
  p16 = by-assoc-and (under (CX10 • CCX01 • CCX12 • CX01) (X2 • CCX12 • CCX01 • X2 • X0) KB0020.proved) Eq.refl Eq.refl

  p17 : CX10 • CCX01 • CCX12 • CX01 • X0 • CX21 • X2 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • CCX12 • X0 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (CX10 • CCX01 • CCX12) (CCX12 • CCX01 • X2 • X0) KB0862.proved) Eq.refl Eq.refl

  p18 : CX10 • CCX01 • CCX12 • X0 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ CX10 • CCX01 • X0 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (CX10 • CCX01) (X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) KB0046.proved) Eq.refl Eq.refl

  p19 : CX10 • CCX01 • X0 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • CCX01 • CX10 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (ε) (CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) KB0366.proved) Eq.refl Eq.refl

  p20 : X0 • CCX01 • CX10 • CCX12 • X2 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • CCX01 • X2 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (X0 • CCX01) (CX01 • CX21 • CCX12 • CCX01 • X2 • X0) KB0131.proved) Eq.refl Eq.refl

  p21 : X0 • CCX01 • X2 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (X0) (CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p22 : X0 • X2 • CCX01 • CCX12 • CX01 • CX21 • CCX12 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • CCX01 • X2 • X0
  p22 = by-assoc-and (under (X0 • X2 • CCX01) (CCX01 • X2 • X0) KB1366.proved) Eq.refl Eq.refl

  p23 : X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
  p23 = by-assoc-and (under (X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02) (X0) KB0029.proved) Eq.refl Eq.refl

  p24 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
  p24 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (refl))))))))))))))))))))))))

  p25 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p25 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0481.proved) Eq.refl Eq.refl

  p26 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p26 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0215.proved) Eq.refl Eq.refl

  p27 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p27 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0118.proved) Eq.refl Eq.refl

  p28 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p28 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0047.proved) Eq.refl Eq.refl

  p29 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p29 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB3094.proved) Eq.refl Eq.refl

  p30 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p30 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0036.proved) Eq.refl Eq.refl

  p31 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p31 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0021.proved) Eq.refl Eq.refl

  p32 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p32 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB3579.proved) Eq.refl Eq.refl

  p33 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p33 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0357.proved) Eq.refl Eq.refl

  p34 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
  p34 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0044.proved) Eq.refl Eq.refl

  p35 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
  p35 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p36 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
  p36 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0047.proved) Eq.refl Eq.refl

  p37 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
  p37 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0355.proved) Eq.refl Eq.refl

  p38 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
  p38 = by-assoc-and (under (CX10) (CX10 • X0 • CCX01 • CCX02 • CCX01 • X0) KB2829.proved) Eq.refl Eq.refl

  p39 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0
  p39 = by-assoc-and (under (ε) (CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0) KB1661.proved) Eq.refl Eq.refl

  p40 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p40 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0026.proved) Eq.refl Eq.refl

  p41 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p41 = by-assoc-and (under (CX02) (CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) KB1658.proved) Eq.refl Eq.refl

  p42 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p42 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0025.proved) Eq.refl Eq.refl

  p43 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X0
  p43 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0163.proved) Eq.refl Eq.refl

  p44 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX01 • CX02 • CCX12 • X0 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0
  p44 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0) KB5458.proved) Eq.refl Eq.refl

  p45 : CX01 • CX02 • CCX12 • X0 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0 ≈ CX01 • CX02 • X0 • CCX12 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0
  p45 = by-assoc-and (under (CX01 • CX02) (X1 • CCX01 • CCX02 • X2 • CCX01 • X0) KB0046.proved) Eq.refl Eq.refl

  p46 : CX01 • CX02 • X0 • CCX12 • X1 • CCX01 • CCX02 • X2 • CCX01 • X0 ≈ CX01 • X0 • X2 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0
  p46 = by-assoc-and (under (CX01) (CCX02 • X2 • CCX01 • X0) KB3965.proved) Eq.refl Eq.refl

  p47 : CX01 • X0 • X2 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0 ≈ X2 • CX01 • X0 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0
  p47 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0) KB0221.proved) Eq.refl Eq.refl

  p48 : X2 • CX01 • X0 • CCX01 • CCX12 • X1 • CCX02 • X2 • CCX01 • X0 ≈ X2 • X0 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
  p48 = by-assoc-and (under (X2) (CCX02 • X2 • CCX01 • X0) KB4332.proved) Eq.refl Eq.refl

  p49 : X2 • X0 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
  p49 = by-assoc-and (under (ε) (CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0) KB0018.proved) Eq.refl Eq.refl

  p50 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • X2 • CCX01 • CX01 • CX20 • CCX12 • CCX02 • X2 • CCX01 • X0
  p50 = trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (refl)))))))))))))))))))))))))

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  proved = trans p24 (sym p50)

module comm14 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1
  p0 = by-assoc-and (under (X0) (X0 • X1 • CCX01 • X1) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X1 • CCX01 • X1) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 ≈ CX12 • CX21 • CCX02 • CX12 • X1 • CCX01 • X1
  p2 = by-assoc-and (under (ε) (CX12 • X1 • CCX01 • X1) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • X1 • CCX01 • X1 ≈ CX12 • CX21 • CCX02 • CX12 • CX02 • CCX01
  p3 = by-assoc-and (under (CX12 • CX21 • CCX02 • CX12) (ε) KB0150.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • CX12 • CX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX02 • CX12 • CCX01
  p4 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01) KB0027.proved) Eq.refl Eq.refl

  p5 : CX12 • CX21 • CCX02 • CX02 • CX12 • CCX01 ≈ CX12 • CX02 • CX21 • CCX02 • CX12 • CCX01
  p5 = by-assoc-and (under (CX12) (CX12 • CCX01) KB0407.proved) Eq.refl Eq.refl

  p6 : CX12 • CX02 • CX21 • CCX02 • CX12 • CCX01 ≈ CX02 • CX12 • CX21 • CCX02 • CX12 • CCX01
  p6 = by-assoc-and (under (ε) (CX21 • CCX02 • CX12 • CCX01) KB0027.proved) Eq.refl Eq.refl

  p7 : CX02 • CX12 • CX21 • CCX02 • CX12 • CCX01 ≈ CX02 • CX12 • CX21 • CX12 • CCX01 • CCX02
  p7 = by-assoc-and (under (CX02 • CX12 • CX21) (ε) KB0308.proved) Eq.refl Eq.refl

  p8 : CX02 • CX12 • CX21 • CX12 • CCX01 • CCX02 ≈ CX02 • SWAP12 • CCX01 • CCX02
  p8 = by-assoc-and (under (CX02) (CCX01 • CCX02) KB0079.proved) Eq.refl Eq.refl

  p9 : CX02 • SWAP12 • CCX01 • CCX02 ≈ CX02 • CCX02 • SWAP12 • CCX02
  p9 = by-assoc-and (under (CX02) (CCX02) KB0107.proved) Eq.refl Eq.refl

  p10 : CX02 • CCX02 • SWAP12 • CCX02 ≈ CX02 • CCX02 • CCX01 • SWAP12
  p10 = by-assoc-and (under (CX02 • CCX02) (ε) KB0108.proved) Eq.refl Eq.refl

  p11 : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • SWAP12
  p11 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))))))

  p12 : X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0
  p12 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0150.proved) Eq.refl Eq.refl

  p13 : CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • X0 • CX12 • CCX02 • CCX01 • X0
  p13 = by-assoc-and (under (CX02) (CCX02 • CCX01 • X0) KB0152.proved) Eq.refl Eq.refl

  p14 : CX02 • X0 • CX12 • CCX02 • CCX01 • X0 ≈ CX02 • X0 • X0 • CCX02 • CCX01 • SWAP12
  p14 = by-assoc-and (under (CX02 • X0) (ε) KB1329.proved) Eq.refl Eq.refl

  p15 : CX02 • X0 • X0 • CCX02 • CCX01 • SWAP12 ≈ CX02 • CCX02 • CCX01 • SWAP12
  p15 = by-assoc-and (under (CX02) (CCX02 • CCX01 • SWAP12) KB0012.proved) Eq.refl Eq.refl

  p16 : X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX02 • CCX02 • CCX01 • SWAP12
  p16 = trans p12 (trans p13 (trans p14 (trans p15 (refl))))

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 • X0
  proved = trans p11 (sym p16)
