{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B019 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0006 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0023 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0035 ; module KB0037 ; module KB0120 ; module KB0121 ; module KB0127 ; module KB0129 ; module KB0139 ; module KB0147 ; module KB0151 ; module KB0153 ; module KB0213 ; module KB0217 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0020 ; module KB0022 ; module KB0025 ; module KB0122 ; module KB0123 ; module KB0137 ; module KB0165)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0016 ; module KB0019 ; module KB0045 ; module KB0063 ; module KB0090 ; module KB0141 ; module KB0150 ; module KB0161 ; module KB0214 ; module KB1438)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0088 ; module KB0140 ; module KB0154 ; module KB0158 ; module KB0310 ; module KB0340)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB0333)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0015 ; module KB0034 ; module KB0041 ; module KB0107 ; module KB0303)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0060 ; module KB0061)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0145 ; module KB0188 ; module KB0231)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B009 using (module KB0179)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0285)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0055)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0187)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0167 ; module KB0203 ; module KB0515)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B016 using (module KB0143)

module KB0222 where

  p0 : CX12 • CX02 • X1 ≈ CX02 • CX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0027.proved) Eq.refl Eq.refl

  p1 : CX12 • CX02 • X1 ≈ CX12 • X1 • CX02
  p1 = by-assoc-and (under (CX12) (ε) KB0023.proved) Eq.refl Eq.refl

  p2 : CX02 • CX12 • X1 ≈ CX12 • X1 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX12 • X1 ≈ CX02 • CX12 • X1
  p3 = refl

  p4 : CX12 • X1 • CX02 ≈ CX12 • X1 • CX02
  p4 = refl

  p5 : CX02 • CX12 • X1 ≈ CX12 • X1 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • X1 • CX02 ≈ CX02 • CX12 • X1
  p6 = sym p5

  proved : CX12 • X1 • CX02 ≈ CX02 • CX12 • X1
  proved = p6

module KB1439 where

  p0 : CCX01 • CCX02 • CCX01 • X1 • CX02 ≈ CX12 • CCX02 • CX12 • X1 • CX02
  p0 = by-assoc-and (under (ε) (X1 • CX02) KB0214.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • X1 • CX02 ≈ CCX01 • CCX02 • X1 • CCX01
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0203.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CCX01 • CCX02 • X1 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CX12 • CCX02 • CX02 • CX12 • X1
  p3 = by-assoc-and (under (CX12 • CCX02) (ε) KB0222.proved) Eq.refl Eq.refl

  p4 : CX12 • CCX02 • CX02 • CX12 • X1 ≈ CX01 • CX12 • CCX02 • CX12 • X1
  p4 = by-assoc-and (under (ε) (CX12 • X1) KB0285.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CX01 • CX12 • CCX02 • CX12 • X1
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX01 • CCX02 • X1 • CCX01 ≈ CCX01 • X1 • CCX02 • CCX01
  p6 = by-assoc-and (under (CCX01) (CCX01) KB0028.proved) Eq.refl Eq.refl

  p7 : CCX01 • CCX02 • X1 • CCX01 ≈ CCX01 • X1 • CCX02 • CCX01
  p7 = trans p6 (refl)

  p8 : CX01 • CX12 • CCX02 • CX12 • X1 ≈ CCX01 • X1 • CCX02 • CCX01
  p8 = trans (sym p5) (trans p2 p7)

  proved : CX01 • CX12 • CCX02 • CX12 • X1 ≈ CCX01 • X1 • CCX02 • CCX01
  proved = p8

module decodeX1 where

  p0 : X1 ≈ X1
  p0 = refl

  p1 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p2 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p3 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p3 = by-assoc-and (under (ε) (CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0515.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p4 = by-assoc-and (under (CX12 • CX21 • CCX02) (X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p5 : CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p5 = by-assoc-and (under (CX12) (CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0129.proved) Eq.refl Eq.refl

  p6 : CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p6 = by-assoc-and (under (ε) (CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p7 : X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • CCX02 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p7 = by-assoc-and (under (X0) (X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB1438.proved) Eq.refl Eq.refl

  p8 : X0 • X1 • CCX01 • CX01 • CCX02 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • X1 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p8 = by-assoc-and (under (X0 • X1 • CCX01 • CX01) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p9 : X0 • X1 • CCX01 • CX01 • X1 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • X1 • CCX01 • X1 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p9 = by-assoc-and (under (X0 • X1 • CCX01) (CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0035.proved) Eq.refl Eq.refl

  p10 : X0 • X1 • CCX01 • X1 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • CCX01 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p10 = by-assoc-and (under (X0) (CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p11 : X0 • CX02 • CCX01 • CX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p11 = by-assoc-and (under (X0) (CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0137.proved) Eq.refl Eq.refl

  p12 : X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p12 = by-assoc-and (under (X0 • CX01 • CCX01 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p13 : X0 • CX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p13 = by-assoc-and (under (X0 • CX01) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p14 : X0 • CX01 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p14 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p15 : X0 • CX01 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • X0 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p15 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02 • X0) (CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p16 : X0 • CX01 • CX12 • CCX02 • X0 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p16 = by-assoc-and (under (X0 • CX01 • CX12 • CCX02) (CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p17 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX02 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p17 = by-assoc-and (under (X0 • CX01) (CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p18 : X0 • CX01 • CCX01 • CCX02 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • CCX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p18 = by-assoc-and (under (X0 • CX01 • CCX01) (CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0010.proved) Eq.refl Eq.refl

  p19 : X0 • CX01 • CCX01 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X0 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p19 = by-assoc-and (under (X0 • CX01) (X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p20 : X0 • CX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p20 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0158.proved) Eq.refl Eq.refl

  p21 : X1 • CX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX01 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p21 = by-assoc-and (under (X1 • CX01) (X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p22 : X1 • CX01 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p22 = by-assoc-and (under (X1) (CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB1439.proved) Eq.refl Eq.refl

  p23 : X1 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p23 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p24 : CX02 • CCX01 • CCX02 • CCX01 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX12 • CCX02 • CX12 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p24 = by-assoc-and (under (CX02) (CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p25 : CX02 • CX12 • CCX02 • CX12 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p25 = by-assoc-and (under (CX02) (X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p26 : CX02 • CCX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p26 = by-assoc-and (under (CX02 • CCX01) (CCX01 • CCX01 • CCX02 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p27 : CX02 • CCX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p27 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) KB0120.proved) Eq.refl Eq.refl

  p28 : X1 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
  p28 = by-assoc-and (under (X1) (CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p29 : X1 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX02 • CCX02 • CCX01
  p29 = by-assoc-and (under (X1) (CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p30 : X1 • CCX01 • CCX02 • CCX02 • CCX01 ≈ X1 • CCX01 • CCX01
  p30 = by-assoc-and (under (X1 • CCX01) (CCX01) KB0010.proved) Eq.refl Eq.refl

  p31 : X1 • CCX01 • CCX01 ≈ X1
  p31 = by-assoc-and (under (X1) (ε) KB0011.proved) Eq.refl Eq.refl

  p32 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1
  p32 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (refl)))))))))))))))))))))))))))))))

  proved : X1 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  proved = trans p0 (sym p32)

module KB0475 where

  p0 : X2 • X1 • CX02 • CCX01 ≈ X2 • CCX01 • X1
  p0 = by-assoc-and (under (X2) (ε) KB0151.proved) Eq.refl Eq.refl

  p1 : X2 • X1 • CX02 • CCX01 ≈ X1 • X2 • CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0019.proved) Eq.refl Eq.refl

  p2 : X2 • CCX01 • X1 ≈ X1 • X2 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : X2 • CCX01 • X1 ≈ X2 • CCX01 • X1
  p3 = refl

  p4 : X1 • X2 • CX02 • CCX01 ≈ X1 • X2 • CX02 • CCX01
  p4 = refl

  p5 : X2 • CCX01 • X1 ≈ X1 • X2 • CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • X2 • CX02 • CCX01 ≈ X2 • CCX01 • X1
  p6 = sym p5

  proved : X1 • X2 • CX02 • CCX01 ≈ X2 • CCX01 • X1
  proved = p6

module decodeX2 where

  p0 : X2 ≈ X2
  p0 = refl

  p1 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
  p1 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • CCX01 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
  p2 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • X0 • X1 • CCX01 • X1 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p3 : X0 • CX02 • CCX01 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • X0 • X1 • CCX01 • X1 • CCX01
  p3 = by-assoc-and (under (X0 • CX02) (X0 • X1 • CCX01 • X1 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p4 : X0 • CX02 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • X1 • CCX01 • X1 • CCX01
  p4 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01) KB0161.proved) Eq.refl Eq.refl

  p5 : X2 • CX02 • X1 • CCX01 • X1 • CCX01 ≈ X2 • X1 • CX02 • CCX01 • X1 • CCX01
  p5 = by-assoc-and (under (X2) (CCX01 • X1 • CCX01) KB0023.proved) Eq.refl Eq.refl

  p6 : X2 • X1 • CX02 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX02 • CCX01 • X1 • CCX01
  p6 = by-assoc-and (under (ε) (CX02 • CCX01 • X1 • CCX01) KB0019.proved) Eq.refl Eq.refl

  p7 : X1 • X2 • CX02 • CCX01 • X1 • CCX01 ≈ X2 • CCX01 • X1 • X1 • CCX01
  p7 = by-assoc-and (under (ε) (X1 • CCX01) KB0475.proved) Eq.refl Eq.refl

  p8 : X2 • CCX01 • X1 • X1 • CCX01 ≈ X2 • CCX01 • CCX01
  p8 = by-assoc-and (under (X2 • CCX01) (CCX01) KB0003.proved) Eq.refl Eq.refl

  p9 : X2 • CCX01 • CCX01 ≈ X2
  p9 = by-assoc-and (under (X2) (ε) KB0011.proved) Eq.refl Eq.refl

  p10 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X2
  p10 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl)))))))))

  proved : X2 ≈ X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
  proved = trans p0 (sym p10)

module KB0181 where

  p0 : CX10 • CCX12 • CX12 • CX12 ≈ CX12 • CCX12 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0141.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CX12 ≈ CX10 • CCX12
  p1 = by-assoc-and (under (CX10 • CCX12) (ε) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CX12 ≈ CX12 • CCX12 • CX12
  p3 = refl

  p4 : CX10 • CCX12 ≈ CX10 • CCX12
  p4 = refl

  p5 : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
  proved = p5

module KB0183 where

  p0 : CX12 • CX12 • X1 • CX12 ≈ CX12 • X1 • X2
  p0 = by-assoc-and (under (CX12) (ε) KB0145.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • X1 • CX12 ≈ X1 • CX12
  p1 = by-assoc-and (under (ε) (X1 • CX12) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • X1 • X2 ≈ X1 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • X1 • X2 ≈ CX12 • X1 • X2
  p3 = refl

  p4 : X1 • CX12 ≈ X1 • CX12
  p4 = refl

  p5 : CX12 • X1 • X2 ≈ X1 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • X1 • X2 ≈ X1 • CX12
  proved = p5

module KB0193 where

  p0 : X0 • CX21 • CCX02 • CCX02 ≈ CCX02 • X0 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0165.proved) Eq.refl Eq.refl

  p1 : X0 • CX21 • CCX02 • CCX02 ≈ X0 • CX21
  p1 = by-assoc-and (under (X0 • CX21) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • CCX02 ≈ X0 • CX21
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • CCX02 ≈ CCX02 • X0 • CCX02
  p3 = refl

  p4 : X0 • CX21 ≈ X0 • CX21
  p4 = refl

  p5 : CCX02 • X0 • CCX02 ≈ X0 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X0 • CCX02 ≈ X0 • CX21
  proved = p5

module KB0234 where

  p0 : CX21 • SWAP12 • X2 ≈ CX21 • X1 • SWAP12
  p0 = by-assoc-and (under (CX21) (ε) KB0055.proved) Eq.refl Eq.refl

  p1 : CX21 • SWAP12 • X2 ≈ CX12 • CX21 • X2
  p1 = by-assoc-and (under (ε) (X2) KB0041.proved) Eq.refl Eq.refl

  p2 : CX21 • X1 • SWAP12 ≈ CX12 • CX21 • X2
  p2 = trans (sym p0) p1

  p3 : CX21 • X1 • SWAP12 ≈ X1 • CX21 • SWAP12
  p3 = by-assoc-and (under (ε) (SWAP12) KB0034.proved) Eq.refl Eq.refl

  p4 : X1 • CX21 • SWAP12 ≈ X1 • CX12 • CX21
  p4 = by-assoc-and (under (X1) (ε) KB0041.proved) Eq.refl Eq.refl

  p5 : CX21 • X1 • SWAP12 ≈ X1 • CX12 • CX21
  p5 = trans p3 (trans p4 (refl))

  p6 : CX12 • CX21 • X2 ≈ CX12 • CX21 • X2
  p6 = refl

  p7 : X1 • CX12 • CX21 ≈ CX12 • CX21 • X2
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX12 • CX21 • X2 ≈ X1 • CX12 • CX21
  p8 = sym p7

  proved : CX12 • CX21 • X2 ≈ X1 • CX12 • CX21
  proved = p8

module KB0283 where

  p0 : CX12 • CX01 • CX02 • CCX01 ≈ CX01 • CX12 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0127.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX02 • CCX01 ≈ CX12 • CCX01 • CX01
  p1 = by-assoc-and (under (CX12) (ε) KB0123.proved) Eq.refl Eq.refl

  p2 : CX01 • CX12 • CCX01 ≈ CX12 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX12 • CCX01 ≈ CX01 • CX12 • CCX01
  p3 = refl

  p4 : CX12 • CCX01 • CX01 ≈ CX12 • CCX01 • CX01
  p4 = refl

  p5 : CX01 • CX12 • CCX01 ≈ CX12 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CCX01 • CX01 ≈ CX01 • CX12 • CCX01
  p6 = sym p5

  proved : CX12 • CCX01 • CX01 ≈ CX01 • CX12 • CCX01
  proved = p6

module KB0306 where

  p0 : CX01 • CX20 • CX21 • CCX12 ≈ CX20 • CX01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0303.proved) Eq.refl Eq.refl

  p1 : CX01 • CX20 • CX21 • CCX12 ≈ CX01 • CCX12 • CX21
  p1 = by-assoc-and (under (CX01) (ε) KB0179.proved) Eq.refl Eq.refl

  p2 : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX20 • CX01 • CCX12 ≈ CX20 • CX01 • CCX12
  p3 = refl

  p4 : CX01 • CCX12 • CX21 ≈ CX01 • CCX12 • CX21
  p4 = refl

  p5 : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
  proved = p5

module KB0314 where

  p0 : CX02 • CX10 • CX12 • CCX01 ≈ CX10 • CX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0310.proved) Eq.refl Eq.refl

  p1 : CX02 • CX10 • CX12 • CCX01 ≈ CX02 • CCX01 • CX10
  p1 = by-assoc-and (under (CX02) (ε) KB0147.proved) Eq.refl Eq.refl

  p2 : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CX02 • CCX01 ≈ CX10 • CX02 • CCX01
  p3 = refl

  p4 : CX02 • CCX01 • CX10 ≈ CX02 • CCX01 • CX10
  p4 = refl

  p5 : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
  proved = p5

module KB0331 where

  p0 : CCX02 • CCX01 • CCX02 • CCX02 ≈ CX21 • CCX01 • CX21 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0213.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX01 • CCX02 • CCX02 ≈ CCX02 • CCX01
  p1 = by-assoc-and (under (CCX02 • CCX01) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CX21 • CCX02 ≈ CCX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CX21 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0217.proved) Eq.refl Eq.refl

  p4 : CX21 • CCX01 • CX21 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX02
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX01 ≈ CCX02 • CCX01
  p5 = refl

  p6 : CX12 • CCX02 • CX12 • CCX02 ≈ CCX02 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX12 • CCX02 • CX12 • CCX02 ≈ CCX02 • CCX01
  proved = p6

module KB0332 where

  p0 : CX12 • CX12 • CCX02 • CX12 • CCX02 ≈ CX12 • CCX02 • CCX01
  p0 = by-assoc-and (under (CX12) (ε) KB0331.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX02 • CX12 • CCX02 ≈ CCX02 • CX12 • CCX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX02) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX01 ≈ CCX02 • CX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
  p3 = refl

  p4 : CCX02 • CX12 • CCX02 ≈ CCX02 • CX12 • CCX02
  p4 = refl

  p5 : CX12 • CCX02 • CCX01 ≈ CCX02 • CX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX02 ≈ CX12 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX02 • CX12 • CCX02 ≈ CX12 • CCX02 • CCX01
  proved = p6

module KB0334 where

  p0 : CX12 • CX12 • CCX01 • CCX02 • CX12 ≈ CX12 • CCX02 • CCX01
  p0 = by-assoc-and (under (CX12) (ε) KB0333.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX01 • CCX02 • CX12 ≈ CCX01 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02 • CX12) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
  p3 = refl

  p4 : CCX01 • CCX02 • CX12 ≈ CCX01 • CCX02 • CX12
  p4 = refl

  p5 : CX12 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX02 • CX12 ≈ CX12 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX01 • CCX02 • CX12 ≈ CX12 • CCX02 • CCX01
  proved = p6

module KB0341 where

  p0 : CX01 • CX01 • CCX02 • CCX12 • CX01 ≈ CX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX01) (ε) KB0340.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX02 • CCX12 • CX01 ≈ CCX02 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX02 ≈ CX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX02 • CCX12 • CX01 ≈ CCX02 • CCX12 • CX01
  p4 = refl

  p5 : CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX12 • CX01 ≈ CX01 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX02 • CCX12 • CX01 ≈ CX01 • CCX12 • CCX02
  proved = p6

module KB0378 where

  p0 : CX02 • CCX01 • X1 • X0 ≈ X1 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0120.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • X0 ≈ CX02 • CCX01 • X0 • X1
  p1 = by-assoc-and (under (CX02 • CCX01) (ε) KB0044.proved) Eq.refl Eq.refl

  p2 : X1 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • X1
  p2 = trans (sym p0) p1

  p3 : X1 • CCX01 • X0 ≈ X1 • CCX01 • X0
  p3 = refl

  p4 : CX02 • CCX01 • X0 • X1 ≈ CX02 • CCX01 • X0 • X1
  p4 = refl

  p5 : X1 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • CCX01 • X0 • X1 ≈ X1 • CCX01 • X0
  p6 = sym p5

  proved : CX02 • CCX01 • X0 • X1 ≈ X1 • CCX01 • X0
  proved = p6

module KB0385 where

  p0 : X0 • CX12 • CCX01 • CX02 ≈ CCX01 • X0 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0121.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX01 • CX02 ≈ X0 • CX12 • CX02 • CCX01
  p1 = by-assoc-and (under (X0 • CX12) (ε) KB0037.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX02 ≈ X0 • CX12 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX02 ≈ CCX01 • X0 • CX02
  p3 = refl

  p4 : X0 • CX12 • CX02 • CCX01 ≈ X0 • CX02 • CX12 • CCX01
  p4 = by-assoc-and (under (X0) (CCX01) KB0027.proved) Eq.refl Eq.refl

  p5 : X0 • CX12 • CX02 • CCX01 ≈ X0 • CX02 • CX12 • CCX01
  p5 = trans p4 (refl)

  p6 : CCX01 • X0 • CX02 ≈ X0 • CX02 • CX12 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X0 • CX02 • CX12 • CCX01 ≈ CCX01 • X0 • CX02
  p7 = sym p6

  proved : X0 • CX02 • CX12 • CCX01 ≈ CCX01 • X0 • CX02
  proved = p7

module KB0390 where

  p0 : CCX01 • X2 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
  p0 = by-assoc-and (under (CCX01) (ε) KB0122.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • CX01 • CCX02 ≈ X2 • CCX01 • CX01 • CCX02
  p1 = by-assoc-and (under (ε) (CX01 • CCX02) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • X2 ≈ X2 • CCX01 • CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • X2 ≈ CCX01 • CCX02 • X2
  p3 = refl

  p4 : X2 • CCX01 • CX01 • CCX02 ≈ X2 • CCX01 • CX01 • CCX02
  p4 = refl

  p5 : CCX01 • CCX02 • X2 ≈ X2 • CCX01 • CX01 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
  p6 = sym p5

  proved : X2 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX02 • X2
  proved = p6

module KB0417 where

  p0 : SWAP12 • CX12 • CX21 • CCX02 • X0 ≈ SWAP12 • CX12 • X0 • CCX02
  p0 = by-assoc-and (under (SWAP12 • CX12) (ε) KB0129.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX12 • CX21 • CCX02 • X0 ≈ CX12 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0060.proved) Eq.refl Eq.refl

  p2 : SWAP12 • CX12 • X0 • CCX02 ≈ CX12 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : SWAP12 • CX12 • X0 • CCX02 ≈ CX12 • CX21 • X0 • CCX02
  p3 = by-assoc-and (under (ε) (X0 • CCX02) KB0061.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • X0 • CCX02 ≈ CX12 • X0 • CX21 • CCX02
  p4 = by-assoc-and (under (CX12) (CCX02) KB0020.proved) Eq.refl Eq.refl

  p5 : CX12 • X0 • CX21 • CCX02 ≈ X0 • CX12 • CX21 • CCX02
  p5 = by-assoc-and (under (ε) (CX21 • CCX02) KB0045.proved) Eq.refl Eq.refl

  p6 : SWAP12 • CX12 • X0 • CCX02 ≈ X0 • CX12 • CX21 • CCX02
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  p7 : CX12 • CCX02 • X0 ≈ CX12 • CCX02 • X0
  p7 = refl

  p8 : X0 • CX12 • CX21 • CCX02 ≈ CX12 • CCX02 • X0
  p8 = trans (sym p6) (trans p2 p7)

  proved : X0 • CX12 • CX21 • CCX02 ≈ CX12 • CCX02 • X0
  proved = p8

module KB0442 where

  p0 : CX02 • X1 • CX01 • X0 ≈ CX02 • X0 • CX01
  p0 = by-assoc-and (under (CX02) (ε) KB0139.proved) Eq.refl Eq.refl

  p1 : CX02 • X1 • CX01 • X0 ≈ X1 • CX02 • CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0023.proved) Eq.refl Eq.refl

  p2 : CX02 • X0 • CX01 ≈ X1 • CX02 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX02 • X0 • CX01 ≈ CX02 • X0 • CX01
  p3 = refl

  p4 : X1 • CX02 • CX01 • X0 ≈ X1 • CX01 • CX02 • X0
  p4 = by-assoc-and (under (X1) (X0) KB0025.proved) Eq.refl Eq.refl

  p5 : X1 • CX02 • CX01 • X0 ≈ X1 • CX01 • CX02 • X0
  p5 = trans p4 (refl)

  p6 : CX02 • X0 • CX01 ≈ X1 • CX01 • CX02 • X0
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X1 • CX01 • CX02 • X0 ≈ CX02 • X0 • CX01
  p7 = sym p6

  proved : X1 • CX01 • CX02 • X0 ≈ CX02 • X0 • CX01
  proved = p7

module KB0445 where

  p0 : SWAP12 • CX12 • CCX01 • X0 ≈ SWAP12 • X0 • CCX01
  p0 = by-assoc-and (under (SWAP12) (ε) KB0140.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX12 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0061.proved) Eq.refl Eq.refl

  p2 : SWAP12 • X0 • CCX01 ≈ CX12 • CX21 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : SWAP12 • X0 • CCX01 ≈ X0 • SWAP12 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0015.proved) Eq.refl Eq.refl

  p4 : X0 • SWAP12 • CCX01 ≈ X0 • CCX02 • SWAP12
  p4 = by-assoc-and (under (X0) (ε) KB0107.proved) Eq.refl Eq.refl

  p5 : SWAP12 • X0 • CCX01 ≈ X0 • CCX02 • SWAP12
  p5 = trans p3 (trans p4 (refl))

  p6 : CX12 • CX21 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0
  p6 = refl

  p7 : X0 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01 • X0
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX12 • CX21 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12
  p8 = sym p7

  proved : CX12 • CX21 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12
  proved = p8

module KB0483 where

  p0 : X1 • X0 • CCX01 • X0 ≈ X1 • CX12 • CCX01
  p0 = by-assoc-and (under (X1) (ε) KB0153.proved) Eq.refl Eq.refl

  p1 : X1 • X0 • CCX01 • X0 ≈ X0 • X1 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0044.proved) Eq.refl Eq.refl

  p2 : X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : X1 • CX12 • CCX01 ≈ X1 • CX12 • CCX01
  p3 = refl

  p4 : X0 • X1 • CCX01 • X0 ≈ X0 • X1 • CCX01 • X0
  p4 = refl

  p5 : X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • X1 • CCX01 • X0 ≈ X1 • CX12 • CCX01
  p6 = sym p5

  proved : X0 • X1 • CCX01 • X0 ≈ X1 • CX12 • CCX01
  proved = p6

module KB0486 where

  p0 : CX10 • X2 • CCX02 • X2 ≈ CX10 • CX01 • CCX02
  p0 = by-assoc-and (under (CX10) (ε) KB0154.proved) Eq.refl Eq.refl

  p1 : CX10 • X2 • CCX02 • X2 ≈ X2 • CX10 • CCX02 • X2
  p1 = by-assoc-and (under (ε) (CCX02 • X2) KB0021.proved) Eq.refl Eq.refl

  p2 : CX10 • CX01 • CCX02 ≈ X2 • CX10 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CX10 • CX01 • CCX02 ≈ CX01 • SWAP01 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0088.proved) Eq.refl Eq.refl

  p4 : CX01 • SWAP01 • CCX02 ≈ CX01 • CCX12 • SWAP01
  p4 = by-assoc-and (under (CX01) (ε) KB0090.proved) Eq.refl Eq.refl

  p5 : CX10 • CX01 • CCX02 ≈ CX01 • CCX12 • SWAP01
  p5 = trans p3 (trans p4 (refl))

  p6 : X2 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CCX02 • X2
  p6 = refl

  p7 : CX01 • CCX12 • SWAP01 ≈ X2 • CX10 • CCX02 • X2
  p7 = trans (sym p5) (trans p2 p6)

  p8 : X2 • CX10 • CCX02 • X2 ≈ CX01 • CCX12 • SWAP01
  p8 = sym p7

  proved : X2 • CX10 • CCX02 • X2 ≈ CX01 • CCX12 • SWAP01
  proved = p8

module KB0519 where

  p0 : CX01 • X2 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
  p0 = by-assoc-and (under (CX01) (ε) KB0167.proved) Eq.refl Eq.refl

  p1 : CX01 • X2 • CCX12 • X2 ≈ X2 • CX01 • CCX12 • X2
  p1 = by-assoc-and (under (ε) (CCX12 • X2) KB0022.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CCX12 ≈ X2 • CX01 • CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CCX12 ≈ CX01 • CX10 • CCX12
  p3 = refl

  p4 : X2 • CX01 • CCX12 • X2 ≈ X2 • CX01 • CCX12 • X2
  p4 = refl

  p5 : CX01 • CX10 • CCX12 ≈ X2 • CX01 • CCX12 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CX01 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
  p6 = sym p5

  proved : X2 • CX01 • CCX12 • X2 ≈ CX01 • CX10 • CCX12
  proved = p6

module KB0561 where

  p0 : SWAP12 • CCX01 • X0 • CX12 ≈ SWAP12 • X0 • CCX01
  p0 = by-assoc-and (under (SWAP12) (ε) KB0187.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CCX01 • X0 • CX12 ≈ CCX02 • SWAP12 • X0 • CX12
  p1 = by-assoc-and (under (ε) (X0 • CX12) KB0107.proved) Eq.refl Eq.refl

  p2 : SWAP12 • X0 • CCX01 ≈ CCX02 • SWAP12 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • X0 • CCX01 ≈ X0 • SWAP12 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0015.proved) Eq.refl Eq.refl

  p4 : X0 • SWAP12 • CCX01 ≈ X0 • CCX02 • SWAP12
  p4 = by-assoc-and (under (X0) (ε) KB0107.proved) Eq.refl Eq.refl

  p5 : SWAP12 • X0 • CCX01 ≈ X0 • CCX02 • SWAP12
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX02 • SWAP12 • X0 • CX12 ≈ CCX02 • X0 • SWAP12 • CX12
  p6 = by-assoc-and (under (CCX02) (CX12) KB0015.proved) Eq.refl Eq.refl

  p7 : CCX02 • X0 • SWAP12 • CX12 ≈ CCX02 • X0 • CX12 • CX21
  p7 = by-assoc-and (under (CCX02 • X0) (ε) KB0061.proved) Eq.refl Eq.refl

  p8 : CCX02 • SWAP12 • X0 • CX12 ≈ CCX02 • X0 • CX12 • CX21
  p8 = trans p6 (trans p7 (refl))

  p9 : X0 • CCX02 • SWAP12 ≈ CCX02 • X0 • CX12 • CX21
  p9 = trans (sym p5) (trans p2 p8)

  p10 : CCX02 • X0 • CX12 • CX21 ≈ X0 • CCX02 • SWAP12
  p10 = sym p9

  proved : CCX02 • X0 • CX12 • CX21 ≈ X0 • CCX02 • SWAP12
  proved = p10

module KB0562 where

  p0 : SWAP01 • CCX02 • X2 • CX01 ≈ SWAP01 • X2 • CCX02
  p0 = by-assoc-and (under (SWAP01) (ε) KB0188.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CCX02 • X2 • CX01 ≈ CCX12 • SWAP01 • X2 • CX01
  p1 = by-assoc-and (under (ε) (X2 • CX01) KB0090.proved) Eq.refl Eq.refl

  p2 : SWAP01 • X2 • CCX02 ≈ CCX12 • SWAP01 • X2 • CX01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • X2 • CCX02 ≈ X2 • SWAP01 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0016.proved) Eq.refl Eq.refl

  p4 : X2 • SWAP01 • CCX02 ≈ X2 • CCX12 • SWAP01
  p4 = by-assoc-and (under (X2) (ε) KB0090.proved) Eq.refl Eq.refl

  p5 : SWAP01 • X2 • CCX02 ≈ X2 • CCX12 • SWAP01
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX12 • SWAP01 • X2 • CX01 ≈ CCX12 • X2 • SWAP01 • CX01
  p6 = by-assoc-and (under (CCX12) (CX01) KB0016.proved) Eq.refl Eq.refl

  p7 : CCX12 • X2 • SWAP01 • CX01 ≈ CCX12 • X2 • CX01 • CX10
  p7 = by-assoc-and (under (CCX12 • X2) (ε) KB0063.proved) Eq.refl Eq.refl

  p8 : CCX12 • SWAP01 • X2 • CX01 ≈ CCX12 • X2 • CX01 • CX10
  p8 = trans p6 (trans p7 (refl))

  p9 : X2 • CCX12 • SWAP01 ≈ CCX12 • X2 • CX01 • CX10
  p9 = trans (sym p5) (trans p2 p8)

  p10 : CCX12 • X2 • CX01 • CX10 ≈ X2 • CCX12 • SWAP01
  p10 = sym p9

  proved : CCX12 • X2 • CX01 • CX10 ≈ X2 • CCX12 • SWAP01
  proved = p10

module KB0596 where

  p0 : CCX02 • X0 • X1 • CX10 ≈ X1 • CCX02 • X0 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0231.proved) Eq.refl Eq.refl

  p1 : CCX02 • X0 • X1 • CX10 ≈ CCX02 • CX10 • X1
  p1 = by-assoc-and (under (CCX02) (ε) KB0143.proved) Eq.refl Eq.refl

  p2 : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
  p2 = trans (sym p0) p1

  p3 : X1 • CCX02 • X0 • CX10 ≈ X1 • CCX02 • X0 • CX10
  p3 = refl

  p4 : CCX02 • CX10 • X1 ≈ CCX02 • CX10 • X1
  p4 = refl

  p5 : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CCX02 • X0 • CX10 ≈ CCX02 • CX10 • X1
  proved = p5
