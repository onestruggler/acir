{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B012 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0009 ; module KB0010 ; module KB0011 ; module KB0026 ; module KB0028 ; module KB0029 ; module KB0035 ; module KB0036 ; module KB0037 ; module KB0039 ; module KB0046 ; module KB0118 ; module KB0120 ; module KB0153 ; module KB0164 ; module KB0191 ; module KB0215 ; module KB0216)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0002 ; module KB0020 ; module KB0022 ; module KB0025 ; module KB0030 ; module KB0038 ; module KB0086 ; module KB0103 ; module KB0119 ; module KB0165)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0004 ; module KB0016 ; module KB0019 ; module KB0032 ; module KB0042 ; module KB0045 ; module KB0074 ; module KB0091 ; module KB0096 ; module KB0097 ; module KB0221)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0088 ; module KB0154 ; module KB0168 ; module KB0315 ; module KB0366 ; module KB0412 ; module KB0493 ; module KB0783 ; module KB0910 ; module KB1419)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB2681 ; module KB2682 ; module KB3098)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0001 ; module KB0024 ; module KB0080 ; module KB0092 ; module KB0132 ; module KB0134 ; module KB0138 ; module KB0260)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0291 ; module KB0481)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0163 ; module KB0355 ; module KB0357 ; module KB0777 ; module KB1658 ; module KB1661 ; module KB2829 ; module KB3094 ; module KB3579)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module symmetry_CX_i)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module symmetry_X_c)

module decodeSWAP01 where

  p0 : SWAP01 ≈ SWAP01
  p0 = refl

  p1 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0481.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p2 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p3 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p3 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0118.proved) Eq.refl Eq.refl

  p4 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p5 = by-assoc-and (under (X2 • CX10) (X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB3094.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p6 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p7 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p8 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p8 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB3579.proved) Eq.refl Eq.refl

  p9 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p9 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0357.proved) Eq.refl Eq.refl

  p10 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p10 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0044.proved) Eq.refl Eq.refl

  p11 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p11 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p12 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p12 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p13 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p13 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0355.proved) Eq.refl Eq.refl

  p14 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p14 = by-assoc-and (under (CX10) (CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB2829.proved) Eq.refl Eq.refl

  p15 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p15 = by-assoc-and (under (ε) (CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB1661.proved) Eq.refl Eq.refl

  p16 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p16 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p17 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (CX02) (CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB1658.proved) Eq.refl Eq.refl

  p18 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0025.proved) Eq.refl Eq.refl

  p19 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (CX01 • CX02 • CCX12) (X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0163.proved) Eq.refl Eq.refl

  p20 : CX01 • CX02 • CCX12 • CX01 • CX02 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • CX02) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0153.proved) Eq.refl Eq.refl

  p21 : CX01 • CX02 • CCX12 • CX01 • CX02 • CX12 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0164.proved) Eq.refl Eq.refl

  p22 : CX01 • CX02 • CCX12 • CX12 • CX01 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CCX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p22 = by-assoc-and (under (CX01) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB2682.proved) Eq.refl Eq.refl

  p23 : CX01 • CX10 • CCX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CCX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p23 = by-assoc-and (under (CX01 • CX10 • CCX01 • CCX12) (CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0035.proved) Eq.refl Eq.refl

  p24 : CX01 • CX10 • CCX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CX02 • CCX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p24 = by-assoc-and (under (CX01 • CX10) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB3098.proved) Eq.refl Eq.refl

  p25 : CX01 • CX10 • CX02 • CCX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p25 = by-assoc-and (under (CX01) (X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0315.proved) Eq.refl Eq.refl

  p26 : CX01 • CX02 • CCX12 • CX12 • X1 • CX01 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX12 • X1 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p26 = by-assoc-and (under (CX01 • CX02 • CCX12) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0412.proved) Eq.refl Eq.refl

  p27 : CX01 • CX02 • CCX12 • CX01 • CX12 • X1 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p27 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • CX12) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0003.proved) Eq.refl Eq.refl

  p28 : CX01 • CX02 • CCX12 • CX01 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p28 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p29 : CX01 • CX02 • CCX12 • CX01 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p29 = by-assoc-and (under (CX01 • CX02 • CCX12 • CX01 • X0) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p30 : CX01 • CX02 • CCX12 • CX01 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p30 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0221.proved) Eq.refl Eq.refl

  p31 : CX01 • CX02 • CCX12 • X2 • CX01 • X0 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X0 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p31 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0910.proved) Eq.refl Eq.refl

  p32 : CX01 • CX02 • CCX12 • X0 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • X0 • CCX12 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p32 = by-assoc-and (under (CX01 • CX02) (CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0046.proved) Eq.refl Eq.refl

  p33 : CX01 • CX02 • X0 • CCX12 • CX01 • CX12 • X1 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • X0 • CCX12 • CX01 • X0 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p33 = by-assoc-and (under (CX01 • CX02 • X0 • CCX12 • CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0783.proved) Eq.refl Eq.refl

  p34 : CX01 • CX02 • X0 • CCX12 • CX01 • X0 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X1 • CX01 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p34 = by-assoc-and (under (CX01 • CX02) (X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0493.proved) Eq.refl Eq.refl

  p35 : CX01 • CX02 • CCX12 • X1 • CX01 • X1 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X1 • X1 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p35 = by-assoc-and (under (CX01 • CX02 • CCX12 • X1) (X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0035.proved) Eq.refl Eq.refl

  p36 : CX01 • CX02 • CCX12 • X1 • X1 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p36 = by-assoc-and (under (CX01 • CX02 • CCX12) (CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0003.proved) Eq.refl Eq.refl

  p37 : CX01 • CX02 • CCX12 • CX01 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX02 • CCX12 • X2 • CX01 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p37 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0022.proved) Eq.refl Eq.refl

  p38 : CX01 • CX02 • CCX12 • X2 • CX01 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p38 = by-assoc-and (under (CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB2681.proved) Eq.refl Eq.refl

  p39 : CX01 • CCX01 • CCX12 • X2 • CX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX02 • X2 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0
  p39 = by-assoc-and (under (CX01 • CCX01) (CCX12 • X0 • CCX01 • X2 • X0) KB1419.proved) Eq.refl Eq.refl

  p40 : CX01 • CCX01 • CCX02 • X2 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • CCX02 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0
  p40 = by-assoc-and (under (ε) (SWAP01 • CCX12 • X0 • CCX01 • X2 • X0) KB0777.proved) Eq.refl Eq.refl

  p41 : X2 • CX02 • CCX01 • CCX02 • SWAP01 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • CCX02 • CCX02 • SWAP01 • X0 • CCX01 • X2 • X0
  p41 = by-assoc-and (under (X2 • CX02 • CCX01 • CCX02) (X0 • CCX01 • X2 • X0) KB0091.proved) Eq.refl Eq.refl

  p42 : X2 • CX02 • CCX01 • CCX02 • CCX02 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • SWAP01 • X0 • CCX01 • X2 • X0
  p42 = by-assoc-and (under (X2 • CX02 • CCX01) (SWAP01 • X0 • CCX01 • X2 • X0) KB0010.proved) Eq.refl Eq.refl

  p43 : X2 • CX02 • CCX01 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX02 • CCX01 • X1 • SWAP01 • CCX01 • X2 • X0
  p43 = by-assoc-and (under (X2 • CX02 • CCX01) (CCX01 • X2 • X0) KB0097.proved) Eq.refl Eq.refl

  p44 : X2 • CX02 • CCX01 • X1 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • X1 • CCX01 • SWAP01 • CCX01 • X2 • X0
  p44 = by-assoc-and (under (X2) (SWAP01 • CCX01 • X2 • X0) KB0120.proved) Eq.refl Eq.refl

  p45 : X2 • X1 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X1 • X2 • CCX01 • SWAP01 • CCX01 • X2 • X0
  p45 = by-assoc-and (under (ε) (CCX01 • SWAP01 • CCX01 • X2 • X0) KB0019.proved) Eq.refl Eq.refl

  p46 : X1 • X2 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X1 • X2 • CCX01 • CCX01 • SWAP01 • X2 • X0
  p46 = by-assoc-and (under (X1 • X2 • CCX01) (X2 • X0) KB0074.proved) Eq.refl Eq.refl

  p47 : X1 • X2 • CCX01 • CCX01 • SWAP01 • X2 • X0 ≈ X1 • X2 • SWAP01 • X2 • X0
  p47 = by-assoc-and (under (X1 • X2) (SWAP01 • X2 • X0) KB0011.proved) Eq.refl Eq.refl

  p48 : X1 • X2 • SWAP01 • X2 • X0 ≈ X1 • X2 • X2 • SWAP01 • X0
  p48 = by-assoc-and (under (X1 • X2) (X0) KB0016.proved) Eq.refl Eq.refl

  p49 : X1 • X2 • X2 • SWAP01 • X0 ≈ X1 • SWAP01 • X0
  p49 = by-assoc-and (under (X1) (SWAP01 • X0) KB0004.proved) Eq.refl Eq.refl

  p50 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
  p50 = by-assoc-and (under (X1) (ε) KB0097.proved) Eq.refl Eq.refl

  p51 : X1 • X1 • SWAP01 ≈ SWAP01
  p51 = by-assoc-and (under (ε) (SWAP01) KB0003.proved) Eq.refl Eq.refl

  p52 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ SWAP01
  p52 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (refl)))))))))))))))))))))))))))))))))))))))))))))))))))

  proved : SWAP01 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  proved = trans p0 (sym p52)

module KB0094 where

  p0 : SWAP02 • X0 • SWAP02 • SWAP02 ≈ X2 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0092.proved) Eq.refl Eq.refl

  p1 : SWAP02 • X0 • SWAP02 • SWAP02 ≈ SWAP02 • X0
  p1 = by-assoc-and (under (SWAP02 • X0) (ε) KB0002.proved) Eq.refl Eq.refl

  p2 : X2 • SWAP02 ≈ SWAP02 • X0
  p2 = trans (sym p0) p1

  p3 : X2 • SWAP02 ≈ X2 • SWAP02
  p3 = refl

  p4 : SWAP02 • X0 ≈ SWAP02 • X0
  p4 = refl

  p5 : X2 • SWAP02 ≈ SWAP02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP02 • X0 ≈ X2 • SWAP02
  p6 = sym p5

  proved : SWAP02 • X0 ≈ X2 • SWAP02
  proved = p6

module KB0105 where

  p0 : SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ CCX01 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0103.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • CCX12
  p1 = by-assoc-and (under (SWAP02 • CCX12) (ε) KB0002.proved) Eq.refl Eq.refl

  p2 : CCX01 • SWAP02 ≈ SWAP02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • SWAP02 ≈ CCX01 • SWAP02
  p3 = refl

  p4 : SWAP02 • CCX12 ≈ SWAP02 • CCX12
  p4 = refl

  p5 : CCX01 • SWAP02 ≈ SWAP02 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP02 • CCX12 ≈ CCX01 • SWAP02
  p6 = sym p5

  proved : SWAP02 • CCX12 ≈ CCX01 • SWAP02
  proved = p6

module KB0054 where

  p0 : X2 ≈ SWAP12 • X1 • SWAP12
  p0 = symmetry_X_c.proved

  p1 : X2 ≈ X2
  p1 = refl

  p2 : SWAP12 • X1 • SWAP12 ≈ SWAP12 • X1 • SWAP12
  p2 = refl

  p3 : X2 ≈ SWAP12 • X1 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • X1 • SWAP12 ≈ X2
  p4 = sym p3

  proved : SWAP12 • X1 • SWAP12 ≈ X2
  proved = p4

module KB0055 where

  p0 : SWAP12 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • X2
  p0 = by-assoc-and (under (SWAP12) (ε) KB0054.proved) Eq.refl Eq.refl

  p1 : SWAP12 • SWAP12 • X1 • SWAP12 ≈ X1 • SWAP12
  p1 = by-assoc-and (under (ε) (X1 • SWAP12) KB0001.proved) Eq.refl Eq.refl

  p2 : SWAP12 • X2 ≈ X1 • SWAP12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • X2 ≈ SWAP12 • X2
  p3 = refl

  p4 : X1 • SWAP12 ≈ X1 • SWAP12
  p4 = refl

  p5 : SWAP12 • X2 ≈ X1 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP12 • X2 ≈ X1 • SWAP12
  proved = p5

module KB0252 where

  p0 : CX21 • CX12 • X2 ≈ CX12 • SWAP12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0080.proved) Eq.refl Eq.refl

  p1 : CX21 • CX12 • X2 ≈ CX21 • X2 • CX12
  p1 = by-assoc-and (under (CX21) (ε) KB0036.proved) Eq.refl Eq.refl

  p2 : CX12 • SWAP12 • X2 ≈ CX21 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • SWAP12 • X2 ≈ CX12 • X1 • SWAP12
  p3 = by-assoc-and (under (CX12) (ε) KB0055.proved) Eq.refl Eq.refl

  p4 : CX12 • SWAP12 • X2 ≈ CX12 • X1 • SWAP12
  p4 = trans p3 (refl)

  p5 : CX21 • X2 • CX12 ≈ CX21 • X2 • CX12
  p5 = refl

  p6 : CX12 • X1 • SWAP12 ≈ CX21 • X2 • CX12
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX21 • X2 • CX12 ≈ CX12 • X1 • SWAP12
  p7 = sym p6

  proved : CX21 • X2 • CX12 ≈ CX12 • X1 • SWAP12
  proved = p7

module KB0067 where

  p0 : CX21 ≈ SWAP02 • CX01 • SWAP02
  p0 = symmetry_CX_i.proved

  p1 : CX21 ≈ CX21
  p1 = refl

  p2 : SWAP02 • CX01 • SWAP02 ≈ SWAP02 • CX01 • SWAP02
  p2 = refl

  p3 : CX21 ≈ SWAP02 • CX01 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • CX01 • SWAP02 ≈ CX21
  p4 = sym p3

  proved : SWAP02 • CX01 • SWAP02 ≈ CX21
  proved = p4

module KB0069 where

  p0 : SWAP02 • CX01 • SWAP02 • SWAP02 ≈ CX21 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0067.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX01 • SWAP02 • SWAP02 ≈ SWAP02 • CX01
  p1 = by-assoc-and (under (SWAP02 • CX01) (ε) KB0002.proved) Eq.refl Eq.refl

  p2 : CX21 • SWAP02 ≈ SWAP02 • CX01
  p2 = trans (sym p0) p1

  p3 : CX21 • SWAP02 ≈ CX21 • SWAP02
  p3 = refl

  p4 : SWAP02 • CX01 ≈ SWAP02 • CX01
  p4 = refl

  p5 : CX21 • SWAP02 ≈ SWAP02 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP02 • CX01 ≈ CX21 • SWAP02
  p6 = sym p5

  proved : SWAP02 • CX01 ≈ CX21 • SWAP02
  proved = p6

module KB0259 where

  p0 : SWAP02 • CX02 • CX01 ≈ CX02 • CX20 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0086.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX02 • CX01 ≈ SWAP02 • CX01 • CX02
  p1 = by-assoc-and (under (SWAP02) (ε) KB0025.proved) Eq.refl Eq.refl

  p2 : CX02 • CX20 • CX01 ≈ SWAP02 • CX01 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX20 • CX01 ≈ CX02 • CX20 • CX01
  p3 = refl

  p4 : SWAP02 • CX01 • CX02 ≈ CX21 • SWAP02 • CX02
  p4 = by-assoc-and (under (ε) (CX02) KB0069.proved) Eq.refl Eq.refl

  p5 : CX21 • SWAP02 • CX02 ≈ CX21 • CX02 • CX20
  p5 = by-assoc-and (under (CX21) (ε) KB0086.proved) Eq.refl Eq.refl

  p6 : SWAP02 • CX01 • CX02 ≈ CX21 • CX02 • CX20
  p6 = trans p4 (trans p5 (refl))

  p7 : CX02 • CX20 • CX01 ≈ CX21 • CX02 • CX20
  p7 = trans (sym p3) (trans p2 p6)

  p8 : CX21 • CX02 • CX20 ≈ CX02 • CX20 • CX01
  p8 = sym p7

  proved : CX21 • CX02 • CX20 ≈ CX02 • CX20 • CX01
  proved = p8

module KB0170 where

  p0 : CX20 • CX20 • CCX12 • X1 ≈ CX20 • X1 • CCX12
  p0 = by-assoc-and (under (CX20) (ε) KB0132.proved) Eq.refl Eq.refl

  p1 : CX20 • CX20 • CCX12 • X1 ≈ CCX12 • X1
  p1 = by-assoc-and (under (ε) (CCX12 • X1) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • X1 • CCX12 ≈ CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX20 • X1 • CCX12 ≈ X1 • CX20 • CCX12
  p3 = by-assoc-and (under (ε) (CCX12) KB0024.proved) Eq.refl Eq.refl

  p4 : CX20 • X1 • CCX12 ≈ X1 • CX20 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • X1 ≈ CCX12 • X1
  p5 = refl

  p6 : X1 • CX20 • CCX12 ≈ CCX12 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : X1 • CX20 • CCX12 ≈ CCX12 • X1
  proved = p6

module KB0288 where

  p0 : X1 • CX20 • CCX12 • CX21 ≈ CCX12 • X1 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0170.proved) Eq.refl Eq.refl

  p1 : X1 • CX20 • CCX12 • CX21 ≈ X1 • CX21 • CCX12
  p1 = by-assoc-and (under (X1) (ε) KB0138.proved) Eq.refl Eq.refl

  p2 : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • X1 • CX21 ≈ CCX12 • X1 • CX21
  p3 = refl

  p4 : X1 • CX21 • CCX12 ≈ X1 • CX21 • CCX12
  p4 = refl

  p5 : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • X1 • CX21 ≈ X1 • CX21 • CCX12
  proved = p5

module KB0371 where

  p0 : CX21 • CX01 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0119.proved) Eq.refl Eq.refl

  p1 : CX21 • CX01 • CCX02 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX02) KB0030.proved) Eq.refl Eq.refl

  p2 : CX21 • CX02 • CCX02 ≈ CX01 • CX21 • CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CX02 • CCX02 ≈ CX21 • CX02 • CCX02
  p3 = refl

  p4 : CX01 • CX21 • CCX02 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
  p4 = refl

  p5 : CX21 • CX02 • CCX02 ≈ CX01 • CX21 • CCX02 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
  p6 = sym p5

  proved : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
  proved = p6

module KB0429 where

  p0 : CCX02 • CX01 • CX21 • CX02 ≈ CCX02 • CX02 • CX21
  p0 = by-assoc-and (under (CCX02) (ε) KB0134.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX01 • CX21 • CX02 ≈ CX01 • CCX02 • CX21 • CX02
  p1 = by-assoc-and (under (ε) (CX21 • CX02) KB0038.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX02 • CX21 ≈ CX01 • CCX02 • CX21 • CX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX02 • CX21 ≈ CCX02 • CX02 • CX21
  p3 = refl

  p4 : CX01 • CCX02 • CX21 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
  p4 = by-assoc-and (under (CX01) (CX02) KB0039.proved) Eq.refl Eq.refl

  p5 : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
  p5 = by-assoc-and (under (ε) (ε) KB0371.proved) Eq.refl Eq.refl

  p6 : CX01 • CCX02 • CX21 • CX02 ≈ CX21 • CX02 • CCX02
  p6 = trans p4 (trans p5 (refl))

  p7 : CCX02 • CX02 • CX21 ≈ CX21 • CX02 • CCX02
  p7 = trans (sym p3) (trans p2 p6)

  proved : CCX02 • CX02 • CX21 ≈ CX21 • CX02 • CCX02
  proved = p7

module KB0487 where

  p0 : CCX01 • X2 • CCX02 • X2 ≈ CCX01 • CX01 • CCX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0154.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • CCX02 • X2 ≈ X2 • CCX01 • CCX02 • X2
  p1 = by-assoc-and (under (ε) (CCX02 • X2) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CCX02 ≈ X2 • CCX01 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CCX02 ≈ CCX01 • CX01 • CCX02
  p3 = refl

  p4 : X2 • CCX01 • CCX02 • X2 ≈ X2 • CCX01 • CCX02 • X2
  p4 = refl

  p5 : CCX01 • CX01 • CCX02 ≈ X2 • CCX01 • CCX02 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX01 • CCX02 • X2 ≈ CCX01 • CX01 • CCX02
  p6 = sym p5

  proved : X2 • CCX01 • CCX02 • X2 ≈ CCX01 • CX01 • CCX02
  proved = p6

module KB0503 where

  p0 : CX12 • CX01 • CX12 • X0 ≈ CX01 • CX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0163.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX12 • X0 ≈ CX12 • CX01 • X0 • CX12
  p1 = by-assoc-and (under (CX12 • CX01) (ε) KB0045.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • X0 ≈ CX12 • CX01 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • X0 ≈ CX01 • CX02 • X0
  p3 = refl

  p4 : CX12 • CX01 • X0 • CX12 ≈ CX12 • CX01 • X0 • CX12
  p4 = refl

  p5 : CX01 • CX02 • X0 ≈ CX12 • CX01 • X0 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CX01 • X0 • CX12 ≈ CX01 • CX02 • X0
  p6 = sym p5

  proved : CX12 • CX01 • X0 • CX12 ≈ CX01 • CX02 • X0
  proved = p6

module KB0512 where

  p0 : CX10 • X0 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
  p0 = by-assoc-and (under (CX10) (ε) KB0165.proved) Eq.refl Eq.refl

  p1 : CX10 • X0 • CX21 • CCX02 ≈ X0 • CX10 • CX21 • CCX02
  p1 = by-assoc-and (under (ε) (CX21 • CCX02) KB0047.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • X0 ≈ X0 • CX10 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • X0 ≈ CX10 • CCX02 • X0
  p3 = refl

  p4 : X0 • CX10 • CX21 • CCX02 ≈ X0 • CX10 • CX21 • CCX02
  p4 = refl

  p5 : CX10 • CCX02 • X0 ≈ X0 • CX10 • CX21 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CX10 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
  p6 = sym p5

  proved : X0 • CX10 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
  proved = p6

module KB0916 where

  p0 : CX02 • X0 • X2 • CX10 • CCX12 ≈ X0 • CX02 • CX10 • CCX12
  p0 = by-assoc-and (under (ε) (CX10 • CCX12) KB0191.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • X2 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
  p1 = by-assoc-and (under (CX02 • X0) (ε) KB0168.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : X0 • CX02 • CX10 • CCX12 ≈ X0 • CX02 • CX10 • CCX12
  p3 = refl

  p4 : CX02 • X0 • CCX12 • X2 ≈ CX02 • X0 • CCX12 • X2
  p4 = refl

  p5 : X0 • CX02 • CX10 • CCX12 ≈ CX02 • X0 • CCX12 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • X0 • CCX12 • X2 ≈ X0 • CX02 • CX10 • CCX12
  p6 = sym p5

  proved : CX02 • X0 • CCX12 • X2 ≈ X0 • CX02 • CX10 • CCX12
  proved = p6

module KB0965 where

  p0 : CCX02 • CCX12 • CCX02 • X1 ≈ CX01 • CCX12 • CX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0216.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX12 • CCX02 • X1 ≈ CCX02 • CCX12 • X1 • CCX02
  p1 = by-assoc-and (under (CCX02 • CCX12) (ε) KB0028.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CX01 • X1 ≈ CCX02 • CCX12 • X1 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CX01 • X1 ≈ CX01 • CCX12 • X1 • CX01
  p3 = by-assoc-and (under (CX01 • CCX12) (ε) KB0035.proved) Eq.refl Eq.refl

  p4 : CX01 • CCX12 • CX01 • X1 ≈ CX01 • CCX12 • X1 • CX01
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX12 • X1 • CCX02 ≈ CCX02 • CCX12 • X1 • CCX02
  p5 = refl

  p6 : CX01 • CCX12 • X1 • CX01 ≈ CCX02 • CCX12 • X1 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX02 • CCX12 • X1 • CCX02 ≈ CX01 • CCX12 • X1 • CX01
  p7 = sym p6

  proved : CCX02 • CCX12 • X1 • CCX02 ≈ CX01 • CCX12 • X1 • CX01
  proved = p7

module KB0248 where

  p0 : CX10 • SWAP01 • CCX01 ≈ CX10 • CCX01 • SWAP01
  p0 = by-assoc-and (under (CX10) (ε) KB0074.proved) Eq.refl Eq.refl

  p1 : CX10 • SWAP01 • CCX01 ≈ CX01 • CX10 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01) KB0042.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • SWAP01 ≈ CX10 • CCX01 • SWAP01
  p3 = refl

  p4 : CX01 • CX10 • CCX01 ≈ CX01 • CX10 • CCX01
  p4 = refl

  p5 : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CCX01 • SWAP01 ≈ CX01 • CX10 • CCX01
  proved = p5

module KB1050 where

  p0 : CX10 • CCX01 • SWAP01 • X1 ≈ CX01 • CX10 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0248.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX01 • SWAP01 • X1 ≈ CX10 • CCX01 • X0 • SWAP01
  p1 = by-assoc-and (under (CX10 • CCX01) (ε) KB0096.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CCX01 • X1 ≈ CX10 • CCX01 • X0 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CCX01 • X1 ≈ CX01 • CX10 • CCX01 • X1
  p3 = refl

  p4 : CX10 • CCX01 • X0 • SWAP01 ≈ X0 • CCX01 • CX10 • SWAP01
  p4 = by-assoc-and (under (ε) (SWAP01) KB0366.proved) Eq.refl Eq.refl

  p5 : X0 • CCX01 • CX10 • SWAP01 ≈ X0 • CCX01 • CX01 • CX10
  p5 = by-assoc-and (under (X0 • CCX01) (ε) KB0042.proved) Eq.refl Eq.refl

  p6 : CX10 • CCX01 • X0 • SWAP01 ≈ X0 • CCX01 • CX01 • CX10
  p6 = trans p4 (trans p5 (refl))

  p7 : CX01 • CX10 • CCX01 • X1 ≈ X0 • CCX01 • CX01 • CX10
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX01 • CX10 • CCX01 • X1 ≈ X0 • CCX01 • CX01 • CX10
  proved = p7

module KB1097 where

  p0 : CCX01 • CX02 • CX20 • X2 ≈ CCX01 • X0 • CX02 • CX20
  p0 = by-assoc-and (under (CCX01) (ε) KB0260.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX02 • CX20 • X2 ≈ CX02 • CCX01 • CX20 • X2
  p1 = by-assoc-and (under (ε) (CX20 • X2) KB0037.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX02 • CX20 ≈ CCX01 • X0 • CX02 • CX20
  p3 = refl

  p4 : CX02 • CCX01 • CX20 • X2 ≈ CX02 • CCX01 • CX20 • X2
  p4 = refl

  p5 : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2
  proved = p5

module KB0262 where

  p0 : CCX12 • CX10 • CX01 ≈ CCX12 • CX01 • SWAP01
  p0 = by-assoc-and (under (CCX12) (ε) KB0088.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX10 • CX01 ≈ CX10 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CX01) KB0032.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX01 • SWAP01 ≈ CCX12 • CX01 • SWAP01
  p3 = refl

  p4 : CX10 • CCX12 • CX01 ≈ CX10 • CCX12 • CX01
  p4 = refl

  p5 : CCX12 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01
  proved = p5

module KB1107 where

  p0 : CCX12 • CX01 • SWAP01 • X0 ≈ CX10 • CCX12 • CX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0262.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX01 • SWAP01 • X0 ≈ CCX12 • CX01 • X1 • SWAP01
  p1 = by-assoc-and (under (CCX12 • CX01) (ε) KB0097.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CX01 • X0 ≈ CCX12 • CX01 • X1 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CX01 • X0 ≈ CX10 • CCX12 • CX01 • X0
  p3 = refl

  p4 : CCX12 • CX01 • X1 • SWAP01 ≈ CCX12 • X1 • CX01 • SWAP01
  p4 = by-assoc-and (under (CCX12) (SWAP01) KB0035.proved) Eq.refl Eq.refl

  p5 : CCX12 • CX01 • X1 • SWAP01 ≈ CCX12 • X1 • CX01 • SWAP01
  p5 = trans p4 (refl)

  p6 : CX10 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01 • SWAP01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX12 • X1 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01 • X0
  p7 = sym p6

  proved : CCX12 • X1 • CX01 • SWAP01 ≈ CX10 • CCX12 • CX01 • X0
  proved = p7

module KB1605 where

  p0 : CCX01 • CX21 • CX02 • X0 • X2 ≈ CX01 • CCX01 • CX21 • X0 • X2
  p0 = by-assoc-and (under (ε) (X0 • X2) KB0291.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CX02 • X0 • X2 ≈ CCX01 • CX21 • X0 • CX02
  p1 = by-assoc-and (under (CCX01 • CX21) (ε) KB0191.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CCX01 • CX21 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CX01 • CCX01 • X0 • CX21 • X2
  p3 = by-assoc-and (under (CX01 • CCX01) (X2) KB0020.proved) Eq.refl Eq.refl

  p4 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CX01 • CCX01 • X0 • CX21 • X2
  p4 = trans p3 (refl)

  p5 : CCX01 • CX21 • X0 • CX02 ≈ CCX01 • X0 • CX21 • CX02
  p5 = by-assoc-and (under (CCX01) (CX02) KB0020.proved) Eq.refl Eq.refl

  p6 : CCX01 • CX21 • X0 • CX02 ≈ CCX01 • X0 • CX21 • CX02
  p6 = trans p5 (refl)

  p7 : CX01 • CCX01 • X0 • CX21 • X2 ≈ CCX01 • X0 • CX21 • CX02
  p7 = trans (sym p4) (trans p2 p6)

  proved : CX01 • CCX01 • X0 • CX21 • X2 ≈ CCX01 • X0 • CX21 • CX02
  proved = p7
