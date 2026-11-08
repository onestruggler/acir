{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B023 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; SWAP01 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0011 ; module KB0012 ; module KB0023 ; module KB0026 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0033 ; module KB0035 ; module KB0118 ; module KB0153 ; module KB0186 ; module KB0215 ; module KB0219 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0022 ; module KB0137 ; module KB0211 ; module KB0282)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0004 ; module KB0018 ; module KB0045 ; module KB0074 ; module KB0090 ; module KB0097 ; module KB0150 ; module KB0161 ; module KB0214 ; module KB0221 ; module KB0435)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0115 ; module KB0140 ; module KB0280 ; module KB0310 ; module KB0366)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB0623)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0223 ; module KB0416 ; module KB0423 ; module KB0480)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0112)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0231 ; module KB0481)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0285 ; module KB0357)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB1107)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0326)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0314 ; module KB0331 ; module KB0562 ; module KB0596)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0751 ; module KB0788 ; module KB0805 ; module KB0836 ; module KB0963)

module braid3 where

  p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0481.proved) Eq.refl Eq.refl

  p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0118.proved) Eq.refl Eq.refl

  p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p5 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p6 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0366.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p7 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p8 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p8 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p9 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p9 = by-assoc-and (under (X2 • CX10) (CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0963.proved) Eq.refl Eq.refl

  p10 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p10 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p11 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX10 • X1 • CX12 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p11 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0357.proved) Eq.refl Eq.refl

  p12 : X2 • CX10 • CX12 • CCX02 • CX10 • X1 • CX12 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X1 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p12 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0805.proved) Eq.refl Eq.refl

  p13 : X2 • CX10 • CX12 • CCX02 • X0 • X1 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • X1 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p13 = by-assoc-and (under (X2 • CX10 • CX12) (CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0231.proved) Eq.refl Eq.refl

  p14 : X2 • CX10 • CX12 • X1 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p14 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0357.proved) Eq.refl Eq.refl

  p15 : CX10 • X1 • CX12 • CCX02 • X0 • CCX01 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • CCX02 • X0 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p15 = by-assoc-and (under (CX10 • X1) (CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0623.proved) Eq.refl Eq.refl

  p16 : CX10 • X1 • CCX01 • CCX02 • X0 • CX10 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • CCX02 • X1 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p16 = by-assoc-and (under (CX10 • X1 • CCX01 • CCX02) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0115.proved) Eq.refl Eq.refl

  p17 : CX10 • X1 • CCX01 • CCX02 • X1 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • X1 • CCX01 • X1 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (CX10 • X1 • CCX01) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0028.proved) Eq.refl Eq.refl

  p18 : CX10 • X1 • CCX01 • X1 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX10 • CX02 • CCX01 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (CX10) (CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0150.proved) Eq.refl Eq.refl

  p19 : CX10 • CX02 • CCX01 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX01 • CX10 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (ε) (CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0314.proved) Eq.refl Eq.refl

  p20 : CX02 • CCX01 • CX10 • CCX02 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX02 • CCX01 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (CX02 • CCX01) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0219.proved) Eq.refl Eq.refl

  p21 : CX02 • CCX01 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0137.proved) Eq.refl Eq.refl

  p22 : CX01 • CCX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p22 = by-assoc-and (under (CX01 • CCX01 • CCX12) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0221.proved) Eq.refl Eq.refl

  p23 : CX01 • CCX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p23 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0153.proved) Eq.refl Eq.refl

  p24 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p24 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01) (X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p25 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • CCX12 • X2 • CX01 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p25 = by-assoc-and (under (CX01 • CCX01 • CCX12 • X2 • CX01) (CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0118.proved) Eq.refl Eq.refl

  p26 : CX01 • CCX01 • CCX12 • X2 • CX01 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX01 • X2 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p26 = by-assoc-and (under (CX01 • CCX01) (CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0562.proved) Eq.refl Eq.refl

  p27 : CX01 • CCX01 • X2 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX01 • X2 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p27 = by-assoc-and (under (CX01) (CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p28 : CX01 • X2 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p28 = by-assoc-and (under (ε) (CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0022.proved) Eq.refl Eq.refl

  p29 : X2 • CX01 • CCX01 • CCX12 • SWAP01 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX01 • CCX12 • CCX01 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p29 = by-assoc-and (under (X2 • CX01 • CCX01 • CCX12) (CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0074.proved) Eq.refl Eq.refl

  p30 : X2 • CX01 • CCX01 • CCX12 • CCX01 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX02 • CCX12 • CX02 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p30 = by-assoc-and (under (X2 • CX01) (SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0211.proved) Eq.refl Eq.refl

  p31 : X2 • CX01 • CX02 • CCX12 • CX02 • SWAP01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX02 • CCX12 • CX02 • CCX12 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0
  p31 = by-assoc-and (under (X2 • CX01 • CX02 • CCX12 • CX02) (CX10 • X0 • CCX01 • X2 • X0) KB0090.proved) Eq.refl Eq.refl

  p32 : X2 • CX01 • CX02 • CCX12 • CX02 • CCX12 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0
  p32 = by-assoc-and (under (X2 • CX01) (SWAP01 • CX10 • X0 • CCX01 • X2 • X0) KB0326.proved) Eq.refl Eq.refl

  p33 : X2 • CX01 • CCX12 • CCX01 • SWAP01 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • CX01 • SWAP01 • X0 • CCX01 • X2 • X0
  p33 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01) (X0 • CCX01 • X2 • X0) KB0112.proved) Eq.refl Eq.refl

  p34 : X2 • CX01 • CCX12 • CCX01 • CX01 • SWAP01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • CX01 • X1 • SWAP01 • CCX01 • X2 • X0
  p34 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01 • CX01) (CCX01 • X2 • X0) KB0097.proved) Eq.refl Eq.refl

  p35 : X2 • CX01 • CCX12 • CCX01 • CX01 • X1 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CCX01 • X1 • CX01 • SWAP01 • CCX01 • X2 • X0
  p35 = by-assoc-and (under (X2 • CX01 • CCX12 • CCX01) (SWAP01 • CCX01 • X2 • X0) KB0035.proved) Eq.refl Eq.refl

  p36 : X2 • CX01 • CCX12 • CCX01 • X1 • CX01 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • SWAP01 • CCX01 • X2 • X0
  p36 = by-assoc-and (under (X2 • CX01 • CCX12) (SWAP01 • CCX01 • X2 • X0) KB0282.proved) Eq.refl Eq.refl

  p37 : X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • SWAP01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • SWAP01 • X2 • X0
  p37 = by-assoc-and (under (X2 • CX01 • CCX12 • X1 • CX01 • CCX01) (X2 • X0) KB0074.proved) Eq.refl Eq.refl

  p38 : X2 • CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • SWAP01 • X2 • X0 ≈ X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • X2 • X0
  p38 = by-assoc-and (under (X2 • CX01 • CCX12 • X1 • CX01) (SWAP01 • X2 • X0) KB0011.proved) Eq.refl Eq.refl

  p39 : X2 • CX01 • CCX12 • X1 • CX01 • SWAP01 • X2 • X0 ≈ X2 • CX01 • CX10 • CCX12 • CX01 • X0 • X2 • X0
  p39 = by-assoc-and (under (X2 • CX01) (X2 • X0) KB1107.proved) Eq.refl Eq.refl

  p40 : X2 • CX01 • CX10 • CCX12 • CX01 • X0 • X2 • X0 ≈ CX01 • CCX12 • X2 • CX01 • X0 • X2 • X0
  p40 = by-assoc-and (under (ε) (CX01 • X0 • X2 • X0) KB0423.proved) Eq.refl Eq.refl

  p41 : CX01 • CCX12 • X2 • CX01 • X0 • X2 • X0 ≈ CX01 • CCX12 • X2 • X2 • CX01 • X0 • X0
  p41 = by-assoc-and (under (CX01 • CCX12 • X2) (X0) KB0221.proved) Eq.refl Eq.refl

  p42 : CX01 • CCX12 • X2 • X2 • CX01 • X0 • X0 ≈ CX01 • CCX12 • CX01 • X0 • X0
  p42 = by-assoc-and (under (CX01 • CCX12) (CX01 • X0 • X0) KB0004.proved) Eq.refl Eq.refl

  p43 : CX01 • CCX12 • CX01 • X0 • X0 ≈ CX01 • CCX12 • CX01
  p43 = by-assoc-and (under (CX01 • CCX12 • CX01) (ε) KB0012.proved) Eq.refl Eq.refl

  p44 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CCX12 • CX01
  p44 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (refl))))))))))))))))))))))))))))))))))))))))))))

  p45 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p45 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0150.proved) Eq.refl Eq.refl

  p46 : CX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p46 = by-assoc-and (under (CX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0223.proved) Eq.refl Eq.refl

  p47 : CX02 • X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p47 = by-assoc-and (under (ε) (CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0033.proved) Eq.refl Eq.refl

  p48 : X2 • CX02 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p48 = by-assoc-and (under (ε) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0416.proved) Eq.refl Eq.refl

  p49 : CCX01 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p49 = by-assoc-and (under (ε) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0480.proved) Eq.refl Eq.refl

  p50 : X0 • CX02 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p50 = by-assoc-and (under (X0 • CX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0045.proved) Eq.refl Eq.refl

  p51 : X0 • CX02 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p51 = by-assoc-and (under (ε) (CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0161.proved) Eq.refl Eq.refl

  p52 : X2 • CX02 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p52 = by-assoc-and (under (X2 • CX02 • CX12) (X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0215.proved) Eq.refl Eq.refl

  p53 : X2 • CX02 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p53 = by-assoc-and (under (X2 • CX02) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0026.proved) Eq.refl Eq.refl

  p54 : X2 • CX02 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p54 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0310.proved) Eq.refl Eq.refl

  p55 : X2 • CX10 • CX02 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  p55 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02) (CCX01 • X2 • X0 • X1 • CCX01 • X1) KB0047.proved) Eq.refl Eq.refl

  p56 : X2 • CX10 • CX02 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1
  p56 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02 • X0 • CX10) (X0 • X1 • CCX01 • X1) KB0029.proved) Eq.refl Eq.refl

  p57 : X2 • CX10 • CX02 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • CX02 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
  p57 = by-assoc-and (under (X2 • CX10 • CX02 • CCX02 • X0) (CCX01 • X0 • X1 • CCX01 • X1) KB0021.proved) Eq.refl Eq.refl

  p58 : X2 • CX10 • CX02 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • CX10 • X2 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
  p58 = by-assoc-and (under (X2 • CX10) (CX10 • CCX01 • X0 • X1 • CCX01 • X1) KB0836.proved) Eq.refl Eq.refl

  p59 : X2 • CX10 • X2 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X2 • X2 • CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
  p59 = by-assoc-and (under (X2) (CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1) KB0021.proved) Eq.refl Eq.refl

  p60 : X2 • X2 • CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1
  p60 = by-assoc-and (under (ε) (CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1) KB0004.proved) Eq.refl Eq.refl

  p61 : CX10 • CCX02 • CX02 • X0 • CX10 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • X1 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1
  p61 = by-assoc-and (under (CX10 • CCX02) (X0 • X1 • CCX01 • X1) KB0788.proved) Eq.refl Eq.refl

  p62 : CX10 • CCX02 • X1 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1
  p62 = by-assoc-and (under (CX10) (CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1) KB0028.proved) Eq.refl Eq.refl

  p63 : CX10 • X1 • CCX02 • CCX01 • CX10 • X1 • X0 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • CX10 • X0 • X1 • X1 • CCX01 • X1
  p63 = by-assoc-and (under (CX10 • X1 • CCX02 • CCX01 • CX10) (X1 • CCX01 • X1) KB0044.proved) Eq.refl Eq.refl

  p64 : CX10 • X1 • CCX02 • CCX01 • CX10 • X0 • X1 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • CCX01 • X0 • CX10 • X1 • X1 • CCX01 • X1
  p64 = by-assoc-and (under (CX10 • X1 • CCX02 • CCX01) (X1 • X1 • CCX01 • X1) KB0047.proved) Eq.refl Eq.refl

  p65 : CX10 • X1 • CCX02 • CCX01 • X0 • CX10 • X1 • X1 • CCX01 • X1 ≈ CX10 • X1 • CCX02 • X0 • CX10 • CCX01 • X1 • X1 • CCX01 • X1
  p65 = by-assoc-and (under (CX10 • X1 • CCX02) (X1 • X1 • CCX01 • X1) KB0280.proved) Eq.refl Eq.refl

  p66 : CX10 • X1 • CCX02 • X0 • CX10 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX10 • CCX02 • CX10 • X1 • CCX01 • X1 • X1 • CCX01 • X1
  p66 = by-assoc-and (under (CX10) (CCX01 • X1 • X1 • CCX01 • X1) KB0596.proved) Eq.refl Eq.refl

  p67 : CX10 • CCX02 • CX10 • X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X1 • CCX01 • X1
  p67 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • X1 • CCX01 • X1) KB0219.proved) Eq.refl Eq.refl

  p68 : CX01 • CCX12 • CX01 • X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X1 • CCX01 • X1
  p68 = by-assoc-and (under (CX01 • CCX12) (CCX01 • X1 • X1 • CCX01 • X1) KB0035.proved) Eq.refl Eq.refl

  p69 : CX01 • CCX12 • X1 • CX01 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • X1 • CCX01 • CX01 • X1 • CCX01 • X1
  p69 = by-assoc-and (under (CX01 • CCX12 • X1) (X1 • CCX01 • X1) KB0435.proved) Eq.refl Eq.refl

  p70 : CX01 • CCX12 • X1 • X1 • CCX01 • CX01 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CCX01 • CX01 • X1 • CCX01 • X1
  p70 = by-assoc-and (under (CX01 • CCX12) (CCX01 • CX01 • X1 • CCX01 • X1) KB0003.proved) Eq.refl Eq.refl

  p71 : CX01 • CCX12 • CCX01 • CX01 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CCX01 • X1 • CX01 • CCX01 • X1
  p71 = by-assoc-and (under (CX01 • CCX12 • CCX01) (CCX01 • X1) KB0035.proved) Eq.refl Eq.refl

  p72 : CX01 • CCX12 • CCX01 • X1 • CX01 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • X1
  p72 = by-assoc-and (under (CX01 • CCX12) (CCX01 • X1) KB0282.proved) Eq.refl Eq.refl

  p73 : CX01 • CCX12 • X1 • CX01 • CCX01 • CCX01 • X1 ≈ CX01 • CCX12 • X1 • CX01 • X1
  p73 = by-assoc-and (under (CX01 • CCX12 • X1 • CX01) (X1) KB0011.proved) Eq.refl Eq.refl

  p74 : CX01 • CCX12 • X1 • CX01 • X1 ≈ CX01 • CCX12 • X1 • X1 • CX01
  p74 = by-assoc-and (under (CX01 • CCX12 • X1) (ε) KB0035.proved) Eq.refl Eq.refl

  p75 : CX01 • CCX12 • X1 • X1 • CX01 ≈ CX01 • CCX12 • CX01
  p75 = by-assoc-and (under (CX01 • CCX12) (CX01) KB0003.proved) Eq.refl Eq.refl

  p76 : X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 ≈ CX01 • CCX12 • CX01
  p76 = trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (trans p52 (trans p53 (trans p54 (trans p55 (trans p56 (trans p57 (trans p58 (trans p59 (trans p60 (trans p61 (trans p62 (trans p63 (trans p64 (trans p65 (trans p66 (trans p67 (trans p68 (trans p69 (trans p70 (trans p71 (trans p72 (trans p73 (trans p74 (trans p75 (refl)))))))))))))))))))))))))))))))

  proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1
  proved = trans p44 (sym p76)

module braid4 where

  p0 : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1) KB0150.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1 • CCX01 • X1
  p1 = by-assoc-and (under (CX02) (CCX02 • CCX01 • X1 • CCX01 • X1) KB0011.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01 • CCX01 • X1
  p2 = by-assoc-and (under (ε) (CCX01 • X1) KB0751.proved) Eq.refl Eq.refl

  p3 : X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • X1
  p3 = by-assoc-and (under (X1 • CX01 • CCX02) (X1) KB0011.proved) Eq.refl Eq.refl

  p4 : X1 • CX01 • CCX02 • X1 ≈ X1 • CX01 • X1 • CCX02
  p4 = by-assoc-and (under (X1 • CX01) (ε) KB0028.proved) Eq.refl Eq.refl

  p5 : X1 • CX01 • X1 • CCX02 ≈ X1 • X1 • CX01 • CCX02
  p5 = by-assoc-and (under (X1) (CCX02) KB0035.proved) Eq.refl Eq.refl

  p6 : X1 • X1 • CX01 • CCX02 ≈ CX01 • CCX02
  p6 = by-assoc-and (under (ε) (CX01 • CCX02) KB0003.proved) Eq.refl Eq.refl

  p7 : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX01 • CCX02
  p7 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (refl)))))))

  p8 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01
  p8 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p9 : CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CX02 • CCX01 • CCX01 • CCX02 • CCX01
  p9 = by-assoc-and (under (CX12 • CCX02 • CX12) (CCX01 • CCX02 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p10 : CX12 • CCX02 • CX12 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
  p10 = by-assoc-and (under (CX12 • CCX02) (CCX01 • CCX01 • CCX02 • CCX01) KB0027.proved) Eq.refl Eq.refl

  p11 : CX12 • CCX02 • CX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
  p11 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX01 • CCX02 • CCX01) KB0285.proved) Eq.refl Eq.refl

  p12 : CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01
  p12 = by-assoc-and (under (CX01) (CCX01 • CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p13 : CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01
  p13 = by-assoc-and (under (CX01) (CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p14 : CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 ≈ CX01 • CCX02 • CCX01 • CCX01
  p14 = by-assoc-and (under (CX01) (CCX01) KB0331.proved) Eq.refl Eq.refl

  p15 : CX01 • CCX02 • CCX01 • CCX01 ≈ CX01 • CCX02
  p15 = by-assoc-and (under (CX01 • CCX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p16 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX02
  p16 = trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (refl))))))))

  proved : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01
  proved = trans p7 (sym p16)

module braid5 where

  p0 : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX02 • CCX01
  p2 = by-assoc-and (under (ε) (CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p3 : CX12 • CCX02 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0331.proved) Eq.refl Eq.refl

  p4 : CCX02 • CCX01 • CCX01 ≈ CCX02
  p4 = by-assoc-and (under (CCX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p5 : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX02
  p5 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (refl)))))

  p6 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CCX01 • CCX01
  p6 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p7 : CCX02 • CCX01 • CCX01 ≈ CCX02
  p7 = by-assoc-and (under (CCX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p8 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02
  p8 = trans p6 (trans p7 (refl))

  proved : CCX01 • CCX02 • CCX01 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  proved = trans p5 (sym p8)

module comm02 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • CCX01 • X0
  p1 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • X0) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX01 • CCX01 • X0 ≈ X0 • CX02 • X0
  p2 = by-assoc-and (under (X0 • CX02) (X0) KB0011.proved) Eq.refl Eq.refl

  p3 : X0 • CX02 • X0 ≈ X2 • CX02
  p3 = by-assoc-and (under (ε) (ε) KB0161.proved) Eq.refl Eq.refl

  p4 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X2 • CX02
  p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

  p5 : X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX01 • X0 • X1 • CCX01 • X1 • X0
  p5 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) KB0153.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CCX01 • X1 • CCX01 • X1 • X0
  p6 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • X0) KB0140.proved) Eq.refl Eq.refl

  p7 : X0 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CX02 • X1 • X0
  p7 = by-assoc-and (under (X0) (X1 • X0) KB0186.proved) Eq.refl Eq.refl

  p8 : X0 • X1 • CX02 • X1 • X0 ≈ X0 • X1 • X1 • CX02 • X0
  p8 = by-assoc-and (under (X0 • X1) (X0) KB0023.proved) Eq.refl Eq.refl

  p9 : X0 • X1 • X1 • CX02 • X0 ≈ X0 • CX02 • X0
  p9 = by-assoc-and (under (X0) (CX02 • X0) KB0003.proved) Eq.refl Eq.refl

  p10 : X0 • CX02 • X0 ≈ X2 • CX02
  p10 = by-assoc-and (under (ε) (ε) KB0161.proved) Eq.refl Eq.refl

  p11 : X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02
  p11 = trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))

  proved : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
  proved = trans p4 (sym p11)
