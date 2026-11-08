{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B025 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX21 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0008 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0023 ; module KB0026 ; module KB0029 ; module KB0036 ; module KB0046 ; module KB0118 ; module KB0120 ; module KB0121 ; module KB0129 ; module KB0147 ; module KB0153 ; module KB0186 ; module KB0215 ; module KB0219 ; module KB0307 ; module KB0308)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0025 ; module KB0123)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0018 ; module KB0045 ; module KB0150 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0140 ; module KB0152 ; module KB0366)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB2230 ; module KB2897 ; module KB3873)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0015 ; module KB0079 ; module KB0107 ; module KB0108 ; module KB0223)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0383 ; module KB0481)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0163 ; module KB0285 ; module KB0355 ; module KB0357 ; module KB1658 ; module KB1661 ; module KB2829 ; module KB3094 ; module KB3579)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0901)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0515)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B016 using (module KB1871)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0222 ; module KB0341 ; module KB0445)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0742 ; module KB0904 ; module KB0963 ; module KB1329 ; module KB1720)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B021 using (module KB3229 ; module KB5021 ; module KB5198 ; module KB5514)

module comm15 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
  p2 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX02 • CCX01) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01
  p3 = by-assoc-and (under (CX12 • CX21) (CCX02 • CCX01) KB0308.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ SWAP12 • CCX01 • CCX02 • CCX02 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX02 • CCX01) KB0079.proved) Eq.refl Eq.refl

  p5 : SWAP12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX02 • SWAP12 • CCX02 • CCX02 • CCX01
  p5 = by-assoc-and (under (ε) (CCX02 • CCX02 • CCX01) KB0107.proved) Eq.refl Eq.refl

  p6 : CCX02 • SWAP12 • CCX02 • CCX02 • CCX01 ≈ CCX02 • CCX01 • SWAP12 • CCX02 • CCX01
  p6 = by-assoc-and (under (CCX02) (CCX02 • CCX01) KB0108.proved) Eq.refl Eq.refl

  p7 : CCX02 • CCX01 • SWAP12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01 • SWAP12 • CCX01
  p7 = by-assoc-and (under (CCX02 • CCX01) (CCX01) KB0108.proved) Eq.refl Eq.refl

  p8 : CCX02 • CCX01 • CCX01 • SWAP12 • CCX01 ≈ CCX02 • SWAP12 • CCX01
  p8 = by-assoc-and (under (CCX02) (SWAP12 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p9 : CCX02 • SWAP12 • CCX01 ≈ CCX02 • CCX02 • SWAP12
  p9 = by-assoc-and (under (CCX02) (ε) KB0107.proved) Eq.refl Eq.refl

  p10 : CCX02 • CCX02 • SWAP12 ≈ SWAP12
  p10 = by-assoc-and (under (ε) (SWAP12) KB0010.proved) Eq.refl Eq.refl

  p11 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ SWAP12
  p11 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))))))

  p12 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p12 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p13 : CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0
  p13 = by-assoc-and (under (CX12 • CCX02) (CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p14 : CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • CCX02 • CCX01 • X0
  p14 = by-assoc-and (under (CX12 • CCX02) (CCX02 • CCX01 • X0) KB0121.proved) Eq.refl Eq.refl

  p15 : CX12 • CCX02 • CCX01 • X0 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX01 • X0 • CCX01 • X0
  p15 = by-assoc-and (under (CX12) (CCX01 • X0) KB0742.proved) Eq.refl Eq.refl

  p16 : CX12 • CX21 • CCX01 • X0 • CCX01 • X0 ≈ X0 • CCX02 • SWAP12 • CCX01 • X0
  p16 = by-assoc-and (under (ε) (CCX01 • X0) KB0445.proved) Eq.refl Eq.refl

  p17 : X0 • CCX02 • SWAP12 • CCX01 • X0 ≈ X0 • CCX02 • CCX02 • SWAP12 • X0
  p17 = by-assoc-and (under (X0 • CCX02) (X0) KB0107.proved) Eq.refl Eq.refl

  p18 : X0 • CCX02 • CCX02 • SWAP12 • X0 ≈ X0 • SWAP12 • X0
  p18 = by-assoc-and (under (X0) (SWAP12 • X0) KB0010.proved) Eq.refl Eq.refl

  p19 : X0 • SWAP12 • X0 ≈ X0 • X0 • SWAP12
  p19 = by-assoc-and (under (X0) (ε) KB0015.proved) Eq.refl Eq.refl

  p20 : X0 • X0 • SWAP12 ≈ SWAP12
  p20 = by-assoc-and (under (ε) (SWAP12) KB0012.proved) Eq.refl Eq.refl

  p21 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ SWAP12
  p21 = trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (refl)))))))))

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0
  proved = trans p11 (sym p21)

module comm16 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • CCX01
  p0 = by-assoc-and (under (X0) (X0 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • CCX01
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • CCX01
  p2 = by-assoc-and (under (ε) (CX12 • CCX01) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • CCX01 ≈ CX12 • CX21 • CX12 • CCX01 • CCX02
  p3 = by-assoc-and (under (CX12 • CX21) (ε) KB0308.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CX12 • CCX01 • CCX02 ≈ SWAP12 • CCX01 • CCX02
  p4 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0079.proved) Eq.refl Eq.refl

  p5 : SWAP12 • CCX01 • CCX02 ≈ CCX02 • SWAP12 • CCX02
  p5 = by-assoc-and (under (ε) (CCX02) KB0107.proved) Eq.refl Eq.refl

  p6 : CCX02 • SWAP12 • CCX02 ≈ CCX02 • CCX01 • SWAP12
  p6 = by-assoc-and (under (CCX02) (ε) KB0108.proved) Eq.refl Eq.refl

  p7 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 ≈ CCX02 • CCX01 • SWAP12
  p7 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (refl)))))))

  p8 : CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CCX01 • X0
  p8 = by-assoc-and (under (ε) (CCX02 • CCX01 • X0) KB0152.proved) Eq.refl Eq.refl

  p9 : X0 • CX12 • CCX02 • CCX01 • X0 ≈ X0 • X0 • CCX02 • CCX01 • SWAP12
  p9 = by-assoc-and (under (X0) (ε) KB1329.proved) Eq.refl Eq.refl

  p10 : X0 • X0 • CCX02 • CCX01 • SWAP12 ≈ CCX02 • CCX01 • SWAP12
  p10 = by-assoc-and (under (ε) (CCX02 • CCX01 • SWAP12) KB0012.proved) Eq.refl Eq.refl

  p11 : CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CCX02 • CCX01 • SWAP12
  p11 = trans p8 (trans p9 (trans p10 (refl)))

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0
  proved = trans p7 (sym p11)

module comm24 where

  p0 : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX12 • CCX01 • X1 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1 • CCX01 • X1) KB0153.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • X1 • CCX01 • X1 ≈ CX12 • X1 • CX02 • X1
  p1 = by-assoc-and (under (CX12) (X1) KB0186.proved) Eq.refl Eq.refl

  p2 : CX12 • X1 • CX02 • X1 ≈ CX02 • CX12 • X1 • X1
  p2 = by-assoc-and (under (ε) (X1) KB0222.proved) Eq.refl Eq.refl

  p3 : CX02 • CX12 • X1 • X1 ≈ CX02 • CX12
  p3 = by-assoc-and (under (CX02 • CX12) (ε) KB0003.proved) Eq.refl Eq.refl

  p4 : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX02 • CX12
  p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

  p5 : X1 • CCX01 • X1 • X0 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • CCX01 • X0
  p5 = by-assoc-and (under (ε) (X0 • CCX01 • X0) KB0150.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX01 • X0 • CCX01 • X0 ≈ CX02 • X0 • CX12 • X0
  p6 = by-assoc-and (under (CX02) (X0) KB0152.proved) Eq.refl Eq.refl

  p7 : CX02 • X0 • CX12 • X0 ≈ CX02 • X0 • X0 • CX12
  p7 = by-assoc-and (under (CX02 • X0) (ε) KB0045.proved) Eq.refl Eq.refl

  p8 : CX02 • X0 • X0 • CX12 ≈ CX02 • CX12
  p8 = by-assoc-and (under (CX02) (CX12) KB0012.proved) Eq.refl Eq.refl

  p9 : X1 • CCX01 • X1 • X0 • CCX01 • X0 ≈ CX02 • CX12
  p9 = trans p5 (trans p6 (trans p7 (trans p8 (refl))))

  proved : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • CCX01 • X0
  proved = trans p4 (sym p9)

module comm25 where

  p0 : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX01 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) KB0153.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
  p1 = by-assoc-and (under (CX12) (CCX02 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
  p2 = trans p0 (trans p1 (refl))

  p3 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • CX12 • X0 • CCX01 • X0
  p3 = by-assoc-and (under (ε) (X0 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p4 : CX12 • CCX02 • CX12 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CCX01 • X0
  p4 = by-assoc-and (under (CX12 • CCX02) (CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • X0 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • X0
  p5 = by-assoc-and (under (CX12 • CCX02) (X0) KB0121.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX02 • CCX01 • X0 • X0 ≈ CX12 • CCX02 • CCX01
  p6 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) KB0012.proved) Eq.refl Eq.refl

  p7 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  proved : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0
  proved = trans p2 (sym p7)

module comm26 where

  p0 : X0 • CCX01 • X0 • CCX01 ≈ CX12 • CCX01 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0153.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • CCX01 ≈ CX12
  p1 = by-assoc-and (under (CX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • X0 • CCX01 ≈ CX12
  p2 = trans p0 (trans p1 (refl))

  p3 : CCX01 • X0 • CCX01 • X0 ≈ X0 • CX12 • X0
  p3 = by-assoc-and (under (ε) (X0) KB0152.proved) Eq.refl Eq.refl

  p4 : X0 • CX12 • X0 ≈ X0 • X0 • CX12
  p4 = by-assoc-and (under (X0) (ε) KB0045.proved) Eq.refl Eq.refl

  p5 : X0 • X0 • CX12 ≈ CX12
  p5 = by-assoc-and (under (ε) (CX12) KB0012.proved) Eq.refl Eq.refl

  p6 : CCX01 • X0 • CCX01 • X0 ≈ CX12
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  proved : X0 • CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CCX01 • X0
  proved = trans p2 (sym p6)

module comm35 where

  p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) KB0481.proved) Eq.refl Eq.refl

  p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) KB0215.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
  p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) KB0118.proved) Eq.refl Eq.refl

  p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01
  p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01) KB0047.proved) Eq.refl Eq.refl

  p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • CCX01 • CCX02 • CCX01
  p4 = by-assoc-and (under (X2 • CX10) (X2 • X0 • CCX01 • CCX02 • CCX01) KB3094.proved) Eq.refl Eq.refl

  p5 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • CCX01 • CCX02 • CCX01
  p5 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0 • CCX01 • CCX02 • CCX01) KB0036.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01
  p6 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX12 • X0 • CCX01 • CCX02 • CCX01) KB0021.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01
  p7 = by-assoc-and (under (X2 • CX10 • CX12) (X0 • CCX01 • CCX02 • CCX01) KB3579.proved) Eq.refl Eq.refl

  p8 : X2 • CX10 • CX12 • X1 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01
  p8 = by-assoc-and (under (ε) (CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01) KB0357.proved) Eq.refl Eq.refl

  p9 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • CCX01 • CCX02 • CCX01
  p9 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10 • CX12) (CCX01 • CCX02 • CCX01) KB0044.proved) Eq.refl Eq.refl

  p10 : CX10 • X1 • CX12 • CCX02 • CX10 • CX12 • X0 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • CCX01 • CCX02 • CCX01
  p10 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02 • CX10) (X1 • CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p11 : CX10 • X1 • CX12 • CCX02 • CX10 • X0 • CX12 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • CCX01 • CCX02 • CCX01
  p11 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CX12 • X1 • CCX01 • CCX02 • CCX01) KB0047.proved) Eq.refl Eq.refl

  p12 : CX10 • X1 • CX12 • CCX02 • X0 • CX10 • CX12 • X1 • CCX01 • CCX02 • CCX01 ≈ CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • CCX01 • CCX02 • CCX01
  p12 = by-assoc-and (under (CX10 • X1 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) KB0355.proved) Eq.refl Eq.refl

  p13 : CX10 • X1 • CX12 • CCX02 • CX12 • X1 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01
  p13 = by-assoc-and (under (CX10) (CX10 • CCX01 • CCX02 • CCX01) KB2829.proved) Eq.refl Eq.refl

  p14 : CX10 • CX12 • CX01 • CCX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01
  p14 = by-assoc-and (under (ε) (CX12 • CX10 • CCX01 • CCX02 • CCX01) KB1661.proved) Eq.refl Eq.refl

  p15 : CX02 • CX10 • CCX02 • CX02 • CX12 • CX10 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • CCX01 • CCX02 • CCX01
  p15 = by-assoc-and (under (CX02 • CX10 • CCX02 • CX02) (CCX01 • CCX02 • CCX01) KB0026.proved) Eq.refl Eq.refl

  p16 : CX02 • CX10 • CCX02 • CX02 • CX10 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01
  p16 = by-assoc-and (under (CX02) (CX12 • CCX01 • CCX02 • CCX01) KB1658.proved) Eq.refl Eq.refl

  p17 : CX02 • CX01 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01
  p17 = by-assoc-and (under (ε) (CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01) KB0025.proved) Eq.refl Eq.refl

  p18 : CX01 • CX02 • CCX12 • CX12 • CX01 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CX01 • CX02 • CCX01 • CCX02 • CCX01
  p18 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX01 • CCX02 • CCX01) KB0163.proved) Eq.refl Eq.refl

  p19 : CX01 • CX02 • CCX12 • CX01 • CX02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CCX01
  p19 = by-assoc-and (under (CX01 • CX02 • CCX12) (CCX02 • CCX01) KB0123.proved) Eq.refl Eq.refl

  p20 : CX01 • CX02 • CCX12 • CCX01 • CX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX12 • CCX02 • CX02 • CCX01
  p20 = by-assoc-and (under (CX01) (CCX01) KB2897.proved) Eq.refl Eq.refl

  p21 : CX01 • CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CX01 • CCX12 • CX01 • CX02 • CCX12
  p21 = by-assoc-and (under (CX01) (ε) KB5514.proved) Eq.refl Eq.refl

  p22 : CX01 • CX01 • CCX12 • CX01 • CX02 • CCX12 ≈ CCX12 • CX01 • CX02 • CCX12
  p22 = by-assoc-and (under (ε) (CCX12 • CX01 • CX02 • CCX12) KB0013.proved) Eq.refl Eq.refl

  p23 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX12 • CX01 • CX02 • CCX12
  p23 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (refl)))))))))))))))))))))))

  p24 : CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p24 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0214.proved) Eq.refl Eq.refl

  p25 : CX12 • CCX02 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p25 = by-assoc-and (under (CX12 • CCX02) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p26 : CX12 • CCX02 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p26 = by-assoc-and (under (CX12 • CCX02 • X0) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p27 : CX12 • CCX02 • X0 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p27 = by-assoc-and (under (CX12 • CCX02) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0383.proved) Eq.refl Eq.refl

  p28 : CX12 • CCX02 • X2 • CCX01 • X0 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p28 = by-assoc-and (under (ε) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB5021.proved) Eq.refl Eq.refl

  p29 : X0 • CCX02 • CCX01 • X1 • SWAP12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X1 • X0 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p29 = by-assoc-and (under (X0 • CCX02 • CCX01 • X1) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0015.proved) Eq.refl Eq.refl

  p30 : X0 • CCX02 • CCX01 • X1 • X0 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • CCX02 • CCX01 • X0 • X1 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p30 = by-assoc-and (under (X0 • CCX02 • CCX01) (SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0044.proved) Eq.refl Eq.refl

  p31 : X0 • CCX02 • CCX01 • X0 • X1 • SWAP12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X0 • CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p31 = by-assoc-and (under (X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB5198.proved) Eq.refl Eq.refl

  p32 : X0 • X0 • CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p32 = by-assoc-and (under (ε) (CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p33 : CX12 • CCX02 • X2 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p33 = by-assoc-and (under (CX12 • CCX02 • X2 • CCX01) (X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p34 : CX12 • CCX02 • X2 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p34 = by-assoc-and (under (CX12 • CCX02 • X2 • CCX01) (X0 • CCX01 • X2 • X0) KB0219.proved) Eq.refl Eq.refl

  p35 : CX12 • CCX02 • X2 • CCX01 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CX12 • X2 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p35 = by-assoc-and (under (CX12) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) KB0901.proved) Eq.refl Eq.refl

  p36 : CX12 • X2 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p36 = by-assoc-and (under (ε) (CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p37 : X2 • CX12 • CCX02 • CX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ X2 • CX01 • CX12 • CCX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p37 = by-assoc-and (under (X2) (CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0) KB0285.proved) Eq.refl Eq.refl

  p38 : X2 • CX01 • CX12 • CCX02 • CCX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CCX02 • X2 • CX12 • CCX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0
  p38 = by-assoc-and (under (ε) (CCX12 • CX01 • X0 • CCX01 • X2 • X0) KB1720.proved) Eq.refl Eq.refl

  p39 : CCX02 • X2 • CX12 • CCX02 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 ≈ CCX02 • X2 • CX12 • CX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0
  p39 = by-assoc-and (under (CCX02 • X2 • CX12) (X0 • CCX01 • X2 • X0) KB0341.proved) Eq.refl Eq.refl

  p40 : CCX02 • X2 • CX12 • CX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 ≈ X2 • CCX02 • CX02 • CX12 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0
  p40 = by-assoc-and (under (ε) (CCX12 • CCX02 • X0 • CCX01 • X2 • X0) KB0904.proved) Eq.refl Eq.refl

  p41 : X2 • CCX02 • CX02 • CX12 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 ≈ X2 • CCX02 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X0 • X2 • X0
  p41 = by-assoc-and (under (X2 • CCX02 • CX02) (X2 • X0) KB3873.proved) Eq.refl Eq.refl

  p42 : X2 • CCX02 • CX02 • CX10 • CCX12 • CCX01 • CCX02 • X0 • X2 • X0 ≈ CX02 • CCX02 • CCX12 • X2 • CCX01 • CCX02 • X0 • X2 • X0
  p42 = by-assoc-and (under (ε) (CCX01 • CCX02 • X0 • X2 • X0) KB1871.proved) Eq.refl Eq.refl

  p43 : CX02 • CCX02 • CCX12 • X2 • CCX01 • CCX02 • X0 • X2 • X0 ≈ CX02 • CCX02 • CCX12 • CCX01 • CX01 • CCX02 • X0 • X0
  p43 = by-assoc-and (under (CX02 • CCX02 • CCX12) (X0) KB2230.proved) Eq.refl Eq.refl

  p44 : CX02 • CCX02 • CCX12 • CCX01 • CX01 • CCX02 • X0 • X0 ≈ CX02 • CX02 • CCX12 • CX01 • CX02 • CCX12 • X0 • X0
  p44 = by-assoc-and (under (CX02) (X0 • X0) KB3229.proved) Eq.refl Eq.refl

  p45 : CX02 • CX02 • CCX12 • CX01 • CX02 • CCX12 • X0 • X0 ≈ CCX12 • CX01 • CX02 • CCX12 • X0 • X0
  p45 = by-assoc-and (under (ε) (CCX12 • CX01 • CX02 • CCX12 • X0 • X0) KB0008.proved) Eq.refl Eq.refl

  p46 : CCX12 • CX01 • CX02 • CCX12 • X0 • X0 ≈ CCX12 • CX01 • CX02 • X0 • CCX12 • X0
  p46 = by-assoc-and (under (CCX12 • CX01 • CX02) (X0) KB0046.proved) Eq.refl Eq.refl

  p47 : CCX12 • CX01 • CX02 • X0 • CCX12 • X0 ≈ CCX12 • CX01 • CX02 • X0 • X0 • CCX12
  p47 = by-assoc-and (under (CCX12 • CX01 • CX02 • X0) (ε) KB0046.proved) Eq.refl Eq.refl

  p48 : CCX12 • CX01 • CX02 • X0 • X0 • CCX12 ≈ CCX12 • CX01 • CX02 • CCX12
  p48 = by-assoc-and (under (CCX12 • CX01 • CX02) (CCX12) KB0012.proved) Eq.refl Eq.refl

  p49 : CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CCX12 • CX01 • CX02 • CCX12
  p49 = trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (refl)))))))))))))))))))))))))

  proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  proved = trans p23 (sym p49)

module comm36 where

  p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01) KB0481.proved) Eq.refl Eq.refl

  p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01
  p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • CCX01) KB0215.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01
  p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01) KB0118.proved) Eq.refl Eq.refl

  p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01
  p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • CCX01) KB0047.proved) Eq.refl Eq.refl

  p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • CCX01
  p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • CCX01) KB0029.proved) Eq.refl Eq.refl

  p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • CCX01
  p5 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • CCX01) KB0021.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • CCX01
  p6 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (CCX01) KB0366.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • CCX01
  p7 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • CCX01) KB0018.proved) Eq.refl Eq.refl

  p8 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • CCX01 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • CCX01
  p8 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p9 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • CCX01
  p9 = by-assoc-and (under (X2 • CX10) (CX10 • CCX01) KB0963.proved) Eq.refl Eq.refl

  p10 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • CCX01
  p10 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (CCX01) KB0026.proved) Eq.refl Eq.refl

  p11 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CCX01 • CX10
  p11 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (ε) KB0147.proved) Eq.refl Eq.refl

  p12 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CCX01 • CX10
  p12 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (refl))))))))))))

  p13 : CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p13 = by-assoc-and (under (ε) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0223.proved) Eq.refl Eq.refl

  p14 : X2 • CCX01 • X0 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • X0 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p14 = by-assoc-and (under (X2) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0152.proved) Eq.refl Eq.refl

  p15 : X2 • X0 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p15 = by-assoc-and (under (ε) (CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p16 : X0 • X2 • CX12 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X2 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p16 = by-assoc-and (under (X0 • X2) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p17 : X0 • X2 • X0 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X0 • X0 • X2 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (X0) (CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p18 : X0 • X0 • X2 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (ε) (X2 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p19 : X2 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (X2 • CX12) (X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p20 : X2 • CX12 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p21 : X2 • CX10 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p22 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CCX01 • X0
  p22 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • CX10) (X0) KB0029.proved) Eq.refl Eq.refl

  p23 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CCX01 • X0
  p23 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CCX01 • X0) KB0021.proved) Eq.refl Eq.refl

  p24 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CCX01 • CX10
  p24 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (ε) KB0366.proved) Eq.refl Eq.refl

  p25 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CCX01 • CX10
  p25 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CCX01 • CX10) KB0018.proved) Eq.refl Eq.refl

  p26 : X2 • CX10 • CX12 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CCX01 • CX10
  p26 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X2 • CCX01 • CX10) KB0012.proved) Eq.refl Eq.refl

  p27 : CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CCX01 • CX10
  p27 = trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (refl))))))))))))))

  proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • CCX01 ≈ CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  proved = trans p12 (sym p27)

module comm46 where

  p0 : X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX01 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0150.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • CCX01 ≈ CX02
  p1 = by-assoc-and (under (CX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : X1 • CCX01 • X1 • CCX01 ≈ CX02
  p2 = trans p0 (trans p1 (refl))

  p3 : CCX01 • X1 • CCX01 • X1 ≈ X1 • CX02 • X1
  p3 = by-assoc-and (under (ε) (X1) KB0186.proved) Eq.refl Eq.refl

  p4 : X1 • CX02 • X1 ≈ X1 • X1 • CX02
  p4 = by-assoc-and (under (X1) (ε) KB0023.proved) Eq.refl Eq.refl

  p5 : X1 • X1 • CX02 ≈ CX02
  p5 = by-assoc-and (under (ε) (CX02) KB0003.proved) Eq.refl Eq.refl

  p6 : CCX01 • X1 • CCX01 • X1 ≈ CX02
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  proved : X1 • CCX01 • X1 • CCX01 ≈ CCX01 • X1 • CCX01 • X1
  proved = trans p2 (sym p6)

module invol0 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X1 • CCX01 • X1 • X0
  p1 = by-assoc-and (under (X0 • CX02 • CCX01) (X1 • CCX01 • X1 • X0) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CCX01 • CCX01 • X1 • X0
  p2 = by-assoc-and (under (X0) (CCX01 • X1 • X0) KB0120.proved) Eq.refl Eq.refl

  p3 : X0 • X1 • CCX01 • CCX01 • X1 • X0 ≈ X0 • X1 • X1 • X0
  p3 = by-assoc-and (under (X0 • X1) (X1 • X0) KB0011.proved) Eq.refl Eq.refl

  p4 : X0 • X1 • X1 • X0 ≈ X0 • X0
  p4 = by-assoc-and (under (X0) (X0) KB0003.proved) Eq.refl Eq.refl

  p5 : X0 • X0 ≈ ε
  p5 = by-assoc-and (under (ε) (ε) KB0012.proved) Eq.refl Eq.refl

  p6 : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ ε
  p6 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (refl))))))

  p7 : ε ≈ ε
  p7 = refl

  proved : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ ε
  proved = trans p6 (sym p7)

module invol1 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
  p2 = by-assoc-and (under (ε) (CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0
  p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0
  p4 = by-assoc-and (under (CX12) (CX12 • CCX01 • CCX02 • CCX01 • X0) KB0129.proved) Eq.refl Eq.refl

  p5 : CX12 • X0 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0
  p5 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p6 : X0 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • CCX02 • CCX01 • X0
  p6 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0) KB0307.proved) Eq.refl Eq.refl

  p7 : X0 • CCX01 • CCX02 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • X0
  p7 = by-assoc-and (under (X0 • CCX01) (CCX01 • X0) KB0010.proved) Eq.refl Eq.refl

  p8 : X0 • CCX01 • CCX01 • X0 ≈ X0 • X0
  p8 = by-assoc-and (under (X0) (X0) KB0011.proved) Eq.refl Eq.refl

  p9 : X0 • X0 ≈ ε
  p9 = by-assoc-and (under (ε) (ε) KB0012.proved) Eq.refl Eq.refl

  p10 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ ε
  p10 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl))))))))))

  p11 : ε ≈ ε
  p11 = refl

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ ε
  proved = trans p10 (sym p11)

module invol2 where

  p0 : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0 • CCX01 • X0) KB0153.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • X0 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0140.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • CCX01 • X0 ≈ X0 • X0
  p2 = by-assoc-and (under (X0) (X0) KB0011.proved) Eq.refl Eq.refl

  p3 : X0 • X0 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0012.proved) Eq.refl Eq.refl

  p4 : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ ε
  p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

  p5 : ε ≈ ε
  p5 = refl

  proved : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ ε
  proved = trans p4 (sym p5)
