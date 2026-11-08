{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B016 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0006 ; module KB0008 ; module KB0011 ; module KB0012 ; module KB0014 ; module KB0023 ; module KB0026 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0037 ; module KB0046 ; module KB0139 ; module KB0147 ; module KB0160 ; module KB0217 ; module KB0219)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0007 ; module KB0043 ; module KB0218 ; module KB0282 ; module KB0322)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0005 ; module KB0018 ; module KB0019 ; module KB0032 ; module KB0091 ; module KB0141 ; module KB0150 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0115 ; module KB0135 ; module KB0168 ; module KB0280 ; module KB0315)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB0335)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0072 ; module KB0085 ; module KB0104 ; module KB0132 ; module KB0223 ; module KB0657)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0061 ; module KB0294 ; module KB0329)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0174 ; module KB0210 ; module KB0231 ; module KB0325 ; module KB1364)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B009 using (module KB0179)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0311)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0105)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0224)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0167 ; module KB0169 ; module KB0372 ; module KB0466 ; module KB0915 ; module KB1394)

module KB1395 where

  p0 : CCX02 • X2 • CX10 • CCX02 • CCX12 • CCX12 ≈ CCX12 • X2 • SWAP01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB1394.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX10 • CCX02 • CCX12 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02
  p1 = by-assoc-and (under (CCX02 • X2 • CX10 • CCX02) (ε) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX12 • X2 • CCX02 • SWAP01
  p3 = by-assoc-and (under (CCX12 • X2) (ε) KB0091.proved) Eq.refl Eq.refl

  p4 : CCX12 • X2 • SWAP01 • CCX12 ≈ CCX12 • X2 • CCX02 • SWAP01
  p4 = trans p3 (refl)

  p5 : CCX02 • X2 • CX10 • CCX02 ≈ CCX02 • X2 • CX10 • CCX02
  p5 = refl

  p6 : CCX12 • X2 • CCX02 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX12 • X2 • CCX02 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02
  proved = p6

module KB1407 where

  p0 : CCX12 • CCX01 • CCX02 • CX10 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB1364.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX01 • CCX02 • CX10 • CX10 ≈ CCX12 • CCX01 • CCX02
  p1 = by-assoc-and (under (CCX12 • CCX01 • CCX02) (ε) KB0005.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CCX12 • CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX01
  p3 = by-assoc-and (under (CX12 • CCX02) (ε) KB0466.proved) Eq.refl Eq.refl

  p4 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX01 • CCX02 ≈ CCX12 • CCX01 • CCX02
  p5 = refl

  p6 : CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02
  proved = p6

module KB1408 where

  p0 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
  p0 = by-assoc-and (under (CX12) (ε) KB1407.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX12 • CCX01) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CCX01 • CCX02 ≈ CX12 • CCX12 • CCX01 • CCX02
  p3 = refl

  p4 : CCX02 • CX12 • CCX12 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX01
  p4 = refl

  p5 : CX12 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
  proved = p6

module KB1474 where

  p0 : CCX01 • X0 • X2 • CCX12 • X2 ≈ X2 • CCX01 • X0 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (CCX12 • X2) KB0223.proved) Eq.refl Eq.refl

  p1 : CCX01 • X0 • X2 • CCX12 • X2 ≈ CCX01 • X0 • CX10 • CCX12
  p1 = by-assoc-and (under (CCX01 • X0) (ε) KB0167.proved) Eq.refl Eq.refl

  p2 : X2 • CCX01 • X0 • CCX12 • X2 ≈ CCX01 • X0 • CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : X2 • CCX01 • X0 • CCX12 • X2 ≈ X2 • CCX01 • X0 • CCX12 • X2
  p3 = refl

  p4 : CCX01 • X0 • CX10 • CCX12 ≈ X0 • CX10 • CCX01 • CCX12
  p4 = by-assoc-and (under (ε) (CCX12) KB0280.proved) Eq.refl Eq.refl

  p5 : CCX01 • X0 • CX10 • CCX12 ≈ X0 • CX10 • CCX01 • CCX12
  p5 = trans p4 (refl)

  p6 : X2 • CCX01 • X0 • CCX12 • X2 ≈ X0 • CX10 • CCX01 • CCX12
  p6 = trans (sym p3) (trans p2 p5)

  proved : X2 • CCX01 • X0 • CCX12 • X2 ≈ X0 • CX10 • CCX01 • CCX12
  proved = p6

module KB0143 where

  p0 : X0 • X0 • CX10 • X1 ≈ X0 • X1 • CX10
  p0 = by-assoc-and (under (X0) (ε) KB0115.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • CX10 • X1 ≈ CX10 • X1
  p1 = by-assoc-and (under (ε) (CX10 • X1) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • X1 • CX10 ≈ CX10 • X1
  p2 = trans (sym p0) p1

  p3 : X0 • X1 • CX10 ≈ X0 • X1 • CX10
  p3 = refl

  p4 : CX10 • X1 ≈ CX10 • X1
  p4 = refl

  p5 : X0 • X1 • CX10 ≈ CX10 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • X1 • CX10 ≈ CX10 • X1
  proved = p5

module KB0182 where

  p0 : X0 • X1 • CX10 • CX10 ≈ CX10 • X1 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0143.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX10 • CX10 ≈ X0 • X1
  p1 = by-assoc-and (under (X0 • X1) (ε) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • X1 • CX10 ≈ X0 • X1
  p2 = trans (sym p0) p1

  p3 : CX10 • X1 • CX10 ≈ CX10 • X1 • CX10
  p3 = refl

  p4 : X0 • X1 ≈ X0 • X1
  p4 = refl

  p5 : CX10 • X1 • CX10 ≈ X0 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • X1 • CX10 ≈ X0 • X1
  proved = p5

module KB1734 where

  p0 : CX10 • CCX12 • CCX02 • CX10 • X1 • CX10 ≈ CCX02 • CCX12 • X1 • CX10
  p0 = by-assoc-and (under (ε) (X1 • CX10) KB0335.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CCX02 • CX10 • X1 • CX10 ≈ CX10 • CCX12 • CCX02 • X0 • X1
  p1 = by-assoc-and (under (CX10 • CCX12 • CCX02) (ε) KB0182.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX12 • X1 • CX10 ≈ CX10 • CCX12 • CCX02 • X0 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX12 • X1 • CX10 ≈ CCX02 • CCX12 • X1 • CX10
  p3 = refl

  p4 : CX10 • CCX12 • CCX02 • X0 • X1 ≈ CX10 • CCX12 • X1 • CCX02 • X0
  p4 = by-assoc-and (under (CX10 • CCX12) (ε) KB0231.proved) Eq.refl Eq.refl

  p5 : CX10 • CCX12 • CCX02 • X0 • X1 ≈ CX10 • CCX12 • X1 • CCX02 • X0
  p5 = trans p4 (refl)

  p6 : CCX02 • CCX12 • X1 • CX10 ≈ CX10 • CCX12 • X1 • CCX02 • X0
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX10 • CCX12 • X1 • CCX02 • X0 ≈ CCX02 • CCX12 • X1 • CX10
  p7 = sym p6

  proved : CX10 • CCX12 • X1 • CCX02 • X0 ≈ CCX02 • CCX12 • X1 • CX10
  proved = p7

module KB0284 where

  p0 : CX20 • CX10 • CX12 • CCX01 ≈ CX20 • CCX01 • CX10
  p0 = by-assoc-and (under (CX20) (ε) KB0147.proved) Eq.refl Eq.refl

  p1 : CX20 • CX10 • CX12 • CCX01 ≈ CX12 • CX20 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01) KB0135.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CX10 ≈ CX20 • CCX01 • CX10
  p3 = refl

  p4 : CX12 • CX20 • CCX01 ≈ CX12 • CX20 • CCX01
  p4 = refl

  p5 : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
  proved = p5

module KB0297 where

  p0 : CX21 • CX20 • CX10 ≈ CX21 • CX10 • CX20
  p0 = by-assoc-and (under (CX21) (ε) KB0210.proved) Eq.refl Eq.refl

  p1 : CX21 • CX20 • CX10 ≈ CX20 • CX21 • CX10
  p1 = by-assoc-and (under (ε) (CX10) KB0043.proved) Eq.refl Eq.refl

  p2 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
  p2 = trans (sym p0) p1

  p3 : CX21 • CX10 • CX20 ≈ CX21 • CX10 • CX20
  p3 = refl

  p4 : CX20 • CX21 • CX10 ≈ CX20 • CX21 • CX10
  p4 = refl

  p5 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
  proved = p5

module KB0237 where

  p0 : SWAP12 • CX12 • CX10 ≈ CX12 • CX21 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0061.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX12 • CX10 ≈ SWAP12 • CX10 • CX12
  p1 = by-assoc-and (under (SWAP12) (ε) KB0026.proved) Eq.refl Eq.refl

  p2 : CX12 • CX21 • CX10 ≈ SWAP12 • CX10 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CX21 • CX10 ≈ CX12 • CX21 • CX10
  p3 = refl

  p4 : SWAP12 • CX10 • CX12 ≈ CX20 • SWAP12 • CX12
  p4 = by-assoc-and (under (ε) (CX12) KB0072.proved) Eq.refl Eq.refl

  p5 : CX20 • SWAP12 • CX12 ≈ CX20 • CX12 • CX21
  p5 = by-assoc-and (under (CX20) (ε) KB0061.proved) Eq.refl Eq.refl

  p6 : SWAP12 • CX10 • CX12 ≈ CX20 • CX12 • CX21
  p6 = trans p4 (trans p5 (refl))

  p7 : CX12 • CX21 • CX10 ≈ CX20 • CX12 • CX21
  p7 = trans (sym p3) (trans p2 p6)

  p8 : CX20 • CX12 • CX21 ≈ CX12 • CX21 • CX10
  p8 = sym p7

  proved : CX20 • CX12 • CX21 ≈ CX12 • CX21 • CX10
  proved = p8

module KB0343 where

  p0 : CX20 • CX12 • CX21 • CX21 ≈ CX12 • CX21 • CX10 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0237.proved) Eq.refl Eq.refl

  p1 : CX20 • CX12 • CX21 • CX21 ≈ CX20 • CX12
  p1 = by-assoc-and (under (CX20 • CX12) (ε) KB0007.proved) Eq.refl Eq.refl

  p2 : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CX21 • CX10 • CX21 ≈ CX12 • CX21 • CX10 • CX21
  p3 = refl

  p4 : CX20 • CX12 ≈ CX20 • CX12
  p4 = refl

  p5 : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX21 • CX10 • CX21 ≈ CX20 • CX12
  proved = p5

module KB0344 where

  p0 : CX12 • CX12 • CX21 • CX10 • CX21 ≈ CX12 • CX20 • CX12
  p0 = by-assoc-and (under (CX12) (ε) KB0343.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX21
  p1 = by-assoc-and (under (ε) (CX21 • CX10 • CX21) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CX20 • CX12 ≈ CX21 • CX10 • CX21
  p2 = trans (sym p0) p1

  p3 : CX12 • CX20 • CX12 ≈ CX20 • CX10
  p3 = by-assoc-and (under (ε) (ε) KB0174.proved) Eq.refl Eq.refl

  p4 : CX20 • CX10 ≈ CX10 • CX20
  p4 = by-assoc-and (under (ε) (ε) KB0210.proved) Eq.refl Eq.refl

  p5 : CX12 • CX20 • CX12 ≈ CX10 • CX20
  p5 = trans p3 (trans p4 (refl))

  p6 : CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX21
  p6 = refl

  p7 : CX10 • CX20 ≈ CX21 • CX10 • CX21
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX21 • CX10 • CX21 ≈ CX10 • CX20
  p8 = sym p7

  proved : CX21 • CX10 • CX21 ≈ CX10 • CX20
  proved = p8

module KB0345 where

  p0 : CX21 • CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX20
  p0 = by-assoc-and (under (CX21) (ε) KB0344.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CX10 • CX21 ≈ CX10 • CX21
  p1 = by-assoc-and (under (ε) (CX10 • CX21) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CX10 • CX20 ≈ CX10 • CX21
  p2 = trans (sym p0) p1

  p3 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
  p3 = by-assoc-and (under (ε) (ε) KB0297.proved) Eq.refl Eq.refl

  p4 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
  p4 = trans p3 (refl)

  p5 : CX10 • CX21 ≈ CX10 • CX21
  p5 = refl

  p6 : CX20 • CX21 • CX10 ≈ CX10 • CX21
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX20 • CX21 • CX10 ≈ CX10 • CX21
  proved = p6

module KB1778 where

  p0 : CX20 • CCX01 • CX20 • CX21 • CX10 ≈ CX20 • CCX01 • CX10 • CX21
  p0 = by-assoc-and (under (CX20 • CCX01) (ε) KB0345.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX01 • CX20 • CX21 • CX10 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
  p1 = by-assoc-and (under (ε) (CX21 • CX10) KB0218.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CX10 • CX21 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CX10 • CX21 ≈ CX12 • CX20 • CCX01 • CX21
  p3 = by-assoc-and (under (ε) (CX21) KB0284.proved) Eq.refl Eq.refl

  p4 : CX20 • CCX01 • CX10 • CX21 ≈ CX12 • CX20 • CCX01 • CX21
  p4 = trans p3 (refl)

  p5 : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
  p5 = refl

  p6 : CX12 • CX20 • CCX01 • CX21 ≈ CX02 • CCX12 • CX02 • CX21 • CX10
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX12 • CX20 • CCX01 • CX21
  p7 = sym p6

  proved : CX02 • CCX12 • CX02 • CX21 • CX10 ≈ CX12 • CX20 • CCX01 • CX21
  proved = p7

module KB1871 where

  p0 : CX02 • CCX02 • X2 • CX10 • CCX12 ≈ X2 • CCX02 • CX02 • CX10 • CCX12
  p0 = by-assoc-and (under (ε) (CX10 • CCX12) KB0372.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX02 • X2 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
  p1 = by-assoc-and (under (CX02 • CCX02) (ε) KB0168.proved) Eq.refl Eq.refl

  p2 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ X2 • CCX02 • CX02 • CX10 • CCX12
  p3 = refl

  p4 : CX02 • CCX02 • CCX12 • X2 ≈ CX02 • CCX02 • CCX12 • X2
  p4 = refl

  p5 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
  proved = p5

module KB0441 where

  p0 : X2 • X1 • CX01 • X0 ≈ X2 • X0 • CX01
  p0 = by-assoc-and (under (X2) (ε) KB0139.proved) Eq.refl Eq.refl

  p1 : X2 • X1 • CX01 • X0 ≈ X1 • X2 • CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0019.proved) Eq.refl Eq.refl

  p2 : X2 • X0 • CX01 ≈ X1 • X2 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : X2 • X0 • CX01 ≈ X0 • X2 • CX01
  p3 = by-assoc-and (under (ε) (CX01) KB0018.proved) Eq.refl Eq.refl

  p4 : X2 • X0 • CX01 ≈ X0 • X2 • CX01
  p4 = trans p3 (refl)

  p5 : X1 • X2 • CX01 • X0 ≈ X1 • X2 • CX01 • X0
  p5 = refl

  p6 : X0 • X2 • CX01 ≈ X1 • X2 • CX01 • X0
  p6 = trans (sym p4) (trans p2 p5)

  p7 : X1 • X2 • CX01 • X0 ≈ X0 • X2 • CX01
  p7 = sym p6

  proved : X1 • X2 • CX01 • X0 ≈ X0 • X2 • CX01
  proved = p7

module KB2122 where

  p0 : CCX01 • X1 • X2 • CX01 • X0 ≈ CCX01 • X0 • X2 • CX01
  p0 = by-assoc-and (under (CCX01) (ε) KB0441.proved) Eq.refl Eq.refl

  p1 : CCX01 • X1 • X2 • CX01 • X0 ≈ X2 • CCX01 • X1 • CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0224.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X1 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X0 • CX01
  p3 = by-assoc-and (under (ε) (CX01) KB0223.proved) Eq.refl Eq.refl

  p4 : CCX01 • X0 • X2 • CX01 ≈ X2 • CCX01 • X0 • CX01
  p4 = trans p3 (refl)

  p5 : X2 • CCX01 • X1 • CX01 • X0 ≈ X2 • X1 • CX01 • CCX01 • X0
  p5 = by-assoc-and (under (X2) (X0) KB0282.proved) Eq.refl Eq.refl

  p6 : X2 • X1 • CX01 • CCX01 • X0 ≈ X1 • X2 • CX01 • CCX01 • X0
  p6 = by-assoc-and (under (ε) (CX01 • CCX01 • X0) KB0019.proved) Eq.refl Eq.refl

  p7 : X2 • CCX01 • X1 • CX01 • X0 ≈ X1 • X2 • CX01 • CCX01 • X0
  p7 = trans p5 (trans p6 (refl))

  p8 : X2 • CCX01 • X0 • CX01 ≈ X1 • X2 • CX01 • CCX01 • X0
  p8 = trans (sym p4) (trans p2 p7)

  p9 : X1 • X2 • CX01 • CCX01 • X0 ≈ X2 • CCX01 • X0 • CX01
  p9 = sym p8

  proved : X1 • X2 • CX01 • CCX01 • X0 ≈ X2 • CCX01 • X0 • CX01
  proved = p9

module KB0526 where

  p0 : CX02 • X1 • CCX12 • X1 ≈ CX02 • CX20 • CCX12
  p0 = by-assoc-and (under (CX02) (ε) KB0169.proved) Eq.refl Eq.refl

  p1 : CX02 • X1 • CCX12 • X1 ≈ X1 • CX02 • CCX12 • X1
  p1 = by-assoc-and (under (ε) (CCX12 • X1) KB0023.proved) Eq.refl Eq.refl

  p2 : CX02 • CX20 • CCX12 ≈ X1 • CX02 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12
  p3 = refl

  p4 : X1 • CX02 • CCX12 • X1 ≈ X1 • CX02 • CCX12 • X1
  p4 = refl

  p5 : CX02 • CX20 • CCX12 ≈ X1 • CX02 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CX02 • CCX12 • X1 ≈ CX02 • CX20 • CCX12
  p6 = sym p5

  proved : X1 • CX02 • CCX12 • X1 ≈ CX02 • CX20 • CCX12
  proved = p6

module KB2310 where

  p0 : CCX02 • X1 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
  p0 = by-assoc-and (under (CCX02) (ε) KB0526.proved) Eq.refl Eq.refl

  p1 : CCX02 • X1 • CX02 • CCX12 • X1 ≈ X1 • CCX02 • CX02 • CCX12 • X1
  p1 = by-assoc-and (under (ε) (CX02 • CCX12 • X1) KB0028.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX02 • CX20 • CCX12 ≈ X1 • CCX02 • CX02 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX02 • CX20 • CCX12 ≈ CCX02 • CX02 • CX20 • CCX12
  p3 = refl

  p4 : X1 • CCX02 • CX02 • CCX12 • X1 ≈ X1 • CCX02 • CX02 • CCX12 • X1
  p4 = refl

  p5 : CCX02 • CX02 • CX20 • CCX12 ≈ X1 • CCX02 • CX02 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CCX02 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
  p6 = sym p5

  proved : X1 • CCX02 • CX02 • CCX12 • X1 ≈ CCX02 • CX02 • CX20 • CCX12
  proved = p6

module KB0708 where

  p0 : CX02 • CX02 • CCX01 • CCX12 • X1 ≈ CX02 • CCX12 • X1 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB0657.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX01 • CCX12 • X1 ≈ CCX01 • CCX12 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1 • CCX01
  p3 = refl

  p4 : CCX01 • CCX12 • X1 ≈ CCX01 • CCX12 • X1
  p4 = refl

  p5 : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
  proved = p5

module KB0738 where

  p0 : CX02 • CCX12 • X1 • CCX01 • CCX01 ≈ CCX01 • CCX12 • X1 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0708.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX12 • X1 • CCX01 • CCX01 ≈ CX02 • CCX12 • X1
  p1 = by-assoc-and (under (CX02 • CCX12 • X1) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1 • CCX01
  p3 = refl

  p4 : CX02 • CCX12 • X1 ≈ CX02 • CCX12 • X1
  p4 = refl

  p5 : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
  proved = p5

module KB2747 where

  p0 : CCX01 • CCX12 • X1 • CCX01 • X2 ≈ CX02 • CCX12 • X1 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0738.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • X1 • CCX01 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
  p1 = by-assoc-and (under (CCX01 • CCX12 • X1) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • X1 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • X2
  p3 = refl

  p4 : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
  p4 = refl

  p5 : CX02 • CCX12 • X1 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CX02 • CCX12 • X1 • X2
  p6 = sym p5

  proved : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CX02 • CCX12 • X1 • X2
  proved = p6

module KB0356 where

  p0 : CCX12 • X0 • CX10 • X1 ≈ CCX12 • X1 • CX10
  p0 = by-assoc-and (under (CCX12) (ε) KB0115.proved) Eq.refl Eq.refl

  p1 : CCX12 • X0 • CX10 • X1 ≈ X0 • CCX12 • CX10 • X1
  p1 = by-assoc-and (under (ε) (CX10 • X1) KB0046.proved) Eq.refl Eq.refl

  p2 : CCX12 • X1 • CX10 ≈ X0 • CCX12 • CX10 • X1
  p2 = trans (sym p0) p1

  p3 : CCX12 • X1 • CX10 ≈ CCX12 • X1 • CX10
  p3 = refl

  p4 : X0 • CCX12 • CX10 • X1 ≈ X0 • CX10 • CCX12 • X1
  p4 = by-assoc-and (under (X0) (X1) KB0032.proved) Eq.refl Eq.refl

  p5 : X0 • CCX12 • CX10 • X1 ≈ X0 • CX10 • CCX12 • X1
  p5 = trans p4 (refl)

  p6 : CCX12 • X1 • CX10 ≈ X0 • CX10 • CCX12 • X1
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X0 • CX10 • CCX12 • X1 ≈ CCX12 • X1 • CX10
  p7 = sym p6

  proved : X0 • CX10 • CCX12 • X1 ≈ CCX12 • X1 • CX10
  proved = p7

module KB2819 where

  p0 : CX02 • X0 • CX10 • CCX12 • X1 ≈ X0 • CX02 • CCX12 • X2 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0915.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • CX10 • CCX12 • X1 ≈ CX02 • CCX12 • X1 • CX10
  p1 = by-assoc-and (under (CX02) (ε) KB0356.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX12 • X2 • X1 ≈ CX02 • CCX12 • X1 • CX10
  p2 = trans (sym p0) p1

  p3 : X0 • CX02 • CCX12 • X2 • X1 ≈ X0 • CX02 • CCX12 • X1 • X2
  p3 = by-assoc-and (under (X0 • CX02 • CCX12) (ε) KB0019.proved) Eq.refl Eq.refl

  p4 : X0 • CX02 • CCX12 • X2 • X1 ≈ X0 • CX02 • CCX12 • X1 • X2
  p4 = trans p3 (refl)

  p5 : CX02 • CCX12 • X1 • CX10 ≈ CX02 • CCX12 • X1 • CX10
  p5 = refl

  p6 : X0 • CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • CX10
  p6 = trans (sym p4) (trans p2 p5)

  proved : X0 • CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • CX10
  proved = p6

module KB3095 where

  p0 : CCX01 • X0 • CX10 • CCX02 • CX10 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
  p0 = by-assoc-and (under (ε) (CCX02 • CX10) KB0280.proved) Eq.refl Eq.refl

  p1 : CCX01 • X0 • CX10 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
  p1 = by-assoc-and (under (CCX01 • X0) (ε) KB0219.proved) Eq.refl Eq.refl

  p2 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
  p3 = refl

  p4 : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
  p4 = refl

  p5 : X0 • CX10 • CCX01 • CCX02 • CX10 ≈ CCX01 • X0 • CX01 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
  p6 = sym p5

  proved : CCX01 • X0 • CX01 • CCX12 • CX01 ≈ X0 • CX10 • CCX01 • CCX02 • CX10
  proved = p6

module KB1264 where

  p0 : CCX02 • CCX01 • CX21 • CX20 ≈ CX21 • CCX01 • CCX02 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0329.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX01 • CX21 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
  p1 = by-assoc-and (under (CCX02 • CCX01) (ε) KB0043.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 • CX20 ≈ CX21 • CCX01 • CCX02 • CX20
  p3 = refl

  p4 : CCX02 • CCX01 • CX20 • CX21 ≈ CCX02 • CCX01 • CX20 • CX21
  p4 = refl

  p5 : CX21 • CCX01 • CCX02 • CX20 ≈ CCX02 • CCX01 • CX20 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CCX02 • CX20
  p6 = sym p5

  proved : CCX02 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CCX02 • CX20
  proved = p6

module KB2911 where

  p0 : CCX02 • CCX01 • CX20 • CX21 • CCX12 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB1264.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX01 • CX20 • CX21 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  p1 = by-assoc-and (under (CCX02 • CCX01) (ε) KB0179.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
  p3 = refl

  p4 : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX02 • CCX01 • CCX12 • CX21
  p4 = refl

  p5 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  proved = p5

module KB0968 where

  p0 : CX21 • CCX01 • CX21 • CX20 ≈ CX12 • CCX02 • CX12 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0217.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX01 • CX21 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
  p1 = by-assoc-and (under (CX21 • CCX01) (ε) KB0043.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX12 • CX20 ≈ CX12 • CCX02 • CX12 • CX20
  p3 = refl

  p4 : CX21 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CX20 • CX21
  p4 = refl

  p5 : CX12 • CCX02 • CX12 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • CCX01 • CX20 • CX21 ≈ CX12 • CCX02 • CX12 • CX20
  p6 = sym p5

  proved : CX21 • CCX01 • CX20 • CX21 ≈ CX12 • CCX02 • CX12 • CX20
  proved = p6

module KB2831 where

  p0 : CX21 • CCX01 • CX20 • CX21 • CCX12 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0968.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX01 • CX20 • CX21 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  p1 = by-assoc-and (under (CX21 • CCX01) (ε) KB0179.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
  p3 = refl

  p4 : CX21 • CCX01 • CCX12 • CX21 ≈ CX21 • CCX01 • CCX12 • CX21
  p4 = refl

  p5 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  proved = p5

module KB3180 where

  p0 : CCX01 • CCX02 • CCX01 • CX20 • CCX12 ≈ CCX01 • CCX02 • CX20 • CCX12 • CCX01
  p0 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0325.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • CX20 • CCX12 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
  p1 = by-assoc-and (under (ε) (CX20 • CCX12) KB0214.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX12 • CCX02 • CX12 • CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12 • CCX01
  p3 = refl

  p4 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  p4 = by-assoc-and (under (ε) (ε) KB2831.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • CX12 • CX20 • CCX12 ≈ CX21 • CCX01 • CCX12 • CX21
  p5 = trans p4 (refl)

  p6 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX01 • CCX02 • CX20 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21
  proved = p6

module KB3181 where

  p0 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB3180.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
  p1 = by-assoc-and (under (CCX01 • CCX02 • CX20 • CCX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21 • CCX01
  p3 = refl

  p4 : CCX01 • CCX02 • CX20 • CCX12 ≈ CCX01 • CCX02 • CX20 • CCX12
  p4 = refl

  p5 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
  proved = p5

module KB3182 where

  p0 : CX21 • CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02 • CX20 • CCX12
  p0 = by-assoc-and (under (CX21) (ε) KB3181.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX21 • CCX01) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX01 • CCX12 • CX21 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  p3 = by-assoc-and (under (ε) (ε) KB2911.proved) Eq.refl Eq.refl

  p4 : CX21 • CCX01 • CCX02 • CX20 • CCX12 ≈ CCX02 • CCX01 • CCX12 • CX21
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01
  p5 = refl

  p6 : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX01 • CCX12 • CX21 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX02 • CCX01 • CCX12 • CX21 ≈ CCX01 • CCX12 • CX21 • CCX01
  proved = p6

module KB3965 where

  p0 : CX02 • X0 • CX02 • CCX01 • CCX12 • X1 ≈ CX02 • X0 • CCX12 • X1 • CCX01
  p0 = by-assoc-and (under (CX02 • X0) (ε) KB0657.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • CX02 • CCX01 • CCX12 • X1 ≈ X0 • X2 • CCX01 • CCX12 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1) KB0160.proved) Eq.refl Eq.refl

  p2 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ CX02 • X0 • CCX12 • X1 • CCX01
  p3 = refl

  p4 : X0 • X2 • CCX01 • CCX12 • X1 ≈ X0 • X2 • CCX01 • CCX12 • X1
  p4 = refl

  p5 : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • X0 • CCX12 • X1 • CCX01 ≈ X0 • X2 • CCX01 • CCX12 • X1
  proved = p5

module KB0811 where

  p0 : CX20 • CCX12 • X1 • CCX01 • X1 ≈ CX20 • CCX12 • CX02 • CCX01
  p0 = by-assoc-and (under (CX20 • CCX12) (ε) KB0150.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX12 • X1 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0132.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX12 • CX02 • CCX01 ≈ X1 • CCX12 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX12 • CX02 • CCX01 ≈ CX20 • CX02 • CCX01 • CCX12
  p3 = by-assoc-and (under (CX20) (ε) KB0322.proved) Eq.refl Eq.refl

  p4 : CX20 • CX02 • CCX01 • CCX12 ≈ CX02 • SWAP02 • CCX01 • CCX12
  p4 = by-assoc-and (under (ε) (CCX01 • CCX12) KB0085.proved) Eq.refl Eq.refl

  p5 : CX02 • SWAP02 • CCX01 • CCX12 ≈ CX02 • CCX12 • SWAP02 • CCX12
  p5 = by-assoc-and (under (CX02) (CCX12) KB0104.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CCX01 • SWAP02
  p6 = by-assoc-and (under (CX02 • CCX12) (ε) KB0105.proved) Eq.refl Eq.refl

  p7 : CX20 • CCX12 • CX02 • CCX01 ≈ CX02 • CCX12 • CCX01 • SWAP02
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  p8 : X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1
  p8 = refl

  p9 : CX02 • CCX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1
  p9 = trans (sym p7) (trans p2 p8)

  proved : CX02 • CCX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1
  proved = p9

module KB0447 where

  p0 : CX10 • CCX12 • CX12 • CX02 ≈ CX12 • CCX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0141.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
  p1 = by-assoc-and (under (CX10 • CCX12) (ε) KB0027.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CX02 ≈ CX12 • CCX12 • CX02
  p3 = refl

  p4 : CX10 • CCX12 • CX02 • CX12 ≈ CX10 • CCX12 • CX02 • CX12
  p4 = refl

  p5 : CX12 • CCX12 • CX02 ≈ CX10 • CCX12 • CX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
  p6 = sym p5

  proved : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
  proved = p6

module KB0631 where

  p0 : CCX12 • CX10 • CX02 • CX12 ≈ CCX12 • CX02 • CX10
  p0 = by-assoc-and (under (CCX12) (ε) KB0311.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX10 • CX02 • CX12 ≈ CX10 • CCX12 • CX02 • CX12
  p1 = by-assoc-and (under (ε) (CX02 • CX12) KB0032.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX02 • CX10 ≈ CX10 • CCX12 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX02 • CX10 ≈ CCX12 • CX02 • CX10
  p3 = refl

  p4 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
  p4 = by-assoc-and (under (ε) (ε) KB0447.proved) Eq.refl Eq.refl

  p5 : CX10 • CCX12 • CX02 • CX12 ≈ CX12 • CCX12 • CX02
  p5 = trans p4 (refl)

  p6 : CCX12 • CX02 • CX10 ≈ CX12 • CCX12 • CX02
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX12 • CX02 • CX10 ≈ CX12 • CCX12 • CX02
  proved = p6

module KB3908 where

  p0 : CCX01 • CX20 • CCX12 • CX02 • CX10 ≈ CCX01 • CX20 • CX12 • CCX12 • CX02
  p0 = by-assoc-and (under (CCX01 • CX20) (ε) KB0631.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX20 • CCX12 • CX02 • CX10 ≈ CX20 • CCX12 • CCX01 • CX02 • CX10
  p1 = by-assoc-and (under (ε) (CX02 • CX10) KB0325.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX20 • CCX12 • CCX01 • CX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX10 • CCX01 • CX20 • CCX12 • CX02
  p3 = by-assoc-and (under (ε) (CCX12 • CX02) KB0294.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX01 • CX20 • CCX12 • CX02 ≈ CX10 • CX20 • CCX12 • CCX01 • CX02
  p4 = by-assoc-and (under (CX10) (CX02) KB0325.proved) Eq.refl Eq.refl

  p5 : CX10 • CX20 • CCX12 • CCX01 • CX02 ≈ CX10 • CX20 • CCX12 • CX02 • CCX01
  p5 = by-assoc-and (under (CX10 • CX20 • CCX12) (ε) KB0037.proved) Eq.refl Eq.refl

  p6 : CX10 • CX20 • CCX12 • CX02 • CCX01 ≈ CX10 • CX20 • CX02 • CCX01 • CCX12
  p6 = by-assoc-and (under (CX10 • CX20) (ε) KB0322.proved) Eq.refl Eq.refl

  p7 : CX10 • CX20 • CX02 • CCX01 • CCX12 ≈ CX10 • CX02 • SWAP02 • CCX01 • CCX12
  p7 = by-assoc-and (under (CX10) (CCX01 • CCX12) KB0085.proved) Eq.refl Eq.refl

  p8 : CX10 • CX02 • SWAP02 • CCX01 • CCX12 ≈ CX10 • CX02 • CCX12 • SWAP02 • CCX12
  p8 = by-assoc-and (under (CX10 • CX02) (CCX12) KB0104.proved) Eq.refl Eq.refl

  p9 : CX10 • CX02 • CCX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CX12 • SWAP02 • CCX12
  p9 = by-assoc-and (under (ε) (SWAP02 • CCX12) KB0315.proved) Eq.refl Eq.refl

  p10 : CX02 • CCX12 • CX12 • SWAP02 • CCX12 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
  p10 = by-assoc-and (under (CX02 • CCX12 • CX12) (ε) KB0105.proved) Eq.refl Eq.refl

  p11 : CCX01 • CX20 • CX12 • CCX12 • CX02 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
  p11 = trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))))

  p12 : CX20 • CCX12 • CCX01 • CX02 • CX10 ≈ CX20 • CCX12 • CX02 • CCX01 • CX10
  p12 = by-assoc-and (under (CX20 • CCX12) (CX10) KB0037.proved) Eq.refl Eq.refl

  p13 : CX20 • CCX12 • CX02 • CCX01 • CX10 ≈ CX20 • CX02 • CCX01 • CCX12 • CX10
  p13 = by-assoc-and (under (CX20) (CX10) KB0322.proved) Eq.refl Eq.refl

  p14 : CX20 • CX02 • CCX01 • CCX12 • CX10 ≈ CX02 • SWAP02 • CCX01 • CCX12 • CX10
  p14 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX10) KB0085.proved) Eq.refl Eq.refl

  p15 : CX02 • SWAP02 • CCX01 • CCX12 • CX10 ≈ CX02 • CCX12 • SWAP02 • CCX12 • CX10
  p15 = by-assoc-and (under (CX02) (CCX12 • CX10) KB0104.proved) Eq.refl Eq.refl

  p16 : CX02 • CCX12 • SWAP02 • CCX12 • CX10 ≈ CX02 • CCX12 • CCX01 • SWAP02 • CX10
  p16 = by-assoc-and (under (CX02 • CCX12) (CX10) KB0105.proved) Eq.refl Eq.refl

  p17 : CX02 • CCX12 • CCX01 • SWAP02 • CX10 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p17 = by-assoc-and (under (ε) (CX10) KB0811.proved) Eq.refl Eq.refl

  p18 : CX20 • CCX12 • CCX01 • CX02 • CX10 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p18 = trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (refl))))))

  p19 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p19 = trans (sym p11) (trans p2 p18)

  proved : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  proved = p19
