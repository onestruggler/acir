{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B015 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0008 ; module KB0010 ; module KB0011 ; module KB0014 ; module KB0023 ; module KB0027 ; module KB0029 ; module KB0033 ; module KB0035 ; module KB0040 ; module KB0046 ; module KB0118 ; module KB0120 ; module KB0129 ; module KB0136 ; module KB0147 ; module KB0153 ; module KB0166 ; module KB0186 ; module KB0191 ; module KB0308)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0002 ; module KB0086 ; module KB0099 ; module KB0119 ; module KB0122 ; module KB0123 ; module KB0124 ; module KB0176 ; module KB0212 ; module KB0218)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0004 ; module KB0005 ; module KB0016 ; module KB0032 ; module KB0045 ; module KB0063 ; module KB0074 ; module KB0090 ; module KB0096 ; module KB0141 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0047 ; module KB0057 ; module KB0087 ; module KB0131 ; module KB0135 ; module KB0140 ; module KB0168 ; module KB0315)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0017 ; module KB0076 ; module KB0079 ; module KB0080 ; module KB0085 ; module KB0104 ; module KB0107 ; module KB0108 ; module KB0132)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0102)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0130 ; module KB0188 ; module KB0325)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B009 using (module KB0179)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0069 ; module KB0105 ; module KB0170)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB1277)

module KB0515 where

  p0 : CX12 • X0 • CCX02 • X0 ≈ CX12 • CX21 • CCX02
  p0 = by-assoc-and (under (CX12) (ε) KB0166.proved) Eq.refl Eq.refl

  p1 : CX12 • X0 • CCX02 • X0 ≈ X0 • CX12 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • CX21 • CCX02 ≈ X0 • CX12 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CX12 • CX21 • CCX02 ≈ CX12 • CX21 • CCX02
  p3 = refl

  p4 : X0 • CX12 • CCX02 • X0 ≈ X0 • CX12 • CCX02 • X0
  p4 = refl

  p5 : CX12 • CX21 • CCX02 ≈ X0 • CX12 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CX12 • CCX02 • X0 ≈ CX12 • CX21 • CCX02
  p6 = sym p5

  proved : X0 • CX12 • CCX02 • X0 ≈ CX12 • CX21 • CCX02
  proved = p6

module decodeSWAP12 where

  p0 : SWAP12 ≈ SWAP12
  p0 = refl

  p1 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01
  p2 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • CCX02 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p3 : X0 • CX12 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
  p3 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX02 • CCX01) KB0515.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01
  p4 = by-assoc-and (under (CX12 • CX21) (CCX02 • CCX01) KB0308.proved) Eq.refl Eq.refl

  p5 : CX12 • CX21 • CX12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ SWAP12 • CCX01 • CCX02 • CCX02 • CCX01
  p5 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX02 • CCX01) KB0079.proved) Eq.refl Eq.refl

  p6 : SWAP12 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX02 • SWAP12 • CCX02 • CCX02 • CCX01
  p6 = by-assoc-and (under (ε) (CCX02 • CCX02 • CCX01) KB0107.proved) Eq.refl Eq.refl

  p7 : CCX02 • SWAP12 • CCX02 • CCX02 • CCX01 ≈ CCX02 • CCX01 • SWAP12 • CCX02 • CCX01
  p7 = by-assoc-and (under (CCX02) (CCX02 • CCX01) KB0108.proved) Eq.refl Eq.refl

  p8 : CCX02 • CCX01 • SWAP12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • CCX01 • SWAP12 • CCX01
  p8 = by-assoc-and (under (CCX02 • CCX01) (CCX01) KB0108.proved) Eq.refl Eq.refl

  p9 : CCX02 • CCX01 • CCX01 • SWAP12 • CCX01 ≈ CCX02 • SWAP12 • CCX01
  p9 = by-assoc-and (under (CCX02) (SWAP12 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p10 : CCX02 • SWAP12 • CCX01 ≈ CCX02 • CCX02 • SWAP12
  p10 = by-assoc-and (under (CCX02) (ε) KB0107.proved) Eq.refl Eq.refl

  p11 : CCX02 • CCX02 • SWAP12 ≈ SWAP12
  p11 = by-assoc-and (under (ε) (SWAP12) KB0010.proved) Eq.refl Eq.refl

  p12 : X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ SWAP12
  p12 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (refl)))))))))))

  proved : SWAP12 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01
  proved = trans p0 (sym p12)

module KB0058 where

  p0 : SWAP02 • SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX10
  p0 = by-assoc-and (under (SWAP02) (ε) KB0057.proved) Eq.refl Eq.refl

  p1 : SWAP02 • SWAP02 • CX12 • SWAP02 ≈ CX12 • SWAP02
  p1 = by-assoc-and (under (ε) (CX12 • SWAP02) KB0002.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CX10 ≈ CX12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CX10 ≈ SWAP02 • CX10
  p3 = refl

  p4 : CX12 • SWAP02 ≈ CX12 • SWAP02
  p4 = refl

  p5 : SWAP02 • CX10 ≈ CX12 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • CX10 ≈ CX12 • SWAP02
  proved = p5

module KB0146 where

  p0 : CX12 • CCX01 • CX10 • CX10 ≈ CX10 • CCX01 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0118.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • CX10 • CX10 ≈ CX12 • CCX01
  p1 = by-assoc-and (under (CX12 • CCX01) (ε) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CX10 ≈ CX10 • CCX01 • CX10
  p3 = refl

  p4 : CX12 • CCX01 ≈ CX12 • CCX01
  p4 = refl

  p5 : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
  proved = p5

module KB0239 where

  p0 : SWAP01 • CX01 • X1 ≈ CX01 • CX10 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0063.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CX01 • X1 ≈ SWAP01 • X1 • CX01
  p1 = by-assoc-and (under (SWAP01) (ε) KB0035.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • X1 ≈ SWAP01 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • X1 ≈ CX01 • CX10 • X1
  p3 = refl

  p4 : SWAP01 • X1 • CX01 ≈ X0 • SWAP01 • CX01
  p4 = by-assoc-and (under (ε) (CX01) KB0096.proved) Eq.refl Eq.refl

  p5 : X0 • SWAP01 • CX01 ≈ X0 • CX01 • CX10
  p5 = by-assoc-and (under (X0) (ε) KB0063.proved) Eq.refl Eq.refl

  p6 : SWAP01 • X1 • CX01 ≈ X0 • CX01 • CX10
  p6 = trans p4 (trans p5 (refl))

  p7 : CX01 • CX10 • X1 ≈ X0 • CX01 • CX10
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX01 • CX10 • X1 ≈ X0 • CX01 • CX10
  proved = p7

module KB0257 where

  p0 : CCX12 • CX20 • CX02 ≈ CCX12 • CX02 • SWAP02
  p0 = by-assoc-and (under (CCX12) (ε) KB0085.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX20 • CX02 ≈ CX20 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (CX02) KB0040.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX02 • SWAP02 ≈ CX20 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX02 • SWAP02 ≈ CCX12 • CX02 • SWAP02
  p3 = refl

  p4 : CX20 • CCX12 • CX02 ≈ CX20 • CCX12 • CX02
  p4 = refl

  p5 : CCX12 • CX02 • SWAP02 ≈ CX20 • CCX12 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • CX02 • SWAP02 ≈ CX20 • CCX12 • CX02
  proved = p5

module KB0287 where

  p0 : X2 • CX10 • CCX12 • CX12 ≈ CCX12 • X2 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0168.proved) Eq.refl Eq.refl

  p1 : X2 • CX10 • CCX12 • CX12 ≈ X2 • CX12 • CCX12
  p1 = by-assoc-and (under (X2) (ε) KB0141.proved) Eq.refl Eq.refl

  p2 : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • X2 • CX12 ≈ CCX12 • X2 • CX12
  p3 = refl

  p4 : X2 • CX12 • CCX12 ≈ X2 • CX12 • CCX12
  p4 = refl

  p5 : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
  proved = p5

module KB0372 where

  p0 : CX01 • CCX02 • CX02 • X2 ≈ CX02 • CCX02 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0119.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • CX02 • X2 ≈ CX01 • CCX02 • X2 • CX02
  p1 = by-assoc-and (under (CX01 • CCX02) (ε) KB0033.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX02 • X2 ≈ CX01 • CCX02 • X2 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX02 • X2 ≈ CX02 • CCX02 • X2
  p3 = refl

  p4 : CX01 • CCX02 • X2 • CX02 ≈ X2 • CCX02 • CX02
  p4 = by-assoc-and (under (ε) (CX02) KB0130.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX02 • X2 • CX02 ≈ X2 • CCX02 • CX02
  p5 = trans p4 (refl)

  p6 : CX02 • CCX02 • X2 ≈ X2 • CCX02 • CX02
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX02 • CCX02 • X2 ≈ X2 • CCX02 • CX02
  proved = p6

module KB0397 where

  p0 : CX01 • CX10 • CX01 • CX02 • CCX01 ≈ CX01 • CX10 • CCX01 • CX01
  p0 = by-assoc-and (under (CX01 • CX10) (ε) KB0123.proved) Eq.refl Eq.refl

  p1 : CX01 • CX10 • CX01 • CX02 • CCX01 ≈ SWAP01 • CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0087.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CCX01 • CX01 ≈ SWAP01 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CCX01 • CX01 ≈ CX01 • CX10 • CCX01 • CX01
  p3 = refl

  p4 : SWAP01 • CX02 • CCX01 ≈ CX12 • SWAP01 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01) KB0102.proved) Eq.refl Eq.refl

  p5 : CX12 • SWAP01 • CCX01 ≈ CX12 • CCX01 • SWAP01
  p5 = by-assoc-and (under (CX12) (ε) KB0074.proved) Eq.refl Eq.refl

  p6 : SWAP01 • CX02 • CCX01 ≈ CX12 • CCX01 • SWAP01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX01 • CX10 • CCX01 • CX01 ≈ CX12 • CCX01 • SWAP01
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX01 • CX10 • CCX01 • CX01 ≈ CX12 • CCX01 • SWAP01
  proved = p7

module KB0466 where

  p0 : CCX12 • CX10 • CX12 • CCX01 ≈ CCX12 • CCX01 • CX10
  p0 = by-assoc-and (under (CCX12) (ε) KB0147.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX10 • CX12 • CCX01 ≈ CX10 • CCX12 • CX12 • CCX01
  p1 = by-assoc-and (under (ε) (CX12 • CCX01) KB0032.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX01 • CX10 ≈ CX10 • CCX12 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX01 • CX10 ≈ CCX12 • CCX01 • CX10
  p3 = refl

  p4 : CX10 • CCX12 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01) KB0141.proved) Eq.refl Eq.refl

  p5 : CX10 • CCX12 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01
  p5 = trans p4 (refl)

  p6 : CCX12 • CCX01 • CX10 ≈ CX12 • CCX12 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX12 • CCX01 • CX10 ≈ CX12 • CCX12 • CCX01
  proved = p6

module KB0148 where

  p0 : CX01 • CCX02 • CX02 • CX02 ≈ CX02 • CCX02 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0119.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • CX02 • CX02 ≈ CX01 • CCX02
  p1 = by-assoc-and (under (CX01 • CCX02) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX02 • CX02 ≈ CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX02 • CX02 ≈ CX02 • CCX02 • CX02
  p3 = refl

  p4 : CX01 • CCX02 ≈ CX01 • CCX02
  p4 = refl

  p5 : CX02 • CCX02 • CX02 ≈ CX01 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX02 • CX02 ≈ CX01 • CCX02
  proved = p5

module KB0468 where

  p0 : SWAP02 • CX02 • CCX02 • CX02 ≈ SWAP02 • CX01 • CCX02
  p0 = by-assoc-and (under (SWAP02) (ε) KB0148.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX02 • CCX02 • CX02 ≈ CX02 • CX20 • CCX02 • CX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX02) KB0086.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CX01 • CCX02 ≈ CX02 • CX20 • CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CX01 • CCX02 ≈ CX21 • SWAP02 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0069.proved) Eq.refl Eq.refl

  p4 : CX21 • SWAP02 • CCX02 ≈ CX21 • CCX02 • SWAP02
  p4 = by-assoc-and (under (CX21) (ε) KB0076.proved) Eq.refl Eq.refl

  p5 : SWAP02 • CX01 • CCX02 ≈ CX21 • CCX02 • SWAP02
  p5 = trans p3 (trans p4 (refl))

  p6 : CX02 • CX20 • CCX02 • CX02 ≈ CX02 • CX20 • CCX02 • CX02
  p6 = refl

  p7 : CX21 • CCX02 • SWAP02 ≈ CX02 • CX20 • CCX02 • CX02
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX02 • CX20 • CCX02 • CX02 ≈ CX21 • CCX02 • SWAP02
  p8 = sym p7

  proved : CX02 • CX20 • CCX02 • CX02 ≈ CX21 • CCX02 • SWAP02
  proved = p8

module KB0484 where

  p0 : CCX12 • X0 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
  p0 = by-assoc-and (under (CCX12) (ε) KB0153.proved) Eq.refl Eq.refl

  p1 : CCX12 • X0 • CCX01 • X0 ≈ X0 • CCX12 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0046.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX12 • CCX01 ≈ X0 • CCX12 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX12 • CCX01 ≈ CCX12 • CX12 • CCX01
  p3 = refl

  p4 : X0 • CCX12 • CCX01 • X0 ≈ X0 • CCX12 • CCX01 • X0
  p4 = refl

  p5 : CCX12 • CX12 • CCX01 ≈ X0 • CCX12 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CCX12 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
  p6 = sym p5

  proved : X0 • CCX12 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
  proved = p6

module KB0167 where

  p0 : CX10 • CCX12 • X2 • X2 ≈ X2 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0131.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • X2 • X2 ≈ CX10 • CCX12
  p1 = by-assoc-and (under (CX10 • CCX12) (ε) KB0004.proved) Eq.refl Eq.refl

  p2 : X2 • CCX12 • X2 ≈ CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : X2 • CCX12 • X2 ≈ X2 • CCX12 • X2
  p3 = refl

  p4 : CX10 • CCX12 ≈ CX10 • CCX12
  p4 = refl

  p5 : X2 • CCX12 • X2 ≈ CX10 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CCX12 • X2 ≈ CX10 • CCX12
  proved = p5

module KB0520 where

  p0 : CCX01 • X2 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0167.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • CCX12 • X2 ≈ X2 • CCX01 • CCX12 • X2
  p1 = by-assoc-and (under (ε) (CCX12 • X2) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX10 • CCX12 ≈ X2 • CCX01 • CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX10 • CCX12 ≈ CCX01 • CX10 • CCX12
  p3 = refl

  p4 : X2 • CCX01 • CCX12 • X2 ≈ X2 • CCX01 • CCX12 • X2
  p4 = refl

  p5 : CCX01 • CX10 • CCX12 ≈ X2 • CCX01 • CCX12 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX01 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
  p6 = sym p5

  proved : X2 • CCX01 • CCX12 • X2 ≈ CCX01 • CX10 • CCX12
  proved = p6

module KB0753 where

  p0 : X0 • X1 • CX01 • CX02 • CCX01 ≈ CX01 • X0 • CX02 • CCX01
  p0 = by-assoc-and (under (ε) (CX02 • CCX01) KB0124.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX01 • CX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01
  p1 = by-assoc-and (under (X0 • X1) (ε) KB0123.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CX02 • CCX01 ≈ CX01 • X0 • CX02 • CCX01
  p3 = refl

  p4 : X0 • X1 • CCX01 • CX01 ≈ X0 • X1 • CCX01 • CX01
  p4 = refl

  p5 : CX01 • X0 • CX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • CX02 • CCX01 ≈ X0 • X1 • CCX01 • CX01
  proved = p5

module KB0775 where

  p0 : CX21 • CCX02 • CX20 • CX10 • CX12 ≈ CX20 • CCX02 • CX10 • CX12
  p0 = by-assoc-and (under (ε) (CX10 • CX12) KB0136.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • CX20 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
  p1 = by-assoc-and (under (CX21 • CCX02) (ε) KB0135.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX02 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX02 • CX10 • CX12 ≈ CX20 • CCX02 • CX10 • CX12
  p3 = refl

  p4 : CX21 • CCX02 • CX12 • CX20 ≈ CX21 • CCX02 • CX12 • CX20
  p4 = refl

  p5 : CX20 • CCX02 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • CCX02 • CX12 • CX20 ≈ CX20 • CCX02 • CX10 • CX12
  p6 = sym p5

  proved : CX21 • CCX02 • CX12 • CX20 ≈ CX20 • CCX02 • CX10 • CX12
  proved = p6

module KB0786 where

  p0 : CX10 • CCX12 • CX12 • CCX01 • X0 ≈ CX12 • CCX12 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (CCX01 • X0) KB0141.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CCX01 • X0 ≈ CX10 • CCX12 • X0 • CCX01
  p1 = by-assoc-and (under (CX10 • CCX12) (ε) KB0140.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CCX01 • X0 ≈ CX10 • CCX12 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CCX01 • X0 ≈ CX12 • CCX12 • CCX01 • X0
  p3 = refl

  p4 : CX10 • CCX12 • X0 • CCX01 ≈ CX10 • X0 • CCX12 • CCX01
  p4 = by-assoc-and (under (CX10) (CCX01) KB0046.proved) Eq.refl Eq.refl

  p5 : CX10 • X0 • CCX12 • CCX01 ≈ X0 • CX10 • CCX12 • CCX01
  p5 = by-assoc-and (under (ε) (CCX12 • CCX01) KB0047.proved) Eq.refl Eq.refl

  p6 : CX10 • CCX12 • X0 • CCX01 ≈ X0 • CX10 • CCX12 • CCX01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX12 • CCX12 • CCX01 • X0 ≈ X0 • CX10 • CCX12 • CCX01
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX12 • CCX12 • CCX01 • X0 ≈ X0 • CX10 • CCX12 • CCX01
  proved = p7

module KB0818 where

  p0 : CX21 • CCX02 • X0 • CCX01 • X0 ≈ CX21 • CCX02 • CX12 • CCX01
  p0 = by-assoc-and (under (CX21 • CCX02) (ε) KB0153.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0129.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • CCX01 ≈ X0 • CCX02 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • CCX01 ≈ CX21 • CX12 • CCX01 • CCX02
  p3 = by-assoc-and (under (CX21) (ε) KB0308.proved) Eq.refl Eq.refl

  p4 : CX21 • CX12 • CCX01 • CCX02 ≈ CX12 • SWAP12 • CCX01 • CCX02
  p4 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0080.proved) Eq.refl Eq.refl

  p5 : CX12 • SWAP12 • CCX01 • CCX02 ≈ CX12 • CCX02 • SWAP12 • CCX02
  p5 = by-assoc-and (under (CX12) (CCX02) KB0107.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX02 • SWAP12 • CCX02 ≈ CX12 • CCX02 • CCX01 • SWAP12
  p6 = by-assoc-and (under (CX12 • CCX02) (ε) KB0108.proved) Eq.refl Eq.refl

  p7 : CX21 • CCX02 • CX12 • CCX01 ≈ CX12 • CCX02 • CCX01 • SWAP12
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  p8 : X0 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0
  p8 = refl

  p9 : CX12 • CCX02 • CCX01 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0
  p9 = trans (sym p7) (trans p2 p8)

  proved : CX12 • CCX02 • CCX01 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0
  proved = p9

module KB0915 where

  p0 : CX02 • X0 • X2 • CCX12 • X2 ≈ X0 • CX02 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (CCX12 • X2) KB0191.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • X2 • CCX12 • X2 ≈ CX02 • X0 • CX10 • CCX12
  p1 = by-assoc-and (under (CX02 • X0) (ε) KB0167.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX12 • X2 ≈ CX02 • X0 • CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : X0 • CX02 • CCX12 • X2 ≈ X0 • CX02 • CCX12 • X2
  p3 = refl

  p4 : CX02 • X0 • CX10 • CCX12 ≈ CX02 • X0 • CX10 • CCX12
  p4 = refl

  p5 : X0 • CX02 • CCX12 • X2 ≈ CX02 • X0 • CX10 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • X0 • CX10 • CCX12 ≈ X0 • CX02 • CCX12 • X2
  p6 = sym p5

  proved : CX02 • X0 • CX10 • CCX12 ≈ X0 • CX02 • CCX12 • X2
  proved = p6

module KB0277 where

  p0 : CX20 • SWAP02 • CCX12 ≈ CX20 • CCX01 • SWAP02
  p0 = by-assoc-and (under (CX20) (ε) KB0105.proved) Eq.refl Eq.refl

  p1 : CX20 • SWAP02 • CCX12 ≈ CX02 • CX20 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12) KB0099.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • SWAP02 ≈ CX20 • CCX01 • SWAP02
  p3 = refl

  p4 : CX02 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12
  p4 = refl

  p5 : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CCX01 • SWAP02 ≈ CX02 • CX20 • CCX12
  proved = p5

module KB0169 where

  p0 : CX20 • CCX12 • X1 • X1 ≈ X1 • CCX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0132.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX12 • X1 • X1 ≈ CX20 • CCX12
  p1 = by-assoc-and (under (CX20 • CCX12) (ε) KB0003.proved) Eq.refl Eq.refl

  p2 : X1 • CCX12 • X1 ≈ CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : X1 • CCX12 • X1 ≈ X1 • CCX12 • X1
  p3 = refl

  p4 : CX20 • CCX12 ≈ CX20 • CCX12
  p4 = refl

  p5 : X1 • CCX12 • X1 ≈ CX20 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CCX12 • X1 ≈ CX20 • CCX12
  proved = p5

module KB0854 where

  p0 : CX02 • CCX01 • X1 • CCX12 • X1 ≈ CX02 • CCX01 • CX20 • CCX12
  p0 = by-assoc-and (under (CX02 • CCX01) (ε) KB0169.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • CCX12 • X1 ≈ X1 • CCX01 • CCX12 • X1
  p1 = by-assoc-and (under (ε) (CCX12 • X1) KB0120.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • CX20 • CCX12 ≈ X1 • CCX01 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12 • CCX01
  p3 = by-assoc-and (under (CX02) (ε) KB0325.proved) Eq.refl Eq.refl

  p4 : CX02 • CCX01 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12 • CCX01
  p4 = trans p3 (refl)

  p5 : X1 • CCX01 • CCX12 • X1 ≈ X1 • CCX01 • CCX12 • X1
  p5 = refl

  p6 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
  proved = p6

module KB1156 where

  p0 : CX20 • CCX01 • SWAP02 • CCX01 ≈ CX02 • CX20 • CCX12 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0277.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX01 • SWAP02 • CCX01 ≈ CX20 • CCX01 • CCX12 • SWAP02
  p1 = by-assoc-and (under (CX20 • CCX01) (ε) KB0104.proved) Eq.refl Eq.refl

  p2 : CX02 • CX20 • CCX12 • CCX01 ≈ CX20 • CCX01 • CCX12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
  p3 = by-assoc-and (under (ε) (ε) KB0854.proved) Eq.refl Eq.refl

  p4 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
  p4 = trans p3 (refl)

  p5 : CX20 • CCX01 • CCX12 • SWAP02 ≈ CX20 • CCX01 • CCX12 • SWAP02
  p5 = refl

  p6 : X1 • CCX01 • CCX12 • X1 ≈ CX20 • CCX01 • CCX12 • SWAP02
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX20 • CCX01 • CCX12 • SWAP02 ≈ X1 • CCX01 • CCX12 • X1
  p7 = sym p6

  proved : CX20 • CCX01 • CCX12 • SWAP02 ≈ X1 • CCX01 • CCX12 • X1
  proved = p7

module KB0199 where

  p0 : CX20 • CX21 • CCX02 • CCX02 ≈ CCX02 • CX20 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0176.proved) Eq.refl Eq.refl

  p1 : CX20 • CX21 • CCX02 • CCX02 ≈ CX20 • CX21
  p1 = by-assoc-and (under (CX20 • CX21) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX20 • CCX02 ≈ CCX02 • CX20 • CCX02
  p3 = refl

  p4 : CX20 • CX21 ≈ CX20 • CX21
  p4 = refl

  p5 : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX20 • CCX02 ≈ CX20 • CX21
  proved = p5

module KB0209 where

  p0 : CCX02 • CCX02 • CX20 • CCX02 ≈ CCX02 • CX20 • CX21
  p0 = by-assoc-and (under (CCX02) (ε) KB0199.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CX20 • CCX02 ≈ CX20 • CCX02
  p1 = by-assoc-and (under (ε) (CX20 • CCX02) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX20 • CX21 ≈ CX20 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX20 • CX21 ≈ CCX02 • CX20 • CX21
  p3 = refl

  p4 : CX20 • CCX02 ≈ CX20 • CCX02
  p4 = refl

  p5 : CCX02 • CX20 • CX21 ≈ CX20 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX20 • CX21 ≈ CX20 • CCX02
  proved = p5

module KB0295 where

  p0 : CCX02 • CX20 • CX21 • CCX12 ≈ CX20 • CCX02 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0209.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX20 • CX21 • CCX12 ≈ CCX02 • CCX12 • CX21
  p1 = by-assoc-and (under (CCX02) (ε) KB0179.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX02 • CCX12 ≈ CCX02 • CCX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX02 • CCX12 ≈ CX20 • CCX02 • CCX12
  p3 = refl

  p4 : CCX02 • CCX12 • CX21 ≈ CCX02 • CCX12 • CX21
  p4 = refl

  p5 : CX20 • CCX02 • CCX12 ≈ CCX02 • CCX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX12 • CX21 ≈ CX20 • CCX02 • CCX12
  p6 = sym p5

  proved : CCX02 • CCX12 • CX21 ≈ CX20 • CCX02 • CCX12
  proved = p6

module KB1190 where

  p0 : CCX02 • CCX12 • CX21 • CX12 ≈ CX20 • CCX02 • CCX12 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0295.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX12 • CX21 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
  p1 = by-assoc-and (under (CCX02 • CCX12) (ε) KB0080.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX02 • CCX12 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX02 • CCX12 • CX12 ≈ CX20 • CCX02 • CCX12 • CX12
  p3 = refl

  p4 : CCX02 • CCX12 • CX12 • SWAP12 ≈ CCX02 • CCX12 • CX12 • SWAP12
  p4 = refl

  p5 : CX20 • CCX02 • CCX12 • CX12 ≈ CCX02 • CCX12 • CX12 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX12 • CX12 • SWAP12 ≈ CX20 • CCX02 • CCX12 • CX12
  p6 = sym p5

  proved : CCX02 • CCX12 • CX12 • SWAP12 ≈ CX20 • CCX02 • CCX12 • CX12
  proved = p6

module KB0326 where

  p0 : CCX12 • CCX01 • CCX12 • CCX12 ≈ CX20 • CCX01 • CX20 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0212.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX01 • CCX12 • CCX12 ≈ CCX12 • CCX01
  p1 = by-assoc-and (under (CCX12 • CCX01) (ε) KB0014.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CX20 • CCX12 ≈ CCX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CX20 • CCX12 ≈ CX02 • CCX12 • CX02 • CCX12
  p3 = by-assoc-and (under (ε) (CCX12) KB0218.proved) Eq.refl Eq.refl

  p4 : CX20 • CCX01 • CX20 • CCX12 ≈ CX02 • CCX12 • CX02 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX01 ≈ CCX12 • CCX01
  p5 = refl

  p6 : CX02 • CCX12 • CX02 • CCX12 ≈ CCX12 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX02 • CCX12 • CX02 • CCX12 ≈ CCX12 • CCX01
  proved = p6

module KB0327 where

  p0 : CX02 • CX02 • CCX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB0326.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX12 • CX02 • CCX12 ≈ CCX12 • CX02 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX02 • CCX12) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CCX01 ≈ CCX12 • CX02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CCX01 ≈ CX02 • CCX12 • CCX01
  p3 = refl

  p4 : CCX12 • CX02 • CCX12 ≈ CCX12 • CX02 • CCX12
  p4 = refl

  p5 : CX02 • CCX12 • CCX01 ≈ CCX12 • CX02 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CCX01
  p6 = sym p5

  proved : CCX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CCX01
  proved = p6

module KB0530 where

  p0 : CX02 • X1 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
  p0 = by-assoc-and (under (CX02) (ε) KB0170.proved) Eq.refl Eq.refl

  p1 : CX02 • X1 • CX20 • CCX12 ≈ X1 • CX02 • CX20 • CCX12
  p1 = by-assoc-and (under (ε) (CX20 • CCX12) KB0023.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • X1 ≈ X1 • CX02 • CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • X1 ≈ CX02 • CCX12 • X1
  p3 = refl

  p4 : X1 • CX02 • CX20 • CCX12 ≈ X1 • CX02 • CX20 • CCX12
  p4 = refl

  p5 : CX02 • CCX12 • X1 ≈ X1 • CX02 • CX20 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CX02 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
  p6 = sym p5

  proved : X1 • CX02 • CX20 • CCX12 ≈ CX02 • CCX12 • X1
  proved = p6

module KB0203 where

  p0 : CCX01 • CCX01 • X1 • CCX01 ≈ CCX01 • X1 • CX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0186.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • X1 • CCX01 ≈ X1 • CCX01
  p1 = by-assoc-and (under (ε) (X1 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • X1 • CX02 ≈ X1 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • X1 • CX02 ≈ CCX01 • X1 • CX02
  p3 = refl

  p4 : X1 • CCX01 ≈ X1 • CCX01
  p4 = refl

  p5 : CCX01 • X1 • CX02 ≈ X1 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X1 • CX02 ≈ X1 • CCX01
  proved = p5

module KB0572 where

  p0 : SWAP02 • CCX01 • X1 • CX02 ≈ SWAP02 • X1 • CCX01
  p0 = by-assoc-and (under (SWAP02) (ε) KB0203.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CCX01 • X1 • CX02 ≈ CCX12 • SWAP02 • X1 • CX02
  p1 = by-assoc-and (under (ε) (X1 • CX02) KB0104.proved) Eq.refl Eq.refl

  p2 : SWAP02 • X1 • CCX01 ≈ CCX12 • SWAP02 • X1 • CX02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • X1 • CCX01 ≈ X1 • SWAP02 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0017.proved) Eq.refl Eq.refl

  p4 : X1 • SWAP02 • CCX01 ≈ X1 • CCX12 • SWAP02
  p4 = by-assoc-and (under (X1) (ε) KB0104.proved) Eq.refl Eq.refl

  p5 : SWAP02 • X1 • CCX01 ≈ X1 • CCX12 • SWAP02
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX12 • SWAP02 • X1 • CX02 ≈ CCX12 • X1 • SWAP02 • CX02
  p6 = by-assoc-and (under (CCX12) (CX02) KB0017.proved) Eq.refl Eq.refl

  p7 : CCX12 • X1 • SWAP02 • CX02 ≈ CCX12 • X1 • CX02 • CX20
  p7 = by-assoc-and (under (CCX12 • X1) (ε) KB0086.proved) Eq.refl Eq.refl

  p8 : CCX12 • SWAP02 • X1 • CX02 ≈ CCX12 • X1 • CX02 • CX20
  p8 = trans p6 (trans p7 (refl))

  p9 : X1 • CCX12 • SWAP02 ≈ CCX12 • X1 • CX02 • CX20
  p9 = trans (sym p5) (trans p2 p8)

  p10 : CCX12 • X1 • CX02 • CX20 ≈ X1 • CCX12 • SWAP02
  p10 = sym p9

  proved : CCX12 • X1 • CX02 • CX20 ≈ X1 • CCX12 • SWAP02
  proved = p10

module KB1332 where

  p0 : CCX12 • X1 • CX02 • CX20 • CCX12 ≈ X1 • CCX12 • SWAP02 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0572.proved) Eq.refl Eq.refl

  p1 : CCX12 • X1 • CX02 • CX20 • CCX12 ≈ CCX12 • CX02 • CCX12 • X1
  p1 = by-assoc-and (under (CCX12) (ε) KB0530.proved) Eq.refl Eq.refl

  p2 : X1 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • CX02 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : X1 • CCX12 • SWAP02 • CCX12 ≈ X1 • CCX12 • CCX01 • SWAP02
  p3 = by-assoc-and (under (X1 • CCX12) (ε) KB0105.proved) Eq.refl Eq.refl

  p4 : X1 • CCX12 • SWAP02 • CCX12 ≈ X1 • CCX12 • CCX01 • SWAP02
  p4 = trans p3 (refl)

  p5 : CCX12 • CX02 • CCX12 • X1 ≈ CX02 • CCX12 • CCX01 • X1
  p5 = by-assoc-and (under (ε) (X1) KB0327.proved) Eq.refl Eq.refl

  p6 : CCX12 • CX02 • CCX12 • X1 ≈ CX02 • CCX12 • CCX01 • X1
  p6 = trans p5 (refl)

  p7 : X1 • CCX12 • CCX01 • SWAP02 ≈ CX02 • CCX12 • CCX01 • X1
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CX02 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • SWAP02
  p8 = sym p7

  proved : CX02 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • SWAP02
  proved = p8

module KB1360 where

  p0 : CX10 • CX02 • CCX12 • CX02 • CCX12 ≈ CX10 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX10) (ε) KB0326.proved) Eq.refl Eq.refl

  p1 : CX10 • CX02 • CCX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX12 • CX02 • CCX12
  p1 = by-assoc-and (under (ε) (CX02 • CCX12) KB0315.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX12 • CX02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX01 ≈ CX10 • CCX12 • CCX01
  p3 = refl

  p4 : CX02 • CCX12 • CX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
  p4 = by-assoc-and (under (CX02 • CCX12) (CCX12) KB0027.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX12 • CX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
  p5 = trans p4 (refl)

  p6 : CX10 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CX10 • CCX12 • CCX01
  p7 = sym p6

  proved : CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CX10 • CCX12 • CCX01
  proved = p7

module KB1361 where

  p0 : CX02 • CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CX02 • CX10 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB1360.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CCX12 • CX02 • CX12 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX02 • CX12 • CCX12) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CX10 • CCX12 • CCX01 ≈ CCX12 • CX02 • CX12 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CX10 • CCX12 • CCX01 ≈ CX02 • CX10 • CCX12 • CCX01
  p3 = refl

  p4 : CCX12 • CX02 • CX12 • CCX12 ≈ CCX12 • CX02 • CX12 • CCX12
  p4 = refl

  p5 : CX02 • CX10 • CCX12 • CCX01 ≈ CCX12 • CX02 • CX12 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CX02 • CX12 • CCX12 ≈ CX02 • CX10 • CCX12 • CCX01
  p6 = sym p5

  proved : CCX12 • CX02 • CX12 • CCX12 ≈ CX02 • CX10 • CCX12 • CCX01
  proved = p6

module KB0388 where

  p0 : SWAP01 • X2 • CX01 • CCX02 ≈ SWAP01 • CCX02 • X2
  p0 = by-assoc-and (under (SWAP01) (ε) KB0122.proved) Eq.refl Eq.refl

  p1 : SWAP01 • X2 • CX01 • CCX02 ≈ X2 • SWAP01 • CX01 • CCX02
  p1 = by-assoc-and (under (ε) (CX01 • CCX02) KB0016.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CCX02 • X2 ≈ X2 • SWAP01 • CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CCX02 • X2 ≈ CCX12 • SWAP01 • X2
  p3 = by-assoc-and (under (ε) (X2) KB0090.proved) Eq.refl Eq.refl

  p4 : CCX12 • SWAP01 • X2 ≈ CCX12 • X2 • SWAP01
  p4 = by-assoc-and (under (CCX12) (ε) KB0016.proved) Eq.refl Eq.refl

  p5 : SWAP01 • CCX02 • X2 ≈ CCX12 • X2 • SWAP01
  p5 = trans p3 (trans p4 (refl))

  p6 : X2 • SWAP01 • CX01 • CCX02 ≈ X2 • CX01 • CX10 • CCX02
  p6 = by-assoc-and (under (X2) (CCX02) KB0063.proved) Eq.refl Eq.refl

  p7 : X2 • SWAP01 • CX01 • CCX02 ≈ X2 • CX01 • CX10 • CCX02
  p7 = trans p6 (refl)

  p8 : CCX12 • X2 • SWAP01 ≈ X2 • CX01 • CX10 • CCX02
  p8 = trans (sym p5) (trans p2 p7)

  p9 : X2 • CX01 • CX10 • CCX02 ≈ CCX12 • X2 • SWAP01
  p9 = sym p8

  proved : X2 • CX01 • CX10 • CCX02 ≈ CCX12 • X2 • SWAP01
  proved = p9

module KB1309 where

  p0 : CCX02 • X2 • CX01 • CX10 • CCX02 ≈ CCX02 • CCX12 • X2 • SWAP01
  p0 = by-assoc-and (under (CCX02) (ε) KB0388.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • CX10 • CCX02 ≈ X2 • CCX02 • CX10 • CCX02
  p1 = by-assoc-and (under (ε) (CX10 • CCX02) KB0188.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CCX02 • CX10 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX12 • X2 • SWAP01 ≈ CCX02 • CCX12 • X2 • SWAP01
  p3 = refl

  p4 : X2 • CCX02 • CX10 • CCX02 ≈ X2 • CX10 • CCX02 • CCX12
  p4 = by-assoc-and (under (X2) (ε) KB1277.proved) Eq.refl Eq.refl

  p5 : X2 • CCX02 • CX10 • CCX02 ≈ X2 • CX10 • CCX02 • CCX12
  p5 = trans p4 (refl)

  p6 : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CX10 • CCX02 • CCX12
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX02 • CCX12 • X2 • SWAP01 ≈ X2 • CX10 • CCX02 • CCX12
  proved = p6

module KB1394 where

  p0 : CCX02 • CCX02 • CCX12 • X2 • SWAP01 ≈ CCX02 • X2 • CX10 • CCX02 • CCX12
  p0 = by-assoc-and (under (CCX02) (ε) KB1309.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CCX12 • X2 • SWAP01 ≈ CCX12 • X2 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX12 • X2 • SWAP01) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX02 • X2 • CX10 • CCX02 • CCX12
  p3 = refl

  p4 : CCX12 • X2 • SWAP01 ≈ CCX12 • X2 • SWAP01
  p4 = refl

  p5 : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X2 • CX10 • CCX02 • CCX12 ≈ CCX12 • X2 • SWAP01
  proved = p5
