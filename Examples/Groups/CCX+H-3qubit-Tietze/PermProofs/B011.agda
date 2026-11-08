{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B011 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX21 ; SWAP01 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0006 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0026 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0033 ; module KB0116 ; module KB0127 ; module KB0153 ; module KB0164 ; module KB0166 ; module KB0213 ; module KB0217 ; module KB0219)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0025 ; module KB0126 ; module KB0137)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0000 ; module KB0045 ; module KB0149 ; module KB0150 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0088 ; module KB0115 ; module KB0117 ; module KB0140 ; module KB0280 ; module KB0310)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0100 ; module KB0102 ; module KB0261)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0130)

module decodeCX21 where

  p0 : CX21 ≈ CX21
  p0 = refl

  p1 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p1 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0153.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p2 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0140.proved) Eq.refl Eq.refl

  p3 : X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p3 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p4 : X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • CCX01 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p4 = by-assoc-and (under (X0 • CCX02 • CCX01) (CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p5 : X0 • CCX02 • CCX01 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX02 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p5 = by-assoc-and (under (X0 • CCX02) (X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p6 : X0 • CCX02 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p6 = by-assoc-and (under (ε) (CCX01 • CCX01 • CCX02 • CCX01 • CCX01) KB0166.proved) Eq.refl Eq.refl

  p7 : CX21 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX02 • CCX02 • CCX01 • CCX01
  p7 = by-assoc-and (under (CX21 • CCX02) (CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p8 : CX21 • CCX02 • CCX02 • CCX01 • CCX01 ≈ CX21 • CCX01 • CCX01
  p8 = by-assoc-and (under (CX21) (CCX01 • CCX01) KB0010.proved) Eq.refl Eq.refl

  p9 : CX21 • CCX01 • CCX01 ≈ CX21
  p9 = by-assoc-and (under (CX21) (ε) KB0011.proved) Eq.refl Eq.refl

  p10 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CX21
  p10 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl)))))))))

  proved : CX21 ≈ X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  proved = trans p0 (sym p10)

module KB0163 where

  p0 : CX12 • CX12 • CX01 • CX02 ≈ CX12 • CX01 • CX12
  p0 = by-assoc-and (under (CX12) (ε) KB0127.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CX01 • CX02 ≈ CX01 • CX02
  p1 = by-assoc-and (under (ε) (CX01 • CX02) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • CX12 ≈ CX01 • CX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX12
  p3 = refl

  p4 : CX01 • CX02 ≈ CX01 • CX02
  p4 = refl

  p5 : CX12 • CX01 • CX12 ≈ CX01 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX01 • CX12 ≈ CX01 • CX02
  proved = p5

module KB0355 where

  p0 : CX12 • X0 • CX10 • X1 ≈ CX12 • X1 • CX10
  p0 = by-assoc-and (under (CX12) (ε) KB0115.proved) Eq.refl Eq.refl

  p1 : CX12 • X0 • CX10 • X1 ≈ X0 • CX12 • CX10 • X1
  p1 = by-assoc-and (under (ε) (CX10 • X1) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • X1 • CX10 ≈ X0 • CX12 • CX10 • X1
  p2 = trans (sym p0) p1

  p3 : CX12 • X1 • CX10 ≈ CX12 • X1 • CX10
  p3 = refl

  p4 : X0 • CX12 • CX10 • X1 ≈ X0 • CX10 • CX12 • X1
  p4 = by-assoc-and (under (X0) (X1) KB0026.proved) Eq.refl Eq.refl

  p5 : X0 • CX12 • CX10 • X1 ≈ X0 • CX10 • CX12 • X1
  p5 = trans p4 (refl)

  p6 : CX12 • X1 • CX10 ≈ X0 • CX10 • CX12 • X1
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X0 • CX10 • CX12 • X1 ≈ CX12 • X1 • CX10
  p7 = sym p6

  proved : X0 • CX10 • CX12 • X1 ≈ CX12 • X1 • CX10
  proved = p7

module KB0357 where

  p0 : CX10 • X2 • CX12 • X1 ≈ CX10 • X1 • CX12
  p0 = by-assoc-and (under (CX10) (ε) KB0116.proved) Eq.refl Eq.refl

  p1 : CX10 • X2 • CX12 • X1 ≈ X2 • CX10 • CX12 • X1
  p1 = by-assoc-and (under (ε) (CX12 • X1) KB0021.proved) Eq.refl Eq.refl

  p2 : CX10 • X1 • CX12 ≈ X2 • CX10 • CX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX10 • X1 • CX12 ≈ CX10 • X1 • CX12
  p3 = refl

  p4 : X2 • CX10 • CX12 • X1 ≈ X2 • CX10 • CX12 • X1
  p4 = refl

  p5 : CX10 • X1 • CX12 ≈ X2 • CX10 • CX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CX10 • CX12 • X1 ≈ CX10 • X1 • CX12
  p6 = sym p5

  proved : X2 • CX10 • CX12 • X1 ≈ CX10 • X1 • CX12
  proved = p6

module KB0777 where

  p0 : CX02 • CCX01 • CX01 • CCX02 • X2 ≈ CX01 • CCX01 • CCX02 • X2
  p0 = by-assoc-and (under (ε) (CCX02 • X2) KB0137.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • CX01 • CCX02 • X2 ≈ CX02 • CCX01 • X2 • CCX02
  p1 = by-assoc-and (under (CX02 • CCX01) (ε) KB0130.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CCX02 • X2 ≈ CX02 • CCX01 • X2 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CCX02 • X2 ≈ CX01 • CCX01 • CCX02 • X2
  p3 = refl

  p4 : CX02 • CCX01 • X2 • CCX02 ≈ CX02 • X2 • CCX01 • CCX02
  p4 = by-assoc-and (under (CX02) (CCX02) KB0029.proved) Eq.refl Eq.refl

  p5 : CX02 • X2 • CCX01 • CCX02 ≈ X2 • CX02 • CCX01 • CCX02
  p5 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0033.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX01 • X2 • CCX02 ≈ X2 • CX02 • CCX01 • CCX02
  p6 = trans p4 (trans p5 (refl))

  p7 : CX01 • CCX01 • CCX02 • X2 ≈ X2 • CX02 • CCX01 • CCX02
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX01 • CCX01 • CCX02 • X2 ≈ X2 • CX02 • CCX01 • CCX02
  proved = p7

module KB0311 where

  p0 : CX02 • CX10 • CX12 • CX12 ≈ CX10 • CX02 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0310.proved) Eq.refl Eq.refl

  p1 : CX02 • CX10 • CX12 • CX12 ≈ CX02 • CX10
  p1 = by-assoc-and (under (CX02 • CX10) (ε) KB0006.proved) Eq.refl Eq.refl

  p2 : CX10 • CX02 • CX12 ≈ CX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CX02 • CX12 ≈ CX10 • CX02 • CX12
  p3 = refl

  p4 : CX02 • CX10 ≈ CX02 • CX10
  p4 = refl

  p5 : CX10 • CX02 • CX12 ≈ CX02 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX02 • CX12 ≈ CX02 • CX10
  proved = p5

module KB1658 where

  p0 : CX10 • CCX02 • CX10 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CX10
  p0 = by-assoc-and (under (CX10 • CCX02) (ε) KB0311.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX02 • CX10 • CX02 • CX12 ≈ CX01 • CCX12 • CX01 • CX02 • CX12
  p1 = by-assoc-and (under (ε) (CX02 • CX12) KB0219.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX01 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CX02 • CX10 ≈ CX10 • CCX02 • CX02 • CX10
  p3 = refl

  p4 : CX01 • CCX12 • CX01 • CX02 • CX12 ≈ CX01 • CCX12 • CX12 • CX01
  p4 = by-assoc-and (under (CX01 • CCX12) (ε) KB0164.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • CX01 • CX02 • CX12 ≈ CX01 • CCX12 • CX12 • CX01
  p5 = trans p4 (refl)

  p6 : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01
  proved = p6

module KB0101 where

  p0 : SWAP01 • SWAP01 • CX02 • SWAP01 ≈ SWAP01 • CX12
  p0 = by-assoc-and (under (SWAP01) (ε) KB0100.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • CX02 • SWAP01 ≈ CX02 • SWAP01
  p1 = by-assoc-and (under (ε) (CX02 • SWAP01) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CX12 ≈ CX02 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CX12 ≈ SWAP01 • CX12
  p3 = refl

  p4 : CX02 • SWAP01 ≈ CX02 • SWAP01
  p4 = refl

  p5 : SWAP01 • CX12 ≈ CX02 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CX12 ≈ CX02 • SWAP01
  proved = p5

module KB0285 where

  p0 : CX12 • CX01 • CX02 • CCX02 ≈ CX12 • CCX02 • CX02
  p0 = by-assoc-and (under (CX12) (ε) KB0149.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX02 • CCX02 ≈ CX01 • CX12 • CCX02
  p1 = by-assoc-and (under (ε) (CCX02) KB0127.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX02 ≈ CX12 • CCX02 • CX02
  p3 = refl

  p4 : CX01 • CX12 • CCX02 ≈ CX01 • CX12 • CCX02
  p4 = refl

  p5 : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CCX02 • CX02 ≈ CX01 • CX12 • CCX02
  proved = p5

module KB1661 where

  p0 : CX10 • CX02 • CX12 • CCX02 • CX02 ≈ CX02 • CX10 • CCX02 • CX02
  p0 = by-assoc-and (under (ε) (CCX02 • CX02) KB0311.proved) Eq.refl Eq.refl

  p1 : CX10 • CX02 • CX12 • CCX02 • CX02 ≈ CX10 • CX02 • CX01 • CX12 • CCX02
  p1 = by-assoc-and (under (CX10 • CX02) (ε) KB0285.proved) Eq.refl Eq.refl

  p2 : CX02 • CX10 • CCX02 • CX02 ≈ CX10 • CX02 • CX01 • CX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX10 • CCX02 • CX02 ≈ CX02 • CX10 • CCX02 • CX02
  p3 = refl

  p4 : CX10 • CX02 • CX01 • CX12 • CCX02 ≈ CX10 • CX01 • CX02 • CX12 • CCX02
  p4 = by-assoc-and (under (CX10) (CX12 • CCX02) KB0025.proved) Eq.refl Eq.refl

  p5 : CX10 • CX01 • CX02 • CX12 • CCX02 ≈ CX01 • SWAP01 • CX02 • CX12 • CCX02
  p5 = by-assoc-and (under (ε) (CX02 • CX12 • CCX02) KB0088.proved) Eq.refl Eq.refl

  p6 : CX01 • SWAP01 • CX02 • CX12 • CCX02 ≈ CX01 • CX12 • SWAP01 • CX12 • CCX02
  p6 = by-assoc-and (under (CX01) (CX12 • CCX02) KB0102.proved) Eq.refl Eq.refl

  p7 : CX01 • CX12 • SWAP01 • CX12 • CCX02 ≈ CX01 • CX12 • CX02 • SWAP01 • CCX02
  p7 = by-assoc-and (under (CX01 • CX12) (CCX02) KB0101.proved) Eq.refl Eq.refl

  p8 : CX01 • CX12 • CX02 • SWAP01 • CCX02 ≈ CX01 • CX02 • CX12 • SWAP01 • CCX02
  p8 = by-assoc-and (under (CX01) (SWAP01 • CCX02) KB0027.proved) Eq.refl Eq.refl

  p9 : CX01 • CX02 • CX12 • SWAP01 • CCX02 ≈ CX12 • CX01 • SWAP01 • CCX02
  p9 = by-assoc-and (under (ε) (SWAP01 • CCX02) KB0164.proved) Eq.refl Eq.refl

  p10 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
  p10 = by-assoc-and (under (ε) (CCX02) KB0261.proved) Eq.refl Eq.refl

  p11 : CX10 • CX02 • CX01 • CX12 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
  p11 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl)))))))

  p12 : CX02 • CX10 • CCX02 • CX02 ≈ CX10 • CX12 • CX01 • CCX02
  p12 = trans (sym p3) (trans p2 p11)

  p13 : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
  p13 = sym p12

  proved : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
  proved = p13

module KB0472 where

  p0 : CCX02 • X1 • CCX01 • X1 ≈ CCX02 • CX02 • CCX01
  p0 = by-assoc-and (under (CCX02) (ε) KB0150.proved) Eq.refl Eq.refl

  p1 : CCX02 • X1 • CCX01 • X1 ≈ X1 • CCX02 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0028.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX02 • CCX01 ≈ X1 • CCX02 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX02 • CCX01 ≈ CCX02 • CX02 • CCX01
  p3 = refl

  p4 : X1 • CCX02 • CCX01 • X1 ≈ X1 • CCX02 • CCX01 • X1
  p4 = refl

  p5 : CCX02 • CX02 • CCX01 ≈ X1 • CCX02 • CCX01 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CCX02 • CCX01 • X1 ≈ CCX02 • CX02 • CCX01
  p6 = sym p5

  proved : X1 • CCX02 • CCX01 • X1 ≈ CCX02 • CX02 • CCX01
  proved = p6

module KB0962 where

  p0 : CCX02 • CCX01 • CCX02 • X1 ≈ CX21 • CCX01 • CX21 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0213.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX01 • CCX02 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
  p1 = by-assoc-and (under (CCX02 • CCX01) (ε) KB0028.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CX21 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CX21 • X1 ≈ CX12 • CCX02 • CX12 • X1
  p3 = by-assoc-and (under (ε) (X1) KB0217.proved) Eq.refl Eq.refl

  p4 : CX21 • CCX01 • CX21 • X1 ≈ CX12 • CCX02 • CX12 • X1
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX01 • X1 • CCX02 ≈ CCX02 • CCX01 • X1 • CCX02
  p5 = refl

  p6 : CX12 • CCX02 • CX12 • X1 ≈ CCX02 • CCX01 • X1 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX02 • CCX01 • X1 • CCX02 ≈ CX12 • CCX02 • CX12 • X1
  p7 = sym p6

  proved : CCX02 • CCX01 • X1 • CCX02 ≈ CX12 • CCX02 • CX12 • X1
  proved = p7

module KB1431 where

  p0 : CX01 • CX02 • CCX02 • CCX01 • CCX02 ≈ CX01 • CX02 • CX21 • CCX01 • CX21
  p0 = by-assoc-and (under (CX01 • CX02) (ε) KB0213.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX02 • CCX01 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0149.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CCX02 • CX02 • CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
  p3 = by-assoc-and (under (ε) (CCX01 • CX21) KB0126.proved) Eq.refl Eq.refl

  p4 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
  p4 = trans p3 (refl)

  p5 : CCX02 • CX02 • CCX01 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
  p5 = refl

  p6 : CX21 • CX02 • CCX01 • CX21 ≈ CCX02 • CX02 • CCX01 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
  p7 = sym p6

  proved : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
  proved = p7

module KB1448 where

  p0 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX01 • CX02 • CX12 • CCX02 • CX12
  p0 = by-assoc-and (under (CX01 • CX02) (ε) KB0217.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
  p1 = by-assoc-and (under (ε) (CCX01 • CX21) KB0126.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX21 • CX02 • CCX01 • CX21
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX12 • CX01 • CCX02 • CX12
  p3 = by-assoc-and (under (ε) (CCX02 • CX12) KB0164.proved) Eq.refl Eq.refl

  p4 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX12 • CX01 • CCX02 • CX12
  p4 = trans p3 (refl)

  p5 : CX21 • CX02 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
  p5 = refl

  p6 : CX12 • CX01 • CCX02 • CX12 ≈ CX21 • CX02 • CCX01 • CX21
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
  p7 = sym p6

  proved : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
  proved = p7

module KB2829 where

  p0 : X1 • CCX02 • CCX01 • X1 • CCX02 ≈ X1 • CX12 • CCX02 • CX12 • X1
  p0 = by-assoc-and (under (X1) (ε) KB0962.proved) Eq.refl Eq.refl

  p1 : X1 • CCX02 • CCX01 • X1 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
  p1 = by-assoc-and (under (ε) (CCX02) KB0472.proved) Eq.refl Eq.refl

  p2 : X1 • CX12 • CCX02 • CX12 • X1 ≈ CCX02 • CX02 • CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : X1 • CX12 • CCX02 • CX12 • X1 ≈ X1 • CX12 • CCX02 • CX12 • X1
  p3 = refl

  p4 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
  p4 = by-assoc-and (under (ε) (ε) KB1431.proved) Eq.refl Eq.refl

  p5 : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
  p5 = by-assoc-and (under (ε) (ε) KB1448.proved) Eq.refl Eq.refl

  p6 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX12 • CX01 • CCX02 • CX12
  p6 = trans p4 (trans p5 (refl))

  p7 : X1 • CX12 • CCX02 • CX12 • X1 ≈ CX12 • CX01 • CCX02 • CX12
  p7 = trans (sym p3) (trans p2 p6)

  proved : X1 • CX12 • CCX02 • CX12 • X1 ≈ CX12 • CX01 • CCX02 • CX12
  proved = p7

module KB3094 where

  p0 : CCX01 • CCX02 • CCX01 • X0 • CX10 ≈ CCX01 • CCX02 • X0 • CX10 • CCX01
  p0 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0280.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • X0 • CX10 ≈ CX12 • CCX02 • CX12 • X0 • CX10
  p1 = by-assoc-and (under (ε) (X0 • CX10) KB0214.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • CX12 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CCX01 • CCX02 • X0 • CX10 • CCX01
  p3 = refl

  p4 : CX12 • CCX02 • CX12 • X0 • CX10 ≈ CX12 • CCX02 • X0 • CX12 • CX10
  p4 = by-assoc-and (under (CX12 • CCX02) (CX10) KB0045.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • X0 • CX12 • CX10 ≈ CX12 • CCX02 • X0 • CX10 • CX12
  p5 = by-assoc-and (under (CX12 • CCX02 • X0) (ε) KB0026.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX02 • CX12 • X0 • CX10 ≈ CX12 • CCX02 • X0 • CX10 • CX12
  p6 = trans p4 (trans p5 (refl))

  p7 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • X0 • CX10 • CX12
  p7 = trans (sym p3) (trans p2 p6)

  proved : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • X0 • CX10 • CX12
  proved = p7

module KB0142 where

  p0 : X0 • CX10 • X1 • X1 ≈ X1 • CX10 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0115.proved) Eq.refl Eq.refl

  p1 : X0 • CX10 • X1 • X1 ≈ X0 • CX10
  p1 = by-assoc-and (under (X0 • CX10) (ε) KB0003.proved) Eq.refl Eq.refl

  p2 : X1 • CX10 • X1 ≈ X0 • CX10
  p2 = trans (sym p0) p1

  p3 : X1 • CX10 • X1 ≈ X1 • CX10 • X1
  p3 = refl

  p4 : X0 • CX10 ≈ X0 • CX10
  p4 = refl

  p5 : X1 • CX10 • X1 ≈ X0 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CX10 • X1 ≈ X0 • CX10
  proved = p5

module KB0451 where

  p0 : CCX02 • X1 • CX10 • X1 ≈ CCX02 • X0 • CX10
  p0 = by-assoc-and (under (CCX02) (ε) KB0142.proved) Eq.refl Eq.refl

  p1 : CCX02 • X1 • CX10 • X1 ≈ X1 • CCX02 • CX10 • X1
  p1 = by-assoc-and (under (ε) (CX10 • X1) KB0028.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • CX10 ≈ X1 • CCX02 • CX10 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • CX10 ≈ CCX02 • X0 • CX10
  p3 = refl

  p4 : X1 • CCX02 • CX10 • X1 ≈ X1 • CCX02 • CX10 • X1
  p4 = refl

  p5 : CCX02 • X0 • CX10 ≈ X1 • CCX02 • CX10 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CCX02 • CX10 • X1 ≈ CCX02 • X0 • CX10
  p6 = sym p5

  proved : X1 • CCX02 • CX10 • X1 ≈ CCX02 • X0 • CX10
  proved = p6

module KB3579 where

  p0 : X1 • CCX02 • CX10 • X1 • X2 • CX12 ≈ CCX02 • X0 • CX10 • X2 • CX12
  p0 = by-assoc-and (under (ε) (X2 • CX12) KB0451.proved) Eq.refl Eq.refl

  p1 : X1 • CCX02 • CX10 • X1 • X2 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
  p1 = by-assoc-and (under (X1 • CCX02 • CX10) (ε) KB0117.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • CX10 • X2 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • CX10 • X2 • CX12 ≈ CCX02 • X0 • X2 • CX10 • CX12
  p3 = by-assoc-and (under (CCX02 • X0) (CX12) KB0021.proved) Eq.refl Eq.refl

  p4 : CCX02 • X0 • CX10 • X2 • CX12 ≈ CCX02 • X0 • X2 • CX10 • CX12
  p4 = trans p3 (refl)

  p5 : X1 • CCX02 • CX10 • CX12 • X1 ≈ X1 • CCX02 • CX10 • CX12 • X1
  p5 = refl

  p6 : CCX02 • X0 • X2 • CX10 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX02 • X0 • X2 • CX10 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
  proved = p6
