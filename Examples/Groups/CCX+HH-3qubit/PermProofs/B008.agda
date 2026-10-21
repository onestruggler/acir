{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B008 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0006 ; module KB0009 ; module KB0010 ; module KB0026 ; module KB0028 ; module KB0029 ; module KB0035 ; module KB0040 ; module KB0046 ; module KB0118 ; module KB0121 ; module KB0129 ; module KB0139 ; module KB0153 ; module KB0164 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0022 ; module KB0038 ; module KB0119 ; module KB0124 ; module KB0126 ; module KB0157 ; module KB0159 ; module KB0165 ; module KB0176 ; module KB0282 ; module KB0328)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0005 ; module KB0018 ; module KB0019 ; module KB0045 ; module KB0141 ; module KB0155 ; module KB0156 ; module KB0189)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0044 ; module KB0117 ; module KB0131 ; module KB0135 ; module KB0180 ; module KB0190 ; module KB0342)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB0333 ; module KB0335 ; module KB0623)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0076 ; module KB0085 ; module KB0093 ; module KB0104 ; module KB0223 ; module KB0309 ; module KB0316 ; module KB0814)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0198 ; module KB0318 ; module KB0323 ; module KB0324)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module drel129)

module KB0383 where

  p0 : X2 • X0 • CX12 • CCX01 ≈ X2 • CCX01 • X0
  p0 = by-assoc-and (under (X2) (ε) KB0121.proved) Eq.refl Eq.refl

  p1 : X2 • X0 • CX12 • CCX01 ≈ X0 • X2 • CX12 • CCX01
  p1 = by-assoc-and (under (ε) (CX12 • CCX01) KB0018.proved) Eq.refl Eq.refl

  p2 : X2 • CCX01 • X0 ≈ X0 • X2 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : X2 • CCX01 • X0 ≈ X2 • CCX01 • X0
  p3 = refl

  p4 : X0 • X2 • CX12 • CCX01 ≈ X0 • X2 • CX12 • CCX01
  p4 = refl

  p5 : X2 • CCX01 • X0 ≈ X0 • X2 • CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • X2 • CX12 • CCX01 ≈ X2 • CCX01 • X0
  p6 = sym p5

  proved : X0 • X2 • CX12 • CCX01 ≈ X2 • CCX01 • X0
  proved = p6

module KB1925 where

  p0 : CX20 • X0 • X2 • CX12 • CCX01 ≈ CX20 • X2 • CCX01 • X0
  p0 = by-assoc-and (under (CX20) (ε) KB0383.proved) Eq.refl Eq.refl

  p1 : CX20 • X0 • X2 • CX12 • CCX01 ≈ X0 • CX20 • X2 • CX12 • CCX01
  p1 = by-assoc-and (under (ε) (X2 • CX12 • CCX01) KB0309.proved) Eq.refl Eq.refl

  p2 : CX20 • X2 • CCX01 • X0 ≈ X0 • CX20 • X2 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX20 • X2 • CCX01 • X0 ≈ CX20 • X2 • CCX01 • X0
  p3 = refl

  p4 : X0 • CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CX12 • CCX01
  p4 = by-assoc-and (under (ε) (CX12 • CCX01) KB0318.proved) Eq.refl Eq.refl

  p5 : X0 • CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CX12 • CCX01
  p5 = trans p4 (refl)

  p6 : CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CX12 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CX12 • CCX01
  proved = p6

module KB0481 where

  p0 : X2 • X0 • CCX01 • X0 ≈ X2 • CX12 • CCX01
  p0 = by-assoc-and (under (X2) (ε) KB0153.proved) Eq.refl Eq.refl

  p1 : X2 • X0 • CCX01 • X0 ≈ X0 • X2 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0018.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 ≈ X0 • X2 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : X2 • CX12 • CCX01 ≈ X2 • CX12 • CCX01
  p3 = refl

  p4 : X0 • X2 • CCX01 • X0 ≈ X0 • X2 • CCX01 • X0
  p4 = refl

  p5 : X2 • CX12 • CCX01 ≈ X0 • X2 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • X2 • CCX01 • X0 ≈ X2 • CX12 • CCX01
  p6 = sym p5

  proved : X0 • X2 • CCX01 • X0 ≈ X2 • CX12 • CCX01
  proved = p6

module KB2217 where

  p0 : CX20 • X0 • X2 • CCX01 • X0 ≈ CX20 • X2 • CX12 • CCX01
  p0 = by-assoc-and (under (CX20) (ε) KB0481.proved) Eq.refl Eq.refl

  p1 : CX20 • X0 • X2 • CCX01 • X0 ≈ X0 • CX20 • X2 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (X2 • CCX01 • X0) KB0309.proved) Eq.refl Eq.refl

  p2 : CX20 • X2 • CX12 • CCX01 ≈ X0 • CX20 • X2 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX20 • X2 • CX12 • CCX01 ≈ CX20 • X2 • CX12 • CCX01
  p3 = refl

  p4 : X0 • CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CCX01 • X0
  p4 = by-assoc-and (under (ε) (CCX01 • X0) KB0318.proved) Eq.refl Eq.refl

  p5 : X0 • CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CCX01 • X0
  p5 = trans p4 (refl)

  p6 : CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CCX01 • X0
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CCX01 • X0
  proved = p6

module KB0174 where

  p0 : CX20 • CX10 • CX12 • CX12 ≈ CX12 • CX20 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0135.proved) Eq.refl Eq.refl

  p1 : CX20 • CX10 • CX12 • CX12 ≈ CX20 • CX10
  p1 = by-assoc-and (under (CX20 • CX10) (ε) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CX20 • CX12 ≈ CX20 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CX20 • CX12 ≈ CX12 • CX20 • CX12
  p3 = refl

  p4 : CX20 • CX10 ≈ CX20 • CX10
  p4 = refl

  p5 : CX12 • CX20 • CX12 ≈ CX20 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX20 • CX12 ≈ CX20 • CX10
  proved = p5

module KB0208 where

  p0 : CX10 • CX10 • CX12 • CX20 ≈ CX10 • CX20 • CX12
  p0 = by-assoc-and (under (CX10) (ε) KB0198.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CX12 • CX20 ≈ CX12 • CX20
  p1 = by-assoc-and (under (ε) (CX12 • CX20) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CX20 • CX12 ≈ CX12 • CX20
  p2 = trans (sym p0) p1

  p3 : CX10 • CX20 • CX12 ≈ CX10 • CX20 • CX12
  p3 = refl

  p4 : CX12 • CX20 ≈ CX12 • CX20
  p4 = refl

  p5 : CX10 • CX20 • CX12 ≈ CX12 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX20 • CX12 ≈ CX12 • CX20
  proved = p5

module KB0210 where

  p0 : CX10 • CX20 • CX12 • CX12 ≈ CX12 • CX20 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0208.proved) Eq.refl Eq.refl

  p1 : CX10 • CX20 • CX12 • CX12 ≈ CX10 • CX20
  p1 = by-assoc-and (under (CX10 • CX20) (ε) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CX20 • CX12 ≈ CX10 • CX20
  p2 = trans (sym p0) p1

  p3 : CX12 • CX20 • CX12 ≈ CX20 • CX10
  p3 = by-assoc-and (under (ε) (ε) KB0174.proved) Eq.refl Eq.refl

  p4 : CX12 • CX20 • CX12 ≈ CX20 • CX10
  p4 = trans p3 (refl)

  p5 : CX10 • CX20 ≈ CX10 • CX20
  p5 = refl

  p6 : CX20 • CX10 ≈ CX10 • CX20
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX20 • CX10 ≈ CX10 • CX20
  proved = p6

module KB0325 where

  p0 : CX20 • CCX12 • CCX01 • CX20 • CX20 ≈ CCX01 • CCX12 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0323.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX12 • CCX01 • CX20 • CX20 ≈ CX20 • CCX12 • CCX01
  p1 = by-assoc-and (under (CX20 • CCX12 • CCX01) (ε) KB0009.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CX20 ≈ CX20 • CCX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CX20 ≈ CCX01 • CX20 • CCX12
  p3 = by-assoc-and (under (CCX01) (ε) KB0040.proved) Eq.refl Eq.refl

  p4 : CCX01 • CCX12 • CX20 ≈ CCX01 • CX20 • CCX12
  p4 = trans p3 (refl)

  p5 : CX20 • CCX12 • CCX01 ≈ CX20 • CCX12 • CCX01
  p5 = refl

  p6 : CCX01 • CX20 • CCX12 ≈ CX20 • CCX12 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX01 • CX20 • CCX12 ≈ CX20 • CCX12 • CCX01
  proved = p6

module KB0336 where

  p0 : CX10 • CX10 • CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
  p0 = by-assoc-and (under (CX10) (ε) KB0335.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CCX12 • CCX02 • CX10 ≈ CCX12 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CX10) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX12 ≈ CX10 • CCX02 • CCX12
  p3 = refl

  p4 : CCX12 • CCX02 • CX10 ≈ CCX12 • CCX02 • CX10
  p4 = refl

  p5 : CX10 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
  p6 = sym p5

  proved : CCX12 • CCX02 • CX10 ≈ CX10 • CCX02 • CCX12
  proved = p6

module KB0622 where

  p0 : CX12 • CCX02 • CX12 • CCX01 • CX10 ≈ CCX01 • CCX02 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0307.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • CX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
  p1 = by-assoc-and (under (CX12 • CCX02) (ε) KB0118.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • CX10 ≈ CCX01 • CCX02 • CX10
  p3 = refl

  p4 : CX12 • CCX02 • CX10 • CCX01 ≈ CX12 • CCX02 • CX10 • CCX01
  p4 = refl

  p5 : CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CCX02 • CX10 • CCX01 ≈ CCX01 • CCX02 • CX10
  p6 = sym p5

  proved : CX12 • CCX02 • CX10 • CCX01 ≈ CCX01 • CCX02 • CX10
  proved = p6

module KB1362 where

  p0 : CX12 • CX10 • CCX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
  p0 = by-assoc-and (under (CX12) (ε) KB0335.proved) Eq.refl Eq.refl

  p1 : CX12 • CX10 • CCX12 • CCX02 • CX10 ≈ CX10 • CX12 • CCX12 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CX10) KB0026.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX12 ≈ CX10 • CX12 • CCX12 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CCX12
  p3 = refl

  p4 : CX10 • CX12 • CCX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CX10
  p4 = by-assoc-and (under (ε) (CCX02 • CX10) KB0180.proved) Eq.refl Eq.refl

  p5 : CX10 • CX12 • CCX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CX10
  p5 = trans p4 (refl)

  p6 : CX12 • CCX02 • CCX12 ≈ CCX12 • CX12 • CCX02 • CX10
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
  p7 = sym p6

  proved : CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12
  proved = p7

module KB1364 where

  p0 : CCX12 • CX12 • CCX02 • CX10 • CCX01 ≈ CX12 • CCX02 • CCX12 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB1362.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX12 • CCX02 • CX10 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
  p1 = by-assoc-and (under (CCX12) (ε) KB0622.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX12 • CCX01 ≈ CX12 • CCX02 • CCX12 • CCX01
  p3 = refl

  p4 : CCX12 • CCX01 • CCX02 • CX10 ≈ CCX12 • CCX01 • CCX02 • CX10
  p4 = refl

  p5 : CX12 • CCX02 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01
  p6 = sym p5

  proved : CCX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01
  proved = p6

module KB3219 where

  p0 : CCX01 • CX20 • CCX12 • CCX02 • CX10 ≈ CCX01 • CX20 • CX10 • CCX02 • CCX12
  p0 = by-assoc-and (under (CCX01 • CX20) (ε) KB0336.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX20 • CCX12 • CCX02 • CX10 ≈ CX20 • CCX12 • CCX01 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CCX02 • CX10) KB0325.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CX20 • CCX12 • CCX01 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CCX01 • CX10 • CX20 • CCX02 • CCX12
  p3 = by-assoc-and (under (CCX01) (CCX02 • CCX12) KB0210.proved) Eq.refl Eq.refl

  p4 : CCX01 • CX20 • CX10 • CCX02 • CCX12 ≈ CCX01 • CX10 • CX20 • CCX02 • CCX12
  p4 = trans p3 (refl)

  p5 : CX20 • CCX12 • CCX01 • CCX02 • CX10 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
  p5 = by-assoc-and (under (CX20) (ε) KB1364.proved) Eq.refl Eq.refl

  p6 : CX20 • CCX12 • CCX01 • CCX02 • CX10 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
  p6 = trans p5 (refl)

  p7 : CCX01 • CX10 • CX20 • CCX02 • CCX12 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
  p7 = trans (sym p4) (trans p2 p6)

  proved : CCX01 • CX10 • CX20 • CCX02 • CCX12 ≈ CX20 • CX12 • CCX02 • CCX12 • CCX01
  proved = p7

module KB0605 where

  p0 : CCX01 • X1 • CX01 • X0 ≈ X1 • CX01 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0282.proved) Eq.refl Eq.refl

  p1 : CCX01 • X1 • CX01 • X0 ≈ CCX01 • X0 • CX01
  p1 = by-assoc-and (under (CCX01) (ε) KB0139.proved) Eq.refl Eq.refl

  p2 : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
  p2 = trans (sym p0) p1

  p3 : X1 • CX01 • CCX01 • X0 ≈ X1 • CX01 • CCX01 • X0
  p3 = refl

  p4 : CCX01 • X0 • CX01 ≈ CCX01 • X0 • CX01
  p4 = refl

  p5 : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
  proved = p5

module KB3825 where

  p0 : X1 • CX01 • CCX01 • X0 • X2 • CX20 ≈ CCX01 • X0 • CX01 • X2 • CX20
  p0 = by-assoc-and (under (ε) (X2 • CX20) KB0605.proved) Eq.refl Eq.refl

  p1 : X1 • CX01 • CCX01 • X0 • X2 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
  p1 = by-assoc-and (under (X1 • CX01 • CCX01) (ε) KB0316.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX01 • X2 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX01 • X2 • CX20 ≈ CCX01 • X0 • X2 • CX01 • CX20
  p3 = by-assoc-and (under (CCX01 • X0) (CX20) KB0022.proved) Eq.refl Eq.refl

  p4 : CCX01 • X0 • X2 • CX01 • CX20 ≈ X2 • CCX01 • X0 • CX01 • CX20
  p4 = by-assoc-and (under (ε) (CX01 • CX20) KB0223.proved) Eq.refl Eq.refl

  p5 : CCX01 • X0 • CX01 • X2 • CX20 ≈ X2 • CCX01 • X0 • CX01 • CX20
  p5 = trans p3 (trans p4 (refl))

  p6 : X1 • CX01 • CCX01 • CX20 • X2 ≈ X1 • CX01 • CCX01 • CX20 • X2
  p6 = refl

  p7 : X2 • CCX01 • X0 • CX01 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
  p7 = trans (sym p5) (trans p2 p6)

  proved : X2 • CCX01 • X0 • CX01 • CX20 ≈ X1 • CX01 • CCX01 • CX20 • X2
  proved = p7

module KB0145 where

  p0 : X1 • X2 • CX12 • CX12 ≈ CX12 • X1 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0117.proved) Eq.refl Eq.refl

  p1 : X1 • X2 • CX12 • CX12 ≈ X1 • X2
  p1 = by-assoc-and (under (X1 • X2) (ε) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • X1 • CX12 ≈ X1 • X2
  p2 = trans (sym p0) p1

  p3 : CX12 • X1 • CX12 ≈ CX12 • X1 • CX12
  p3 = refl

  p4 : X1 • X2 ≈ X1 • X2
  p4 = refl

  p5 : CX12 • X1 • CX12 ≈ X1 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • X1 • CX12 ≈ X1 • X2
  proved = p5

module KB0188 where

  p0 : CCX02 • CCX02 • X2 • CCX02 ≈ CCX02 • X2 • CX01
  p0 = by-assoc-and (under (CCX02) (ε) KB0155.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • X2 • CCX02 ≈ X2 • CCX02
  p1 = by-assoc-and (under (ε) (X2 • CCX02) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • CX01 ≈ X2 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • CX01 ≈ CCX02 • X2 • CX01
  p3 = refl

  p4 : X2 • CCX02 ≈ X2 • CCX02
  p4 = refl

  p5 : CCX02 • X2 • CX01 ≈ X2 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X2 • CX01 ≈ X2 • CCX02
  proved = p5

module KB0231 where

  p0 : CCX02 • X1 • X0 ≈ CCX02 • X0 • X1
  p0 = by-assoc-and (under (CCX02) (ε) KB0044.proved) Eq.refl Eq.refl

  p1 : CCX02 • X1 • X0 ≈ X1 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (X0) KB0028.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • X1 ≈ CCX02 • X0 • X1
  p3 = refl

  p4 : X1 • CCX02 • X0 ≈ X1 • CCX02 • X0
  p4 = refl

  p5 : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X0 • X1 ≈ X1 • CCX02 • X0
  proved = p5

module KB0905 where

  p0 : X0 • CX21 • CCX02 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
  p0 = by-assoc-and (under (X0 • CX21) (ε) KB0188.proved) Eq.refl Eq.refl

  p1 : X0 • CX21 • CCX02 • X2 • CX01 ≈ CCX02 • X0 • X2 • CX01
  p1 = by-assoc-and (under (ε) (X2 • CX01) KB0165.proved) Eq.refl Eq.refl

  p2 : X0 • CX21 • X2 • CCX02 ≈ CCX02 • X0 • X2 • CX01
  p2 = trans (sym p0) p1

  p3 : X0 • CX21 • X2 • CCX02 ≈ X0 • CX21 • X2 • CCX02
  p3 = refl

  p4 : CCX02 • X0 • X2 • CX01 ≈ CCX02 • X0 • X2 • CX01
  p4 = refl

  p5 : X0 • CX21 • X2 • CCX02 ≈ CCX02 • X0 • X2 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
  p6 = sym p5

  proved : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
  proved = p6

module KB0913 where

  p0 : CCX02 • X2 • CX01 • X0 • X1 ≈ CCX02 • X2 • X0 • CX01
  p0 = by-assoc-and (under (CCX02 • X2) (ε) KB0190.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • X0 • X1 ≈ X2 • CCX02 • X0 • X1
  p1 = by-assoc-and (under (ε) (X0 • X1) KB0188.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • X0 • CX01 ≈ X2 • CCX02 • X0 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • X0 • CX01 ≈ CCX02 • X0 • X2 • CX01
  p3 = by-assoc-and (under (CCX02) (CX01) KB0018.proved) Eq.refl Eq.refl

  p4 : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
  p4 = by-assoc-and (under (ε) (ε) KB0905.proved) Eq.refl Eq.refl

  p5 : CCX02 • X2 • X0 • CX01 ≈ X0 • CX21 • X2 • CCX02
  p5 = trans p3 (trans p4 (refl))

  p6 : X2 • CCX02 • X0 • X1 ≈ X2 • X1 • CCX02 • X0
  p6 = by-assoc-and (under (X2) (ε) KB0231.proved) Eq.refl Eq.refl

  p7 : X2 • X1 • CCX02 • X0 ≈ X1 • X2 • CCX02 • X0
  p7 = by-assoc-and (under (ε) (CCX02 • X0) KB0019.proved) Eq.refl Eq.refl

  p8 : X2 • CCX02 • X0 • X1 ≈ X1 • X2 • CCX02 • X0
  p8 = trans p6 (trans p7 (refl))

  p9 : X0 • CX21 • X2 • CCX02 ≈ X1 • X2 • CCX02 • X0
  p9 = trans (sym p5) (trans p2 p8)

  p10 : X1 • X2 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02
  p10 = sym p9

  proved : X1 • X2 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02
  proved = p10

module KB3874 where

  p0 : CX12 • X1 • CX12 • CCX02 • X0 • CCX01 ≈ CX12 • X1 • CCX01 • CCX02 • X0
  p0 = by-assoc-and (under (CX12 • X1) (ε) KB0623.proved) Eq.refl Eq.refl

  p1 : CX12 • X1 • CX12 • CCX02 • X0 • CCX01 ≈ X1 • X2 • CCX02 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01) KB0145.proved) Eq.refl Eq.refl

  p2 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X1 • X2 • CCX02 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ CX12 • X1 • CCX01 • CCX02 • X0
  p3 = refl

  p4 : X1 • X2 • CCX02 • X0 • CCX01 ≈ X0 • CX21 • X2 • CCX02 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01) KB0913.proved) Eq.refl Eq.refl

  p5 : X1 • X2 • CCX02 • X0 • CCX01 ≈ X0 • CX21 • X2 • CCX02 • CCX01
  p5 = trans p4 (refl)

  p6 : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX12 • X1 • CCX01 • CCX02 • X0 ≈ X0 • CX21 • X2 • CCX02 • CCX01
  proved = p6

module KB0642 where

  p0 : CCX01 • X0 • X2 • CX20 ≈ CCX01 • CX20 • X2
  p0 = by-assoc-and (under (CCX01) (ε) KB0316.proved) Eq.refl Eq.refl

  p1 : CCX01 • X0 • X2 • CX20 ≈ X2 • CCX01 • X0 • CX20
  p1 = by-assoc-and (under (ε) (CX20) KB0223.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX20 • X2 ≈ X2 • CCX01 • X0 • CX20
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX20 • X2 ≈ CCX01 • CX20 • X2
  p3 = refl

  p4 : X2 • CCX01 • X0 • CX20 ≈ X2 • CCX01 • X0 • CX20
  p4 = refl

  p5 : CCX01 • CX20 • X2 ≈ X2 • CCX01 • X0 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX01 • X0 • CX20 ≈ CCX01 • CX20 • X2
  p6 = sym p5

  proved : X2 • CCX01 • X0 • CX20 ≈ CCX01 • CX20 • X2
  proved = p6

module KB1258 where

  p0 : CCX12 • CCX01 • CX20 • X0 ≈ CX20 • CCX01 • CCX12 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0324.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX01 • CX20 • X0 ≈ CCX12 • CCX01 • X0 • CX20
  p1 = by-assoc-and (under (CCX12 • CCX01) (ε) KB0309.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CCX12 • X0 ≈ CCX12 • CCX01 • X0 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CCX12 • X0 ≈ CX20 • CCX01 • X0 • CCX12
  p3 = by-assoc-and (under (CX20 • CCX01) (ε) KB0046.proved) Eq.refl Eq.refl

  p4 : CX20 • CCX01 • CCX12 • X0 ≈ CX20 • CCX01 • X0 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX01 • X0 • CX20 ≈ CCX12 • CCX01 • X0 • CX20
  p5 = refl

  p6 : CX20 • CCX01 • X0 • CCX12 ≈ CCX12 • CCX01 • X0 • CX20
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX12 • CCX01 • X0 • CX20 ≈ CX20 • CCX01 • X0 • CCX12
  p7 = sym p6

  proved : CCX12 • CCX01 • X0 • CX20 ≈ CX20 • CCX01 • X0 • CCX12
  proved = p7

module KB3939 where

  p0 : CX10 • CCX12 • X2 • CCX01 • X0 • CX20 ≈ CX10 • CCX12 • CCX01 • CX20 • X2
  p0 = by-assoc-and (under (CX10 • CCX12) (ε) KB0642.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • X2 • CCX01 • X0 • CX20 ≈ X2 • CCX12 • CCX01 • X0 • CX20
  p1 = by-assoc-and (under (ε) (CCX01 • X0 • CX20) KB0131.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ X2 • CCX12 • CCX01 • X0 • CX20
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ CX10 • CX20 • CCX01 • CCX12 • X2
  p3 = by-assoc-and (under (CX10) (X2) KB0324.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ CX10 • CX20 • CCX01 • CCX12 • X2
  p4 = trans p3 (refl)

  p5 : X2 • CCX12 • CCX01 • X0 • CX20 ≈ X2 • CX20 • CCX01 • X0 • CCX12
  p5 = by-assoc-and (under (X2) (ε) KB1258.proved) Eq.refl Eq.refl

  p6 : X2 • CCX12 • CCX01 • X0 • CX20 ≈ X2 • CX20 • CCX01 • X0 • CCX12
  p6 = trans p5 (refl)

  p7 : CX10 • CX20 • CCX01 • CCX12 • X2 ≈ X2 • CX20 • CCX01 • X0 • CCX12
  p7 = trans (sym p4) (trans p2 p6)

  proved : CX10 • CX20 • CCX01 • CCX12 • X2 ≈ X2 • CX20 • CCX01 • X0 • CCX12
  proved = p7

module KB0663 where

  p0 : CX20 • CX21 • CCX02 • CCX01 • CX21 ≈ CX20 • CCX01 • CCX02
  p0 = by-assoc-and (under (CX20) (ε) KB0328.proved) Eq.refl Eq.refl

  p1 : CX20 • CX21 • CCX02 • CCX01 • CX21 ≈ CCX02 • CX20 • CCX01 • CX21
  p1 = by-assoc-and (under (ε) (CCX01 • CX21) KB0176.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CCX02 ≈ CCX02 • CX20 • CCX01 • CX21
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CCX02 ≈ CX20 • CCX01 • CCX02
  p3 = refl

  p4 : CCX02 • CX20 • CCX01 • CX21 ≈ CCX02 • CX20 • CCX01 • CX21
  p4 = refl

  p5 : CX20 • CCX01 • CCX02 ≈ CCX02 • CX20 • CCX01 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX20 • CCX01 • CX21 ≈ CX20 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX02 • CX20 • CCX01 • CX21 ≈ CX20 • CCX01 • CCX02
  proved = p6

module KB4012 where

  p0 : CCX02 • X2 • CCX02 • CX20 • CCX01 • CX21 ≈ CCX02 • X2 • CX20 • CCX01 • CCX02
  p0 = by-assoc-and (under (CCX02 • X2) (ε) KB0663.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CCX02 • CX20 • CCX01 • CX21 ≈ X2 • CX01 • CX20 • CCX01 • CX21
  p1 = by-assoc-and (under (ε) (CX20 • CCX01 • CX21) KB0155.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ CCX02 • X2 • CX20 • CCX01 • CCX02
  p3 = refl

  p4 : X2 • CX01 • CX20 • CCX01 • CX21 ≈ X2 • CX01 • CX20 • CCX01 • CX21
  p4 = refl

  p5 : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X2 • CX20 • CCX01 • CCX02 ≈ X2 • CX01 • CX20 • CCX01 • CX21
  proved = p5

module KB0666 where

  p0 : X0 • CX12 • CCX01 • CCX02 • CX12 ≈ X0 • CCX02 • CCX01
  p0 = by-assoc-and (under (X0) (ε) KB0333.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX01 • CCX02 • CX12 ≈ CCX01 • X0 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (CCX02 • CX12) KB0121.proved) Eq.refl Eq.refl

  p2 : X0 • CCX02 • CCX01 ≈ CCX01 • X0 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : X0 • CCX02 • CCX01 ≈ X0 • CCX02 • CCX01
  p3 = refl

  p4 : CCX01 • X0 • CCX02 • CX12 ≈ CCX01 • X0 • CCX02 • CX12
  p4 = refl

  p5 : X0 • CCX02 • CCX01 ≈ CCX01 • X0 • CCX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • X0 • CCX02 • CX12 ≈ X0 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX01 • X0 • CCX02 • CX12 ≈ X0 • CCX02 • CCX01
  proved = p6

module KB0399 where

  p0 : CX12 • X0 • X1 • CX01 ≈ CX12 • CX01 • X0
  p0 = by-assoc-and (under (CX12) (ε) KB0124.proved) Eq.refl Eq.refl

  p1 : CX12 • X0 • X1 • CX01 ≈ X0 • CX12 • X1 • CX01
  p1 = by-assoc-and (under (ε) (X1 • CX01) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • X0 ≈ X0 • CX12 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • X0 ≈ CX12 • CX01 • X0
  p3 = refl

  p4 : X0 • CX12 • X1 • CX01 ≈ X0 • CX12 • X1 • CX01
  p4 = refl

  p5 : CX12 • CX01 • X0 ≈ X0 • CX12 • X1 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CX12 • X1 • CX01 ≈ CX12 • CX01 • X0
  p6 = sym p5

  proved : X0 • CX12 • X1 • CX01 ≈ CX12 • CX01 • X0
  proved = p6

module KB0504 where

  p0 : CCX02 • CX01 • CX02 • CX12 ≈ CCX02 • CX12 • CX01
  p0 = by-assoc-and (under (CCX02) (ε) KB0164.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX01 • CX02 • CX12 ≈ CX01 • CCX02 • CX02 • CX12
  p1 = by-assoc-and (under (ε) (CX02 • CX12) KB0038.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX12 • CX01 ≈ CX01 • CCX02 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX12 • CX01 ≈ CCX02 • CX12 • CX01
  p3 = refl

  p4 : CX01 • CCX02 • CX02 • CX12 ≈ CX02 • CCX02 • CX12
  p4 = by-assoc-and (under (ε) (CX12) KB0119.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX02 • CX02 • CX12 ≈ CX02 • CCX02 • CX12
  p5 = trans p4 (refl)

  p6 : CCX02 • CX12 • CX01 ≈ CX02 • CCX02 • CX12
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX02 • CX12 • CX01 ≈ CX02 • CCX02 • CX12
  proved = p6

module KB0759 where

  p0 : CX01 • CX02 • CX21 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
  p0 = by-assoc-and (under (CX01 • CX02) (ε) KB0129.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CX21 • CCX02 • X0 ≈ CX21 • CX02 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0126.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • X0 • CCX02 ≈ CX21 • CX02 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • X0 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
  p3 = refl

  p4 : CX21 • CX02 • CCX02 • X0 ≈ CX21 • CX02 • CCX02 • X0
  p4 = refl

  p5 : CX01 • CX02 • X0 • CCX02 ≈ CX21 • CX02 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • CX02 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
  p6 = sym p5

  proved : CX21 • CX02 • CCX02 • X0 ≈ CX01 • CX02 • X0 • CCX02
  proved = p6

module KB1322 where

  p0 : CCX02 • CX12 • CX01 • X1 ≈ CX02 • CCX02 • CX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0504.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CX01 • X1 ≈ CCX02 • CX12 • X1 • CX01
  p1 = by-assoc-and (under (CCX02 • CX12) (ε) KB0035.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX02 • CX12 • X1 ≈ CCX02 • CX12 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX02 • CX12 • X1 ≈ CX02 • CCX02 • CX12 • X1
  p3 = refl

  p4 : CCX02 • CX12 • X1 • CX01 ≈ CCX02 • CX12 • X1 • CX01
  p4 = refl

  p5 : CX02 • CCX02 • CX12 • X1 ≈ CCX02 • CX12 • X1 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • X1 • CX01 ≈ CX02 • CCX02 • CX12 • X1
  p6 = sym p5

  proved : CCX02 • CX12 • X1 • CX01 ≈ CX02 • CCX02 • CX12 • X1
  proved = p6

module KB3403 where

  p0 : CX21 • CCX02 • X0 • CX12 • X1 • CX01 ≈ CX21 • CCX02 • CX12 • CX01 • X0
  p0 = by-assoc-and (under (CX21 • CCX02) (ε) KB0399.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • X0 • CX12 • X1 • CX01 ≈ X0 • CCX02 • CX12 • X1 • CX01
  p1 = by-assoc-and (under (ε) (CX12 • X1 • CX01) KB0129.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ X0 • CCX02 • CX12 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ CX21 • CX02 • CCX02 • CX12 • X0
  p3 = by-assoc-and (under (CX21) (X0) KB0504.proved) Eq.refl Eq.refl

  p4 : CX21 • CX02 • CCX02 • CX12 • X0 ≈ CX21 • CX02 • CCX02 • X0 • CX12
  p4 = by-assoc-and (under (CX21 • CX02 • CCX02) (ε) KB0045.proved) Eq.refl Eq.refl

  p5 : CX21 • CX02 • CCX02 • X0 • CX12 ≈ CX01 • CX02 • X0 • CCX02 • CX12
  p5 = by-assoc-and (under (ε) (CX12) KB0759.proved) Eq.refl Eq.refl

  p6 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CCX02 • CX12
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  p7 : X0 • CCX02 • CX12 • X1 • CX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p7 = by-assoc-and (under (X0) (ε) KB1322.proved) Eq.refl Eq.refl

  p8 : X0 • CCX02 • CX12 • X1 • CX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p8 = trans p7 (refl)

  p9 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p9 = trans (sym p6) (trans p2 p8)

  proved : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
  proved = p9

module KB4039 where

  p0 : CCX01 • CX01 • CCX01 • X0 • CCX02 • CX12 ≈ CCX01 • CX01 • X0 • CCX02 • CCX01
  p0 = by-assoc-and (under (CCX01 • CX01) (ε) KB0666.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • CCX01 • X0 • CCX02 • CX12 ≈ CX01 • CX02 • X0 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (X0 • CCX02 • CX12) KB0156.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ CCX01 • CX01 • X0 • CCX02 • CCX01
  p3 = refl

  p4 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p4 = by-assoc-and (under (ε) (ε) KB3403.proved) Eq.refl Eq.refl

  p5 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p5 = trans p4 (refl)

  p6 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
  proved = p6

module KB0672 where

  p0 : CCX12 • CX01 • CCX02 • CX02 ≈ CX01 • CCX02 • CCX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0342.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX01 • CCX02 • CX02 ≈ CCX12 • CX02 • CCX02
  p1 = by-assoc-and (under (CCX12) (ε) KB0119.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX02 • CCX12 • CX02 ≈ CX01 • CCX02 • CCX12 • CX02
  p3 = refl

  p4 : CCX12 • CX02 • CCX02 ≈ CCX12 • CX02 • CCX02
  p4 = refl

  p5 : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
  proved = p5

module KB4082 where

  p0 : CX01 • X0 • CX01 • CCX02 • CCX12 • CX02 ≈ CX01 • X0 • CCX12 • CX02 • CCX02
  p0 = by-assoc-and (under (CX01 • X0) (ε) KB0672.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • CX01 • CCX02 • CCX12 • CX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CX02) KB0159.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ CX01 • X0 • CCX12 • CX02 • CCX02
  p3 = refl

  p4 : X0 • X1 • CCX02 • CCX12 • CX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
  p4 = refl

  p5 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
  proved = p5

module KB4312 where

  p0 : CX10 • CCX12 • CX12 • CX01 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CX01 • X0
  p0 = by-assoc-and (under (CX10 • CCX12) (ε) KB0814.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CX01 • X0 • CCX01 ≈ CX12 • CCX12 • CX01 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (CX01 • X0 • CCX01) KB0141.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX01 • CX01 • X0 ≈ CX12 • CCX12 • CX01 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX01 • CX01 • X0 ≈ CX10 • CCX12 • CCX01 • CX01 • X0
  p3 = refl

  p4 : CX12 • CCX12 • CX01 • X0 • CCX01 ≈ CX12 • CCX12 • CX01 • X0 • CCX01
  p4 = refl

  p5 : CX10 • CCX12 • CCX01 • CX01 • X0 ≈ CX12 • CCX12 • CX01 • X0 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CCX12 • CX01 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CX01 • X0
  p6 = sym p5

  proved : CX12 • CCX12 • CX01 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CX01 • X0
  proved = p6

module KB0130 where

  p0 : X2 • CCX02 ≈ CCX02 • CX01 • X2
  p0 = drel129.proved

  p1 : X2 • CCX02 ≈ X2 • CCX02
  p1 = refl

  p2 : CCX02 • CX01 • X2 ≈ CX01 • CCX02 • X2
  p2 = by-assoc-and (under (ε) (X2) KB0038.proved) Eq.refl Eq.refl

  p3 : CCX02 • CX01 • X2 ≈ CX01 • CCX02 • X2
  p3 = trans p2 (refl)

  p4 : X2 • CCX02 ≈ CX01 • CCX02 • X2
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX01 • CCX02 • X2 ≈ X2 • CCX02
  p5 = sym p4

  proved : CX01 • CCX02 • X2 ≈ X2 • CCX02
  proved = p5

module KB0827 where

  p0 : CX01 • CCX01 • CX01 • CCX02 • X2 ≈ CX02 • CCX01 • CCX02 • X2
  p0 = by-assoc-and (under (ε) (CCX02 • X2) KB0157.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX01 • CX01 • CCX02 • X2 ≈ CX01 • CCX01 • X2 • CCX02
  p1 = by-assoc-and (under (CX01 • CCX01) (ε) KB0130.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • CCX02 • X2 ≈ CX01 • CCX01 • X2 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX01 • CCX02 • X2
  p3 = refl

  p4 : CX01 • CCX01 • X2 • CCX02 ≈ CX01 • X2 • CCX01 • CCX02
  p4 = by-assoc-and (under (CX01) (CCX02) KB0029.proved) Eq.refl Eq.refl

  p5 : CX01 • X2 • CCX01 • CCX02 ≈ X2 • CX01 • CCX01 • CCX02
  p5 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0022.proved) Eq.refl Eq.refl

  p6 : CX01 • CCX01 • X2 • CCX02 ≈ X2 • CX01 • CCX01 • CCX02
  p6 = trans p4 (trans p5 (refl))

  p7 : CX02 • CCX01 • CCX02 • X2 ≈ X2 • CX01 • CCX01 • CCX02
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX02 • CCX01 • CCX02 • X2 ≈ X2 • CX01 • CCX01 • CCX02
  proved = p7

module KB4337 where

  p0 : CX20 • CX02 • CCX01 • CCX02 • X2 ≈ CX20 • X2 • CX01 • CCX01 • CCX02
  p0 = by-assoc-and (under (CX20) (ε) KB0827.proved) Eq.refl Eq.refl

  p1 : CX20 • CX02 • CCX01 • CCX02 • X2 ≈ CX02 • SWAP02 • CCX01 • CCX02 • X2
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02 • X2) KB0085.proved) Eq.refl Eq.refl

  p2 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • SWAP02 • CCX01 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX20 • X2 • CX01 • CCX01 • CCX02
  p3 = refl

  p4 : CX02 • SWAP02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX12 • SWAP02 • CCX02 • X2
  p4 = by-assoc-and (under (CX02) (CCX02 • X2) KB0104.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX12 • SWAP02 • CCX02 • X2 ≈ CX02 • CCX12 • CCX02 • SWAP02 • X2
  p5 = by-assoc-and (under (CX02 • CCX12) (X2) KB0076.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX12 • CCX02 • SWAP02 • X2 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
  p6 = by-assoc-and (under (CX02 • CCX12 • CCX02) (ε) KB0093.proved) Eq.refl Eq.refl

  p7 : CX02 • SWAP02 • CCX01 • CCX02 • X2 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
  p8 = trans (sym p3) (trans p2 p7)

  proved : CX20 • X2 • CX01 • CCX01 • CCX02 ≈ CX02 • CCX12 • CCX02 • X0 • SWAP02
  proved = p8

module KB0291 where

  p0 : CCX01 • CX01 • CX02 • CX21 ≈ CX01 • CCX01 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0189.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • CX02 • CX21 ≈ CCX01 • CX21 • CX02
  p1 = by-assoc-and (under (CCX01) (ε) KB0126.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CX21 ≈ CCX01 • CX21 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CX21 ≈ CX01 • CCX01 • CX21
  p3 = refl

  p4 : CCX01 • CX21 • CX02 ≈ CCX01 • CX21 • CX02
  p4 = refl

  p5 : CX01 • CCX01 • CX21 ≈ CCX01 • CX21 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX21 • CX02 ≈ CX01 • CCX01 • CX21
  p6 = sym p5

  proved : CCX01 • CX21 • CX02 ≈ CX01 • CCX01 • CX21
  proved = p6
