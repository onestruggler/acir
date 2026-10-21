{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B004 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0008 ; module KB0011 ; module KB0014 ; module KB0023 ; module KB0027 ; module KB0029 ; module KB0031 ; module KB0037 ; module KB0147 ; module KB0191 ; module KB0215 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0022 ; module KB0025 ; module KB0211 ; module KB0282 ; module KB0320 ; module KB0709)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0005 ; module KB0018 ; module KB0032 ; module KB0141 ; module KB0149 ; module KB0214 ; module KB0292)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0140 ; module KB0154 ; module KB0315)

module KB1609 where

  p0 : CCX01 • CCX02 • CX02 • X0 • X2 ≈ CX01 • CCX01 • CCX02 • X0 • X2
  p0 = by-assoc-and (under (ε) (X0 • X2) KB0292.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CX02 • X0 • X2 ≈ CCX01 • CCX02 • X0 • CX02
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0191.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CCX02 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CCX02 • X0 • X2 ≈ CX01 • CCX01 • CCX02 • X0 • X2
  p3 = refl

  p4 : CCX01 • CCX02 • X0 • CX02 ≈ CCX01 • CCX02 • X0 • CX02
  p4 = refl

  p5 : CX01 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CCX02 • X0 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CCX02 • X0 • CX02
  proved = p5

module KB0485 where

  p0 : X2 • CCX02 • X2 • X0 ≈ CX01 • CCX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0154.proved) Eq.refl Eq.refl

  p1 : X2 • CCX02 • X2 • X0 ≈ X2 • CCX02 • X0 • X2
  p1 = by-assoc-and (under (X2 • CCX02) (ε) KB0018.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX02 • X0 ≈ X2 • CCX02 • X0 • X2
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX02 • X0 ≈ CX01 • CCX02 • X0
  p3 = refl

  p4 : X2 • CCX02 • X0 • X2 ≈ X2 • CCX02 • X0 • X2
  p4 = refl

  p5 : CX01 • CCX02 • X0 ≈ X2 • CCX02 • X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX02 • X0 • X2 ≈ CX01 • CCX02 • X0
  p6 = sym p5

  proved : X2 • CCX02 • X0 • X2 ≈ CX01 • CCX02 • X0
  proved = p6

module KB2230 where

  p0 : CCX01 • X2 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
  p0 = by-assoc-and (under (CCX01) (ε) KB0485.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • CCX02 • X0 • X2 ≈ X2 • CCX01 • CCX02 • X0 • X2
  p1 = by-assoc-and (under (ε) (CCX02 • X0 • X2) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CCX02 • X0 ≈ X2 • CCX01 • CCX02 • X0 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CCX02 • X0 ≈ CCX01 • CX01 • CCX02 • X0
  p3 = refl

  p4 : X2 • CCX01 • CCX02 • X0 • X2 ≈ X2 • CCX01 • CCX02 • X0 • X2
  p4 = refl

  p5 : CCX01 • CX01 • CCX02 • X0 ≈ X2 • CCX01 • CCX02 • X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
  p6 = sym p5

  proved : X2 • CCX01 • CCX02 • X0 • X2 ≈ CCX01 • CX01 • CCX02 • X0
  proved = p6

module KB0623 where

  p0 : CX12 • CCX02 • CX12 • CCX01 • X0 ≈ CCX01 • CCX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0307.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CCX01
  p1 = by-assoc-and (under (CX12 • CCX02) (ε) KB0140.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • X0 ≈ CX12 • CCX02 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • X0 ≈ CCX01 • CCX02 • X0
  p3 = refl

  p4 : CX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0 • CCX01
  p4 = refl

  p5 : CCX01 • CCX02 • X0 ≈ CX12 • CCX02 • X0 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0
  p6 = sym p5

  proved : CX12 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0
  proved = p6

module KB0703 where

  p0 : CX12 • CCX02 • X0 • CCX01 • CCX01 ≈ CCX01 • CCX02 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0623.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • X0 • CCX01 • CCX01 ≈ CX12 • CCX02 • X0
  p1 = by-assoc-and (under (CX12 • CCX02 • X0) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0 • CCX01
  p3 = refl

  p4 : CX12 • CCX02 • X0 ≈ CX12 • CCX02 • X0
  p4 = refl

  p5 : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
  proved = p5

module KB2662 where

  p0 : CCX01 • CCX02 • X0 • CCX01 • CX02 ≈ CX12 • CCX02 • X0 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0703.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • X0 • CCX01 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
  p1 = by-assoc-and (under (CCX01 • CCX02 • X0) (ε) KB0037.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • X0 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • X0 • CX02 ≈ CX12 • CCX02 • X0 • CX02
  p3 = refl

  p4 : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
  p4 = refl

  p5 : CX12 • CCX02 • X0 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CX12 • CCX02 • X0 • CX02
  p6 = sym p5

  proved : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CX12 • CCX02 • X0 • CX02
  proved = p6

module KB2681 where

  p0 : CX02 • CCX12 • CX01 • CCX01 • X2 ≈ CCX01 • CCX12 • CX01 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0709.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX12 • CX01 • CCX01 • X2 ≈ CX02 • CCX12 • CX01 • X2 • CCX01
  p1 = by-assoc-and (under (CX02 • CCX12 • CX01) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CX01 • X2 ≈ CX02 • CCX12 • CX01 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CX01 • X2 ≈ CCX01 • CCX12 • X2 • CX01
  p3 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0022.proved) Eq.refl Eq.refl

  p4 : CCX01 • CCX12 • CX01 • X2 ≈ CCX01 • CCX12 • X2 • CX01
  p4 = trans p3 (refl)

  p5 : CX02 • CCX12 • CX01 • X2 • CCX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
  p5 = by-assoc-and (under (CX02 • CCX12) (CCX01) KB0022.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX12 • CX01 • X2 • CCX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
  p6 = trans p5 (refl)

  p7 : CCX01 • CCX12 • X2 • CX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CX02 • CCX12 • X2 • CX01 • CCX01 ≈ CCX01 • CCX12 • X2 • CX01
  p8 = sym p7

  proved : CX02 • CCX12 • X2 • CX01 • CCX01 ≈ CCX01 • CCX12 • X2 • CX01
  proved = p8

module KB2682 where

  p0 : CX10 • CX02 • CCX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
  p0 = by-assoc-and (under (CX10) (ε) KB0709.proved) Eq.refl Eq.refl

  p1 : CX10 • CX02 • CCX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
  p1 = by-assoc-and (under (ε) (CX01 • CCX01) KB0315.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CCX12 • CX01 ≈ CX10 • CCX01 • CCX12 • CX01
  p3 = refl

  p4 : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
  p4 = refl

  p5 : CX10 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
  p6 = sym p5

  proved : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
  proved = p6

module KB0321 where

  p0 : CX02 • CX02 • CCX01 • CCX12 • CX02 ≈ CX02 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB0320.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX01 • CCX12 • CX02 ≈ CCX01 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX02) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CCX01 ≈ CX02 • CCX12 • CCX01
  p3 = refl

  p4 : CCX01 • CCX12 • CX02 ≈ CCX01 • CCX12 • CX02
  p4 = refl

  p5 : CX02 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX12 • CX02 ≈ CX02 • CCX12 • CCX01
  p6 = sym p5

  proved : CCX01 • CCX12 • CX02 ≈ CX02 • CCX12 • CCX01
  proved = p6

module KB1250 where

  p0 : CCX01 • CCX12 • CX02 • CX01 ≈ CX02 • CCX12 • CCX01 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0321.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CX02 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
  p1 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0025.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CCX01 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CCX01 • CX01 ≈ CX02 • CCX12 • CCX01 • CX01
  p3 = refl

  p4 : CCX01 • CCX12 • CX01 • CX02 ≈ CCX01 • CCX12 • CX01 • CX02
  p4 = refl

  p5 : CX02 • CCX12 • CCX01 • CX01 ≈ CCX01 • CCX12 • CX01 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX12 • CX01 • CX02 ≈ CX02 • CCX12 • CCX01 • CX01
  p6 = sym p5

  proved : CCX01 • CCX12 • CX01 • CX02 ≈ CX02 • CCX12 • CCX01 • CX01
  proved = p6

module KB2897 where

  p0 : CCX01 • CCX12 • CX01 • CX02 • CCX02 ≈ CX02 • CCX12 • CCX01 • CX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB1250.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CX01 • CX02 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
  p1 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0149.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CCX01 • CX01 • CCX02
  p3 = refl

  p4 : CCX01 • CCX12 • CCX02 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02
  p4 = refl

  p5 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
  proved = p5

module KB3098 where

  p0 : CCX01 • CCX12 • CCX01 • X1 • CX01 ≈ CCX01 • CCX12 • X1 • CX01 • CCX01
  p0 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0282.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX01 • X1 • CX01 ≈ CX02 • CCX12 • CX02 • X1 • CX01
  p1 = by-assoc-and (under (ε) (X1 • CX01) KB0211.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • CX02 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CCX01 • CCX12 • X1 • CX01 • CCX01
  p3 = refl

  p4 : CX02 • CCX12 • CX02 • X1 • CX01 ≈ CX02 • CCX12 • X1 • CX02 • CX01
  p4 = by-assoc-and (under (CX02 • CCX12) (CX01) KB0023.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX12 • X1 • CX02 • CX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
  p5 = by-assoc-and (under (CX02 • CCX12 • X1) (ε) KB0025.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX12 • CX02 • X1 • CX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
  p6 = trans p4 (trans p5 (refl))

  p7 : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
  p7 = trans (sym p3) (trans p2 p6)

  proved : CCX01 • CCX12 • X1 • CX01 • CCX01 ≈ CX02 • CCX12 • X1 • CX01 • CX02
  proved = p7

module KB3873 where

  p0 : CX10 • CCX12 • CX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
  p0 = by-assoc-and (under (CX10 • CCX12) (ε) KB0623.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01) KB0141.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
  p3 = refl

  p4 : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
  p4 = refl

  p5 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
  p6 = sym p5

  proved : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
  proved = p6

module KB0333 where

  p0 : CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CX12 • CCX02 • CX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0214.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CCX02 • CCX01 ≈ CCX02 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX12 • CCX02 • CX12 ≈ CCX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX12 • CCX02 • CX12 ≈ CX12 • CCX01 • CCX02 • CX12
  p3 = by-assoc-and (under (ε) (CCX02 • CX12) KB0031.proved) Eq.refl Eq.refl

  p4 : CCX01 • CX12 • CCX02 • CX12 ≈ CX12 • CCX01 • CCX02 • CX12
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX01 ≈ CCX02 • CCX01
  p5 = refl

  p6 : CX12 • CCX01 • CCX02 • CX12 ≈ CCX02 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX12 • CCX01 • CCX02 • CX12 ≈ CCX02 • CCX01
  proved = p6

module KB0667 where

  p0 : CX10 • CX12 • CCX01 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01
  p0 = by-assoc-and (under (CX10) (ε) KB0333.proved) Eq.refl Eq.refl

  p1 : CX10 • CX12 • CCX01 • CCX02 • CX12 ≈ CCX01 • CX10 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (CCX02 • CX12) KB0147.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX01 ≈ CCX01 • CX10 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX01 ≈ CX10 • CCX02 • CCX01
  p3 = refl

  p4 : CCX01 • CX10 • CCX02 • CX12 ≈ CCX01 • CX10 • CCX02 • CX12
  p4 = refl

  p5 : CX10 • CCX02 • CCX01 ≈ CCX01 • CX10 • CCX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX10 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX01 • CX10 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01
  proved = p6

module KB0335 where

  p0 : CCX12 • CCX12 • CCX02 • CCX12 ≈ CCX12 • CX10 • CCX02 • CX10
  p0 = by-assoc-and (under (CCX12) (ε) KB0215.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX12 • CCX02 • CCX12 ≈ CCX02 • CCX12
  p1 = by-assoc-and (under (ε) (CCX02 • CCX12) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX10 • CCX02 • CX10 ≈ CCX02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX10 • CCX02 • CX10 ≈ CX10 • CCX12 • CCX02 • CX10
  p3 = by-assoc-and (under (ε) (CCX02 • CX10) KB0032.proved) Eq.refl Eq.refl

  p4 : CCX12 • CX10 • CCX02 • CX10 ≈ CX10 • CCX12 • CCX02 • CX10
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX12 ≈ CCX02 • CCX12
  p5 = refl

  p6 : CX10 • CCX12 • CCX02 • CX10 ≈ CCX02 • CCX12
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX10 • CCX12 • CCX02 • CX10 ≈ CCX02 • CCX12
  proved = p6

module KB0337 where

  p0 : CX10 • CCX12 • CCX02 • CX10 • CX10 ≈ CCX02 • CCX12 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0335.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CCX02 • CX10 • CX10 ≈ CX10 • CCX12 • CCX02
  p1 = by-assoc-and (under (CX10 • CCX12 • CCX02) (ε) KB0005.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX12 • CX10 ≈ CX10 • CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX12 • CX10 ≈ CCX02 • CX10 • CCX12
  p3 = by-assoc-and (under (CCX02) (ε) KB0032.proved) Eq.refl Eq.refl

  p4 : CCX02 • CCX12 • CX10 ≈ CCX02 • CX10 • CCX12
  p4 = trans p3 (refl)

  p5 : CX10 • CCX12 • CCX02 ≈ CX10 • CCX12 • CCX02
  p5 = refl

  p6 : CCX02 • CX10 • CCX12 ≈ CX10 • CCX12 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX02 • CX10 • CCX12 ≈ CX10 • CCX12 • CCX02
  proved = p6

module KB0670 where

  p0 : CCX02 • CX10 • CCX12 • CX12 ≈ CX10 • CCX12 • CCX02 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0337.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX10 • CCX12 • CX12 ≈ CCX02 • CX12 • CCX12
  p1 = by-assoc-and (under (CCX02) (ε) KB0141.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX12 • CCX02 • CX12
  p3 = refl

  p4 : CCX02 • CX12 • CCX12 ≈ CCX02 • CX12 • CCX12
  p4 = refl

  p5 : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CCX12 • CCX02 • CX12 ≈ CCX02 • CX12 • CCX12
  proved = p5

module KB0721 where

  p0 : CX10 • CX10 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CX12 • CCX12
  p0 = by-assoc-and (under (CX10) (ε) KB0670.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CCX12 • CCX02 • CX12 ≈ CCX12 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • CX12) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CX12 • CCX12 ≈ CCX12 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CX12 • CCX12 ≈ CX10 • CCX02 • CX12 • CCX12
  p3 = refl

  p4 : CCX12 • CCX02 • CX12 ≈ CCX12 • CCX02 • CX12
  p4 = refl

  p5 : CX10 • CCX02 • CX12 • CCX12 ≈ CCX12 • CCX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CCX02 • CX12 • CCX12 ≈ CCX12 • CCX02 • CX12
  proved = p5

module KB1350 where

  p0 : CCX01 • CX10 • CCX02 • CX12 • CCX12 ≈ CCX01 • CCX12 • CCX02 • CX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0721.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX10 • CCX02 • CX12 • CCX12 ≈ CX10 • CCX02 • CCX01 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12) KB0667.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CCX02 • CX12 ≈ CCX01 • CCX12 • CCX02 • CX12
  p3 = refl

  p4 : CX10 • CCX02 • CCX01 • CCX12 ≈ CX10 • CCX02 • CCX01 • CCX12
  p4 = refl

  p5 : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
  proved = p5

module KB5127 where

  p0 : CCX01 • CCX12 • CCX02 • CX12 • CX02 ≈ CX10 • CCX02 • CCX01 • CCX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB1350.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX02 • CX12 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX12 • CCX02) (ε) KB0027.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
  p3 = by-assoc-and (under (CX10 • CCX02) (ε) KB0321.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
  p5 = refl

  p6 : CX10 • CCX02 • CX02 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
  p7 = sym p6

  proved : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
  proved = p7
