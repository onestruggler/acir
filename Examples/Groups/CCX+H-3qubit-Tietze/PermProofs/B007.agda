{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B007 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r030 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0006 ; module KB0008 ; module KB0009 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0014 ; module KB0026 ; module KB0028 ; module KB0029 ; module KB0031 ; module KB0035 ; module KB0036 ; module KB0039 ; module KB0040 ; module KB0125 ; module KB0139 ; module KB0160 ; module KB0164 ; module KB0177 ; module KB0192)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0007 ; module KB0020 ; module KB0022 ; module KB0030 ; module KB0043 ; module KB0119 ; module KB0159 ; module KB0211 ; module KB0212 ; module KB0271 ; module KB0276 ; module KB0328)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0000 ; module KB0005 ; module KB0032 ; module KB0042 ; module KB0045 ; module KB0090 ; module KB0141 ; module KB0214 ; module KB0221)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0088 ; module KB0117 ; module KB0158 ; module KB0175 ; module KB0190 ; module KB0202)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0001 ; module KB0024 ; module KB0034 ; module KB0041 ; module KB0107 ; module KB0132 ; module KB0134 ; module KB0173 ; module KB0300 ; module KB0301 ; module KB0316)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module symmetry_CX_d)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module drel133)

module KB0834 where

  p0 : CX01 • CX21 • CX02 • X0 • CX02 ≈ CX01 • CX21 • X0 • X2
  p0 = by-assoc-and (under (CX01 • CX21) (ε) KB0160.proved) Eq.refl Eq.refl

  p1 : CX01 • CX21 • CX02 • X0 • CX02 ≈ CX02 • CX21 • X0 • CX02
  p1 = by-assoc-and (under (ε) (X0 • CX02) KB0134.proved) Eq.refl Eq.refl

  p2 : CX01 • CX21 • X0 • X2 ≈ CX02 • CX21 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CX21 • X0 • X2 ≈ CX01 • X0 • CX21 • X2
  p3 = by-assoc-and (under (CX01) (X2) KB0020.proved) Eq.refl Eq.refl

  p4 : CX01 • CX21 • X0 • X2 ≈ CX01 • X0 • CX21 • X2
  p4 = trans p3 (refl)

  p5 : CX02 • CX21 • X0 • CX02 ≈ CX02 • X0 • CX21 • CX02
  p5 = by-assoc-and (under (CX02) (CX02) KB0020.proved) Eq.refl Eq.refl

  p6 : CX02 • CX21 • X0 • CX02 ≈ CX02 • X0 • CX21 • CX02
  p6 = trans p5 (refl)

  p7 : CX01 • X0 • CX21 • X2 ≈ CX02 • X0 • CX21 • CX02
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
  p8 = sym p7

  proved : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
  proved = p8

module KB0862 where

  p0 : X0 • X2 • CX02 • CX21 • CX02 ≈ X0 • X2 • CX01 • CX21
  p0 = by-assoc-and (under (X0 • X2) (ε) KB0173.proved) Eq.refl Eq.refl

  p1 : X0 • X2 • CX02 • CX21 • CX02 ≈ CX02 • X0 • CX21 • CX02
  p1 = by-assoc-and (under (ε) (CX21 • CX02) KB0125.proved) Eq.refl Eq.refl

  p2 : X0 • X2 • CX01 • CX21 ≈ CX02 • X0 • CX21 • CX02
  p2 = trans (sym p0) p1

  p3 : X0 • X2 • CX01 • CX21 ≈ X0 • X2 • CX01 • CX21
  p3 = refl

  p4 : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
  p4 = by-assoc-and (under (ε) (ε) KB0834.proved) Eq.refl Eq.refl

  p5 : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
  p5 = trans p4 (refl)

  p6 : X0 • X2 • CX01 • CX21 ≈ CX01 • X0 • CX21 • X2
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX01 • X0 • CX21 • X2 ≈ X0 • X2 • CX01 • CX21
  p7 = sym p6

  proved : CX01 • X0 • CX21 • X2 ≈ X0 • X2 • CX01 • CX21
  proved = p7

module KB0874 where

  p0 : CX20 • CCX02 • CX20 • CCX12 • X1 ≈ CX21 • CCX02 • CCX12 • X1
  p0 = by-assoc-and (under (ε) (CCX12 • X1) KB0177.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX02 • CX20 • CCX12 • X1 ≈ CX20 • CCX02 • X1 • CCX12
  p1 = by-assoc-and (under (CX20 • CCX02) (ε) KB0132.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CCX12 • X1 ≈ CX20 • CCX02 • X1 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CCX12 • X1 ≈ CX21 • CCX02 • CCX12 • X1
  p3 = refl

  p4 : CX20 • CCX02 • X1 • CCX12 ≈ CX20 • X1 • CCX02 • CCX12
  p4 = by-assoc-and (under (CX20) (CCX12) KB0028.proved) Eq.refl Eq.refl

  p5 : CX20 • X1 • CCX02 • CCX12 ≈ X1 • CX20 • CCX02 • CCX12
  p5 = by-assoc-and (under (ε) (CCX02 • CCX12) KB0024.proved) Eq.refl Eq.refl

  p6 : CX20 • CCX02 • X1 • CCX12 ≈ X1 • CX20 • CCX02 • CCX12
  p6 = trans p4 (trans p5 (refl))

  p7 : CX21 • CCX02 • CCX12 • X1 ≈ X1 • CX20 • CCX02 • CCX12
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX21 • CCX02 • CCX12 • X1 ≈ X1 • CX20 • CCX02 • CCX12
  proved = p7

module KB0846 where

  p0 : CX01 • X0 • CX01 • CX02 • CX12 ≈ CX01 • X0 • CX12 • CX01
  p0 = by-assoc-and (under (CX01 • X0) (ε) KB0164.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • CX01 • CX02 • CX12 ≈ X0 • X1 • CX02 • CX12
  p1 = by-assoc-and (under (ε) (CX02 • CX12) KB0159.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CX12 • CX01 ≈ X0 • X1 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CX12 • CX01 ≈ CX01 • X0 • CX12 • CX01
  p3 = refl

  p4 : X0 • X1 • CX02 • CX12 ≈ X0 • X1 • CX02 • CX12
  p4 = refl

  p5 : CX01 • X0 • CX12 • CX01 ≈ X0 • X1 • CX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • CX12 • CX01 ≈ X0 • X1 • CX02 • CX12
  proved = p5

module KB0921 where

  p0 : CX01 • CX12 • CX01 • X0 • X1 ≈ CX02 • CX12 • X0 • X1
  p0 = by-assoc-and (under (ε) (X0 • X1) KB0192.proved) Eq.refl Eq.refl

  p1 : CX01 • CX12 • CX01 • X0 • X1 ≈ CX01 • CX12 • X0 • CX01
  p1 = by-assoc-and (under (CX01 • CX12) (ε) KB0190.proved) Eq.refl Eq.refl

  p2 : CX02 • CX12 • X0 • X1 ≈ CX01 • CX12 • X0 • CX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CX12 • X0 • X1 ≈ CX02 • X0 • CX12 • X1
  p3 = by-assoc-and (under (CX02) (X1) KB0045.proved) Eq.refl Eq.refl

  p4 : CX02 • CX12 • X0 • X1 ≈ CX02 • X0 • CX12 • X1
  p4 = trans p3 (refl)

  p5 : CX01 • CX12 • X0 • CX01 ≈ CX01 • X0 • CX12 • CX01
  p5 = by-assoc-and (under (CX01) (CX01) KB0045.proved) Eq.refl Eq.refl

  p6 : CX01 • X0 • CX12 • CX01 ≈ X0 • X1 • CX02 • CX12
  p6 = by-assoc-and (under (ε) (ε) KB0846.proved) Eq.refl Eq.refl

  p7 : CX01 • CX12 • X0 • CX01 ≈ X0 • X1 • CX02 • CX12
  p7 = trans p5 (trans p6 (refl))

  p8 : CX02 • X0 • CX12 • X1 ≈ X0 • X1 • CX02 • CX12
  p8 = trans (sym p4) (trans p2 p7)

  proved : CX02 • X0 • CX12 • X1 ≈ X0 • X1 • CX02 • CX12
  proved = p8

module KB0198 where

  p0 : CX20 • CX12 • CX20 • CX20 ≈ CX10 • CX12 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0175.proved) Eq.refl Eq.refl

  p1 : CX20 • CX12 • CX20 • CX20 ≈ CX20 • CX12
  p1 = by-assoc-and (under (CX20 • CX12) (ε) KB0009.proved) Eq.refl Eq.refl

  p2 : CX10 • CX12 • CX20 ≈ CX20 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CX12 • CX20 ≈ CX10 • CX12 • CX20
  p3 = refl

  p4 : CX20 • CX12 ≈ CX20 • CX12
  p4 = refl

  p5 : CX10 • CX12 • CX20 ≈ CX20 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX12 • CX20 ≈ CX20 • CX12
  proved = p5

module KB0294 where

  p0 : CCX01 • CX10 • CX12 • CX20 ≈ CX10 • CCX01 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0202.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX10 • CX12 • CX20 ≈ CCX01 • CX20 • CX12
  p1 = by-assoc-and (under (CCX01) (ε) KB0198.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CX20 ≈ CCX01 • CX20 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CX20 ≈ CX10 • CCX01 • CX20
  p3 = refl

  p4 : CCX01 • CX20 • CX12 ≈ CCX01 • CX20 • CX12
  p4 = refl

  p5 : CX10 • CCX01 • CX20 ≈ CCX01 • CX20 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX20 • CX12 ≈ CX10 • CCX01 • CX20
  p6 = sym p5

  proved : CCX01 • CX20 • CX12 ≈ CX10 • CCX01 • CX20
  proved = p6

module KB1186 where

  p0 : CCX01 • CX20 • CX12 • X2 ≈ CX10 • CCX01 • CX20 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0294.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX20 • CX12 • X2 ≈ CCX01 • CX20 • X2 • CX12
  p1 = by-assoc-and (under (CCX01 • CX20) (ε) KB0036.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CX20 • X2 ≈ CCX01 • CX20 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CX20 • X2 ≈ CX10 • CCX01 • CX20 • X2
  p3 = refl

  p4 : CCX01 • CX20 • X2 • CX12 ≈ CCX01 • CX20 • X2 • CX12
  p4 = refl

  p5 : CX10 • CCX01 • CX20 • X2 ≈ CCX01 • CX20 • X2 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX20 • X2 • CX12 ≈ CX10 • CCX01 • CX20 • X2
  p6 = sym p5

  proved : CCX01 • CX20 • X2 • CX12 ≈ CX10 • CCX01 • CX20 • X2
  proved = p6

module KB1231 where

  p0 : X0 • CX01 • X0 • X2 • CX20 ≈ X0 • CX01 • CX20 • X2
  p0 = by-assoc-and (under (X0 • CX01) (ε) KB0316.proved) Eq.refl Eq.refl

  p1 : X0 • CX01 • X0 • X2 • CX20 ≈ X1 • CX01 • X2 • CX20
  p1 = by-assoc-and (under (ε) (X2 • CX20) KB0158.proved) Eq.refl Eq.refl

  p2 : X0 • CX01 • CX20 • X2 ≈ X1 • CX01 • X2 • CX20
  p2 = trans (sym p0) p1

  p3 : X0 • CX01 • CX20 • X2 ≈ X0 • CX01 • CX20 • X2
  p3 = refl

  p4 : X1 • CX01 • X2 • CX20 ≈ X1 • X2 • CX01 • CX20
  p4 = by-assoc-and (under (X1) (CX20) KB0022.proved) Eq.refl Eq.refl

  p5 : X1 • CX01 • X2 • CX20 ≈ X1 • X2 • CX01 • CX20
  p5 = trans p4 (refl)

  p6 : X0 • CX01 • CX20 • X2 ≈ X1 • X2 • CX01 • CX20
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X1 • X2 • CX01 • CX20 ≈ X0 • CX01 • CX20 • X2
  p7 = sym p6

  proved : X1 • X2 • CX01 • CX20 ≈ X0 • CX01 • CX20 • X2
  proved = p7

module KB0302 where

  p0 : CX20 • CX01 • CX20 • CX01 • CX01 ≈ CX21 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0300.proved) Eq.refl Eq.refl

  p1 : CX20 • CX01 • CX20 • CX01 • CX01 ≈ CX20 • CX01 • CX20
  p1 = by-assoc-and (under (CX20 • CX01 • CX20) (ε) KB0013.proved) Eq.refl Eq.refl

  p2 : CX21 • CX01 ≈ CX20 • CX01 • CX20
  p2 = trans (sym p0) p1

  p3 : CX21 • CX01 ≈ CX01 • CX21
  p3 = by-assoc-and (under (ε) (ε) KB0030.proved) Eq.refl Eq.refl

  p4 : CX21 • CX01 ≈ CX01 • CX21
  p4 = trans p3 (refl)

  p5 : CX20 • CX01 • CX20 ≈ CX20 • CX01 • CX20
  p5 = refl

  p6 : CX01 • CX21 ≈ CX20 • CX01 • CX20
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX20 • CX01 • CX20 ≈ CX01 • CX21
  p7 = sym p6

  proved : CX20 • CX01 • CX20 ≈ CX01 • CX21
  proved = p7

module KB0317 where

  p0 : X0 • X2 • CX20 • CX20 ≈ CX20 • X2 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0316.proved) Eq.refl Eq.refl

  p1 : X0 • X2 • CX20 • CX20 ≈ X0 • X2
  p1 = by-assoc-and (under (X0 • X2) (ε) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • X2 • CX20 ≈ X0 • X2
  p2 = trans (sym p0) p1

  p3 : CX20 • X2 • CX20 ≈ CX20 • X2 • CX20
  p3 = refl

  p4 : X0 • X2 ≈ X0 • X2
  p4 = refl

  p5 : CX20 • X2 • CX20 ≈ X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • X2 • CX20 ≈ X0 • X2
  proved = p5

module KB1241 where

  p0 : CX20 • CX01 • CX20 • X2 • CX20 ≈ CX20 • CX01 • X0 • X2
  p0 = by-assoc-and (under (CX20 • CX01) (ε) KB0317.proved) Eq.refl Eq.refl

  p1 : CX20 • CX01 • CX20 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
  p1 = by-assoc-and (under (ε) (X2 • CX20) KB0302.proved) Eq.refl Eq.refl

  p2 : CX20 • CX01 • X0 • X2 ≈ CX01 • CX21 • X2 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • CX01 • X0 • X2 ≈ CX20 • X2 • CX01 • X0
  p3 = by-assoc-and (under (CX20) (ε) KB0221.proved) Eq.refl Eq.refl

  p4 : CX20 • CX01 • X0 • X2 ≈ CX20 • X2 • CX01 • X0
  p4 = trans p3 (refl)

  p5 : CX01 • CX21 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
  p5 = refl

  p6 : CX20 • X2 • CX01 • X0 ≈ CX01 • CX21 • X2 • CX20
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX20 • X2 • CX01 • X0 ≈ CX01 • CX21 • X2 • CX20
  proved = p6

module KB0323 where

  p0 : CCX12 • CCX12 • CCX01 • CCX12 ≈ CCX12 • CX20 • CCX01 • CX20
  p0 = by-assoc-and (under (CCX12) (ε) KB0212.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX12 • CCX01 • CCX12 ≈ CCX01 • CCX12
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX20 • CCX01 • CX20 ≈ CCX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX20 • CCX01 • CX20 ≈ CX20 • CCX12 • CCX01 • CX20
  p3 = by-assoc-and (under (ε) (CCX01 • CX20) KB0040.proved) Eq.refl Eq.refl

  p4 : CCX12 • CX20 • CCX01 • CX20 ≈ CX20 • CCX12 • CCX01 • CX20
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX12 ≈ CCX01 • CCX12
  p5 = refl

  p6 : CX20 • CCX12 • CCX01 • CX20 ≈ CCX01 • CCX12
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX20 • CCX12 • CCX01 • CX20 ≈ CCX01 • CCX12
  proved = p6

module KB0324 where

  p0 : CX20 • CX20 • CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
  p0 = by-assoc-and (under (CX20) (ε) KB0323.proved) Eq.refl Eq.refl

  p1 : CX20 • CX20 • CCX12 • CCX01 • CX20 ≈ CCX12 • CCX01 • CX20
  p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX20) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CCX12 ≈ CX20 • CCX01 • CCX12
  p3 = refl

  p4 : CCX12 • CCX01 • CX20 ≈ CCX12 • CCX01 • CX20
  p4 = refl

  p5 : CX20 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
  p6 = sym p5

  proved : CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
  proved = p6

module KB1256 where

  p0 : CCX01 • CCX12 • CCX01 • CX20 ≈ CCX01 • CX20 • CCX01 • CCX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0324.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02 • CX20
  p1 = by-assoc-and (under (ε) (CX20) KB0211.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX20 • CCX01 • CCX12 ≈ CX02 • CCX12 • CX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX20 • CCX01 • CCX12 ≈ CCX01 • CX20 • CCX01 • CCX12
  p3 = refl

  p4 : CX02 • CCX12 • CX02 • CX20 ≈ CX02 • CX20 • CCX12 • SWAP02
  p4 = by-assoc-and (under (CX02) (ε) KB0271.proved) Eq.refl Eq.refl

  p5 : CX02 • CX20 • CCX12 • SWAP02 ≈ CX02 • CX02 • CX20 • CCX01
  p5 = by-assoc-and (under (CX02) (ε) KB0276.proved) Eq.refl Eq.refl

  p6 : CX02 • CX02 • CX20 • CCX01 ≈ CX20 • CCX01
  p6 = by-assoc-and (under (ε) (CX20 • CCX01) KB0008.proved) Eq.refl Eq.refl

  p7 : CX02 • CCX12 • CX02 • CX20 ≈ CX20 • CCX01
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CCX01 • CX20 • CCX01 • CCX12 ≈ CX20 • CCX01
  p8 = trans (sym p3) (trans p2 p7)

  proved : CCX01 • CX20 • CCX01 • CCX12 ≈ CX20 • CCX01
  proved = p8

module KB1257 where

  p0 : CCX01 • CCX01 • CX20 • CCX01 • CCX12 ≈ CCX01 • CX20 • CCX01
  p0 = by-assoc-and (under (CCX01) (ε) KB1256.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CX20 • CCX01 • CCX12 ≈ CX20 • CCX01 • CCX12
  p1 = by-assoc-and (under (ε) (CX20 • CCX01 • CCX12) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX20 • CCX01 ≈ CX20 • CCX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX20 • CCX01 ≈ CCX01 • CX20 • CCX01
  p3 = refl

  p4 : CX20 • CCX01 • CCX12 ≈ CX20 • CCX01 • CCX12
  p4 = refl

  p5 : CCX01 • CX20 • CCX01 ≈ CX20 • CCX01 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX20 • CCX01 ≈ CX20 • CCX01 • CCX12
  proved = p5

module KB1352 where

  p0 : CCX01 • CX20 • CCX01 • X2 ≈ CX20 • CCX01 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB1257.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX20 • CCX01 • X2 ≈ CCX01 • CX20 • X2 • CCX01
  p1 = by-assoc-and (under (CCX01 • CX20) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • CCX12 • X2 ≈ CCX01 • CX20 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • CCX12 • X2 ≈ CX20 • CCX01 • CCX12 • X2
  p3 = refl

  p4 : CCX01 • CX20 • X2 • CCX01 ≈ CCX01 • CX20 • X2 • CCX01
  p4 = refl

  p5 : CX20 • CCX01 • CCX12 • X2 ≈ CCX01 • CX20 • X2 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX20 • X2 • CCX01 ≈ CX20 • CCX01 • CCX12 • X2
  p6 = sym p5

  proved : CCX01 • CX20 • X2 • CCX01 ≈ CX20 • CCX01 • CCX12 • X2
  proved = p6

module KB0226 where

  p0 : CCX02 • CX21 • SWAP12 ≈ CCX02 • CX12 • CX21
  p0 = by-assoc-and (under (CCX02) (ε) KB0041.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX21 • SWAP12 ≈ CX21 • CCX02 • SWAP12
  p1 = by-assoc-and (under (ε) (SWAP12) KB0039.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX12 • CX21 ≈ CCX02 • CX12 • CX21
  p3 = refl

  p4 : CX21 • CCX02 • SWAP12 ≈ CX21 • CCX02 • SWAP12
  p4 = refl

  p5 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
  proved = p5

module KB0060 where

  p0 : CX12 ≈ SWAP12 • CX21 • SWAP12
  p0 = symmetry_CX_d.proved

  p1 : CX12 ≈ CX12
  p1 = refl

  p2 : SWAP12 • CX21 • SWAP12 ≈ SWAP12 • CX12 • CX21
  p2 = by-assoc-and (under (SWAP12) (ε) KB0041.proved) Eq.refl Eq.refl

  p3 : SWAP12 • CX21 • SWAP12 ≈ SWAP12 • CX12 • CX21
  p3 = trans p2 (refl)

  p4 : CX12 ≈ SWAP12 • CX12 • CX21
  p4 = trans (sym p1) (trans p0 p3)

  p5 : SWAP12 • CX12 • CX21 ≈ CX12
  p5 = sym p4

  proved : SWAP12 • CX12 • CX21 ≈ CX12
  proved = p5

module KB0061 where

  p0 : SWAP12 • SWAP12 • CX12 • CX21 ≈ SWAP12 • CX12
  p0 = by-assoc-and (under (SWAP12) (ε) KB0060.proved) Eq.refl Eq.refl

  p1 : SWAP12 • SWAP12 • CX12 • CX21 ≈ CX12 • CX21
  p1 = by-assoc-and (under (ε) (CX12 • CX21) KB0001.proved) Eq.refl Eq.refl

  p2 : SWAP12 • CX12 ≈ CX12 • CX21
  p2 = trans (sym p0) p1

  p3 : SWAP12 • CX12 ≈ SWAP12 • CX12
  p3 = refl

  p4 : CX12 • CX21 ≈ CX12 • CX21
  p4 = refl

  p5 : SWAP12 • CX12 ≈ CX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP12 • CX12 ≈ CX12 • CX21
  proved = p5

module KB0278 where

  p0 : SWAP12 • CCX01 • CX12 ≈ CCX02 • SWAP12 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0107.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CCX01 • CX12 ≈ SWAP12 • CX12 • CCX01
  p1 = by-assoc-and (under (SWAP12) (ε) KB0031.proved) Eq.refl Eq.refl

  p2 : CCX02 • SWAP12 • CX12 ≈ SWAP12 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • SWAP12 • CX12 ≈ CCX02 • CX12 • CX21
  p3 = by-assoc-and (under (CCX02) (ε) KB0061.proved) Eq.refl Eq.refl

  p4 : CCX02 • CX12 • CX21 ≈ CX21 • CCX02 • SWAP12
  p4 = by-assoc-and (under (ε) (ε) KB0226.proved) Eq.refl Eq.refl

  p5 : CCX02 • SWAP12 • CX12 ≈ CX21 • CCX02 • SWAP12
  p5 = trans p3 (trans p4 (refl))

  p6 : SWAP12 • CX12 • CCX01 ≈ CX12 • CX21 • CCX01
  p6 = by-assoc-and (under (ε) (CCX01) KB0061.proved) Eq.refl Eq.refl

  p7 : SWAP12 • CX12 • CCX01 ≈ CX12 • CX21 • CCX01
  p7 = trans p6 (refl)

  p8 : CX21 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01
  p8 = trans (sym p5) (trans p2 p7)

  proved : CX21 • CCX02 • SWAP12 ≈ CX12 • CX21 • CCX01
  proved = p8

module KB0329 where

  p0 : CX21 • CX21 • CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0328.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX02 • CCX01 • CX21 ≈ CCX02 • CCX01 • CX21
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CX21) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CX21
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 ≈ CX21 • CCX01 • CCX02
  p3 = refl

  p4 : CCX02 • CCX01 • CX21 ≈ CCX02 • CCX01 • CX21
  p4 = refl

  p5 : CX21 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
  proved = p6

module KB1265 where

  p0 : CCX01 • CCX02 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX01 • CCX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0329.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12 • CX21
  p1 = by-assoc-and (under (ε) (CX21) KB0214.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX21 • CCX01 • CCX02 ≈ CX12 • CCX02 • CX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01 • CCX02
  p3 = refl

  p4 : CX12 • CCX02 • CX12 • CX21 ≈ CX12 • CX21 • CCX02 • SWAP12
  p4 = by-assoc-and (under (CX12) (ε) KB0226.proved) Eq.refl Eq.refl

  p5 : CX12 • CX21 • CCX02 • SWAP12 ≈ CX12 • CX12 • CX21 • CCX01
  p5 = by-assoc-and (under (CX12) (ε) KB0278.proved) Eq.refl Eq.refl

  p6 : CX12 • CX12 • CX21 • CCX01 ≈ CX21 • CCX01
  p6 = by-assoc-and (under (ε) (CX21 • CCX01) KB0006.proved) Eq.refl Eq.refl

  p7 : CX12 • CCX02 • CX12 • CX21 ≈ CX21 • CCX01
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CCX01 • CX21 • CCX01 • CCX02 ≈ CX21 • CCX01
  p8 = trans (sym p3) (trans p2 p7)

  proved : CCX01 • CX21 • CCX01 • CCX02 ≈ CX21 • CCX01
  proved = p8

module KB1266 where

  p0 : CCX01 • CX21 • CCX01 • CCX02 • CCX02 ≈ CX21 • CCX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB1265.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CCX01 • CCX02 • CCX02 ≈ CCX01 • CX21 • CCX01
  p1 = by-assoc-and (under (CCX01 • CX21 • CCX01) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 ≈ CX21 • CCX01 • CCX02
  p3 = refl

  p4 : CCX01 • CX21 • CCX01 ≈ CCX01 • CX21 • CCX01
  p4 = refl

  p5 : CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX01 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX02
  proved = p6

module KB1353 where

  p0 : CCX01 • CX21 • CCX01 • X2 ≈ CX21 • CCX01 • CCX02 • X2
  p0 = by-assoc-and (under (ε) (X2) KB1266.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CCX01 • X2 ≈ CCX01 • CX21 • X2 • CCX01
  p1 = by-assoc-and (under (CCX01 • CX21) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 • X2 ≈ CCX01 • CX21 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 • X2 ≈ CX21 • CCX01 • CCX02 • X2
  p3 = refl

  p4 : CCX01 • CX21 • X2 • CCX01 ≈ CCX01 • CX21 • X2 • CCX01
  p4 = refl

  p5 : CX21 • CCX01 • CCX02 • X2 ≈ CCX01 • CX21 • X2 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX21 • X2 • CCX01 ≈ CX21 • CCX01 • CCX02 • X2
  p6 = sym p5

  proved : CCX01 • CX21 • X2 • CCX01 ≈ CX21 • CCX01 • CCX02 • X2
  proved = p6

module KB0225 where

  p0 : CX21 • CX01 • X2 ≈ CX01 • CX21 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0030.proved) Eq.refl Eq.refl

  p1 : CX21 • CX01 • X2 ≈ CX21 • X2 • CX01
  p1 = by-assoc-and (under (CX21) (ε) KB0022.proved) Eq.refl Eq.refl

  p2 : CX01 • CX21 • X2 ≈ CX21 • X2 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX21 • X2 ≈ CX01 • CX21 • X2
  p3 = refl

  p4 : CX21 • X2 • CX01 ≈ CX21 • X2 • CX01
  p4 = refl

  p5 : CX01 • CX21 • X2 ≈ CX21 • X2 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • X2 • CX01 ≈ CX01 • CX21 • X2
  p6 = sym p5

  proved : CX21 • X2 • CX01 ≈ CX01 • CX21 • X2
  proved = p6

module KB0133 where

  p0 : X2 • CX21 ≈ CX21 • X1 • X2
  p0 = drel133.proved

  p1 : X2 • CX21 ≈ X2 • CX21
  p1 = refl

  p2 : CX21 • X1 • X2 ≈ X1 • CX21 • X2
  p2 = by-assoc-and (under (ε) (X2) KB0034.proved) Eq.refl Eq.refl

  p3 : CX21 • X1 • X2 ≈ X1 • CX21 • X2
  p3 = trans p2 (refl)

  p4 : X2 • CX21 ≈ X1 • CX21 • X2
  p4 = trans (sym p1) (trans p0 p3)

  p5 : X1 • CX21 • X2 ≈ X2 • CX21
  p5 = sym p4

  proved : X1 • CX21 • X2 ≈ X2 • CX21
  proved = p5

module KB0171 where

  p0 : X1 • X1 • CX21 • X2 ≈ X1 • X2 • CX21
  p0 = by-assoc-and (under (X1) (ε) KB0133.proved) Eq.refl Eq.refl

  p1 : X1 • X1 • CX21 • X2 ≈ CX21 • X2
  p1 = by-assoc-and (under (ε) (CX21 • X2) KB0003.proved) Eq.refl Eq.refl

  p2 : X1 • X2 • CX21 ≈ CX21 • X2
  p2 = trans (sym p0) p1

  p3 : X1 • X2 • CX21 ≈ X1 • X2 • CX21
  p3 = refl

  p4 : CX21 • X2 ≈ CX21 • X2
  p4 = refl

  p5 : X1 • X2 • CX21 ≈ CX21 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • X2 • CX21 ≈ CX21 • X2
  proved = p5

module KB0196 where

  p0 : X1 • X2 • CX21 • CX21 ≈ CX21 • X2 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0171.proved) Eq.refl Eq.refl

  p1 : X1 • X2 • CX21 • CX21 ≈ X1 • X2
  p1 = by-assoc-and (under (X1 • X2) (ε) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • X2 • CX21 ≈ X1 • X2
  p2 = trans (sym p0) p1

  p3 : CX21 • X2 • CX21 ≈ CX21 • X2 • CX21
  p3 = refl

  p4 : X1 • X2 ≈ X1 • X2
  p4 = refl

  p5 : CX21 • X2 • CX21 ≈ X1 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • X2 • CX21 ≈ X1 • X2
  proved = p5

module KB0569 where

  p0 : CX21 • X2 • CX21 • CX20 ≈ X1 • X2 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0196.proved) Eq.refl Eq.refl

  p1 : CX21 • X2 • CX21 • CX20 ≈ CX21 • X2 • CX20 • CX21
  p1 = by-assoc-and (under (CX21 • X2) (ε) KB0043.proved) Eq.refl Eq.refl

  p2 : X1 • X2 • CX20 ≈ CX21 • X2 • CX20 • CX21
  p2 = trans (sym p0) p1

  p3 : X1 • X2 • CX20 ≈ X1 • X2 • CX20
  p3 = refl

  p4 : CX21 • X2 • CX20 • CX21 ≈ CX21 • X2 • CX20 • CX21
  p4 = refl

  p5 : X1 • X2 • CX20 ≈ CX21 • X2 • CX20 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
  p6 = sym p5

  proved : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
  proved = p6

module KB1628 where

  p0 : CX21 • X2 • CX01 • CX20 • CX01 ≈ CX21 • X2 • CX20 • CX21
  p0 = by-assoc-and (under (CX21 • X2) (ε) KB0301.proved) Eq.refl Eq.refl

  p1 : CX21 • X2 • CX01 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20 • CX01
  p1 = by-assoc-and (under (ε) (CX20 • CX01) KB0225.proved) Eq.refl Eq.refl

  p2 : CX21 • X2 • CX20 • CX21 ≈ CX01 • CX21 • X2 • CX20 • CX01
  p2 = trans (sym p0) p1

  p3 : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
  p3 = by-assoc-and (under (ε) (ε) KB0569.proved) Eq.refl Eq.refl

  p4 : CX21 • X2 • CX20 • CX21 ≈ X1 • X2 • CX20
  p4 = trans p3 (refl)

  p5 : CX01 • CX21 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20 • CX01
  p5 = refl

  p6 : X1 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20 • CX01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX01 • CX21 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20
  p7 = sym p6

  proved : CX01 • CX21 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20
  proved = p7

module KB1630 where

  p0 : CX01 • CX21 • X2 • CX20 • CX01 • CX01 ≈ X1 • X2 • CX20 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB1628.proved) Eq.refl Eq.refl

  p1 : CX01 • CX21 • X2 • CX20 • CX01 • CX01 ≈ CX01 • CX21 • X2 • CX20
  p1 = by-assoc-and (under (CX01 • CX21 • X2 • CX20) (ε) KB0013.proved) Eq.refl Eq.refl

  p2 : X1 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20
  p2 = trans (sym p0) p1

  p3 : X1 • X2 • CX20 • CX01 ≈ X1 • X2 • CX20 • CX01
  p3 = refl

  p4 : CX01 • CX21 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
  p4 = refl

  p5 : X1 • X2 • CX20 • CX01 ≈ CX01 • CX21 • X2 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • CX21 • X2 • CX20 ≈ X1 • X2 • CX20 • CX01
  p6 = sym p5

  proved : CX01 • CX21 • X2 • CX20 ≈ X1 • X2 • CX20 • CX01
  proved = p6

module KB0362 where

  p0 : CX20 • X1 • X2 • CX12 ≈ CX20 • CX12 • X1
  p0 = by-assoc-and (under (CX20) (ε) KB0117.proved) Eq.refl Eq.refl

  p1 : CX20 • X1 • X2 • CX12 ≈ X1 • CX20 • X2 • CX12
  p1 = by-assoc-and (under (ε) (X2 • CX12) KB0024.proved) Eq.refl Eq.refl

  p2 : CX20 • CX12 • X1 ≈ X1 • CX20 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CX12 • X1 ≈ CX20 • CX12 • X1
  p3 = refl

  p4 : X1 • CX20 • X2 • CX12 ≈ X1 • CX20 • X2 • CX12
  p4 = refl

  p5 : CX20 • CX12 • X1 ≈ X1 • CX20 • X2 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CX20 • X2 • CX12 ≈ CX20 • CX12 • X1
  p6 = sym p5

  proved : X1 • CX20 • X2 • CX12 ≈ CX20 • CX12 • X1
  proved = p6

module KB1228 where

  p0 : X1 • CX01 • X0 • X2 • CX20 ≈ X1 • CX01 • CX20 • X2
  p0 = by-assoc-and (under (X1 • CX01) (ε) KB0316.proved) Eq.refl Eq.refl

  p1 : X1 • CX01 • X0 • X2 • CX20 ≈ X0 • CX01 • X2 • CX20
  p1 = by-assoc-and (under (ε) (X2 • CX20) KB0139.proved) Eq.refl Eq.refl

  p2 : X1 • CX01 • CX20 • X2 ≈ X0 • CX01 • X2 • CX20
  p2 = trans (sym p0) p1

  p3 : X1 • CX01 • CX20 • X2 ≈ X1 • CX01 • CX20 • X2
  p3 = refl

  p4 : X0 • CX01 • X2 • CX20 ≈ X0 • X2 • CX01 • CX20
  p4 = by-assoc-and (under (X0) (CX20) KB0022.proved) Eq.refl Eq.refl

  p5 : X0 • CX01 • X2 • CX20 ≈ X0 • X2 • CX01 • CX20
  p5 = trans p4 (refl)

  p6 : X1 • CX01 • CX20 • X2 ≈ X0 • X2 • CX01 • CX20
  p6 = trans (sym p3) (trans p2 p5)

  proved : X1 • CX01 • CX20 • X2 ≈ X0 • X2 • CX01 • CX20
  proved = p6

module KB1823 where

  p0 : CX01 • X1 • CX20 • X2 • CX12 ≈ CX01 • CX20 • CX12 • X1
  p0 = by-assoc-and (under (CX01) (ε) KB0362.proved) Eq.refl Eq.refl

  p1 : CX01 • X1 • CX20 • X2 • CX12 ≈ X1 • CX01 • CX20 • X2 • CX12
  p1 = by-assoc-and (under (ε) (CX20 • X2 • CX12) KB0035.proved) Eq.refl Eq.refl

  p2 : CX01 • CX20 • CX12 • X1 ≈ X1 • CX01 • CX20 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CX20 • CX12 • X1 ≈ CX01 • CX20 • CX12 • X1
  p3 = refl

  p4 : X1 • CX01 • CX20 • X2 • CX12 ≈ X0 • X2 • CX01 • CX20 • CX12
  p4 = by-assoc-and (under (ε) (CX12) KB1228.proved) Eq.refl Eq.refl

  p5 : X1 • CX01 • CX20 • X2 • CX12 ≈ X0 • X2 • CX01 • CX20 • CX12
  p5 = trans p4 (refl)

  p6 : CX01 • CX20 • CX12 • X1 ≈ X0 • X2 • CX01 • CX20 • CX12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X0 • X2 • CX01 • CX20 • CX12 ≈ CX01 • CX20 • CX12 • X1
  p7 = sym p6

  proved : X0 • X2 • CX01 • CX20 • CX12 ≈ CX01 • CX20 • CX12 • X1
  proved = p7

module KB0111 where

  p0 : CX10 • CX10 • SWAP01 ≈ CX10 • CX01 • CX10
  p0 = by-assoc-and (under (CX10) (ε) KB0042.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • SWAP01 ≈ SWAP01
  p1 = by-assoc-and (under (ε) (SWAP01) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CX01 • CX10 ≈ SWAP01
  p2 = trans (sym p0) p1

  p3 : CX10 • CX01 • CX10 ≈ CX01 • SWAP01 • CX10
  p3 = by-assoc-and (under (ε) (CX10) KB0088.proved) Eq.refl Eq.refl

  p4 : CX10 • CX01 • CX10 ≈ CX01 • SWAP01 • CX10
  p4 = trans p3 (refl)

  p5 : SWAP01 ≈ SWAP01
  p5 = refl

  p6 : CX01 • SWAP01 • CX10 ≈ SWAP01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX01 • SWAP01 • CX10 ≈ SWAP01
  proved = p6

module KB0112 where

  p0 : CX01 • SWAP01 • CX10 • CX10 ≈ SWAP01 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0111.proved) Eq.refl Eq.refl

  p1 : CX01 • SWAP01 • CX10 • CX10 ≈ CX01 • SWAP01
  p1 = by-assoc-and (under (CX01 • SWAP01) (ε) KB0005.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CX10 ≈ CX01 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CX10 ≈ SWAP01 • CX10
  p3 = refl

  p4 : CX01 • SWAP01 ≈ CX01 • SWAP01
  p4 = refl

  p5 : SWAP01 • CX10 ≈ CX01 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CX10 ≈ CX01 • SWAP01
  proved = p5

module KB0261 where

  p0 : CX12 • CX10 • CX01 ≈ CX12 • CX01 • SWAP01
  p0 = by-assoc-and (under (CX12) (ε) KB0088.proved) Eq.refl Eq.refl

  p1 : CX12 • CX10 • CX01 ≈ CX10 • CX12 • CX01
  p1 = by-assoc-and (under (ε) (CX01) KB0026.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • SWAP01 ≈ CX12 • CX01 • SWAP01
  p3 = refl

  p4 : CX10 • CX12 • CX01 ≈ CX10 • CX12 • CX01
  p4 = refl

  p5 : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX01 • SWAP01 ≈ CX10 • CX12 • CX01
  proved = p5

module KB0100 where

  p0 : CX12 ≈ SWAP01 • CX02 • SWAP01
  p0 = by-assoc-and (axiom r030) Eq.refl Eq.refl

  p1 : CX12 ≈ CX12
  p1 = refl

  p2 : SWAP01 • CX02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01
  p2 = refl

  p3 : CX12 ≈ SWAP01 • CX02 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • CX02 • SWAP01 ≈ CX12
  p4 = sym p3

  proved : SWAP01 • CX02 • SWAP01 ≈ CX12
  proved = p4

module KB0102 where

  p0 : SWAP01 • CX02 • SWAP01 • SWAP01 ≈ CX12 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0100.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CX02 • SWAP01 • SWAP01 ≈ SWAP01 • CX02
  p1 = by-assoc-and (under (SWAP01 • CX02) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : CX12 • SWAP01 ≈ SWAP01 • CX02
  p2 = trans (sym p0) p1

  p3 : CX12 • SWAP01 ≈ CX12 • SWAP01
  p3 = refl

  p4 : SWAP01 • CX02 ≈ SWAP01 • CX02
  p4 = refl

  p5 : CX12 • SWAP01 ≈ SWAP01 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP01 • CX02 ≈ CX12 • SWAP01
  p6 = sym p5

  proved : SWAP01 • CX02 ≈ CX12 • SWAP01
  proved = p6

module KB0376 where

  p0 : CX10 • CX01 • CCX02 • CX02 ≈ CX10 • CX02 • CCX02
  p0 = by-assoc-and (under (CX10) (ε) KB0119.proved) Eq.refl Eq.refl

  p1 : CX10 • CX01 • CCX02 • CX02 ≈ CX01 • SWAP01 • CCX02 • CX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX02) KB0088.proved) Eq.refl Eq.refl

  p2 : CX10 • CX02 • CCX02 ≈ CX01 • SWAP01 • CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : CX10 • CX02 • CCX02 ≈ CX10 • CX02 • CCX02
  p3 = refl

  p4 : CX01 • SWAP01 • CCX02 • CX02 ≈ CX01 • CCX12 • SWAP01 • CX02
  p4 = by-assoc-and (under (CX01) (CX02) KB0090.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • SWAP01 • CX02 ≈ CX01 • CCX12 • CX12 • SWAP01
  p5 = by-assoc-and (under (CX01 • CCX12) (ε) KB0102.proved) Eq.refl Eq.refl

  p6 : CX01 • SWAP01 • CCX02 • CX02 ≈ CX01 • CCX12 • CX12 • SWAP01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX10 • CX02 • CCX02 ≈ CX01 • CCX12 • CX12 • SWAP01
  p7 = trans (sym p3) (trans p2 p6)

  p8 : CX01 • CCX12 • CX12 • SWAP01 ≈ CX10 • CX02 • CCX02
  p8 = sym p7

  proved : CX01 • CCX12 • CX12 • SWAP01 ≈ CX10 • CX02 • CCX02
  proved = p8

module KB1890 where

  p0 : CX01 • CCX12 • CX12 • SWAP01 • CX10 ≈ CX10 • CX02 • CCX02 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0376.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX12 • CX12 • SWAP01 • CX10 ≈ CX01 • CCX12 • CX12 • CX01 • SWAP01
  p1 = by-assoc-and (under (CX01 • CCX12 • CX12) (ε) KB0112.proved) Eq.refl Eq.refl

  p2 : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX10 • CX02 • CCX02 • CX10 ≈ CX10 • CX02 • CCX02 • CX10
  p3 = refl

  p4 : CX01 • CCX12 • CX12 • CX01 • SWAP01 ≈ CX01 • CCX12 • CX10 • CX12 • CX01
  p4 = by-assoc-and (under (CX01 • CCX12) (ε) KB0261.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • CX10 • CX12 • CX01 ≈ CX01 • CX10 • CCX12 • CX12 • CX01
  p5 = by-assoc-and (under (CX01) (CX12 • CX01) KB0032.proved) Eq.refl Eq.refl

  p6 : CX01 • CX10 • CCX12 • CX12 • CX01 ≈ CX01 • CX12 • CCX12 • CX01
  p6 = by-assoc-and (under (CX01) (CX01) KB0141.proved) Eq.refl Eq.refl

  p7 : CX01 • CCX12 • CX12 • CX01 • SWAP01 ≈ CX01 • CX12 • CCX12 • CX01
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CX12 • CCX12 • CX01
  p8 = trans (sym p3) (trans p2 p7)

  proved : CX10 • CX02 • CCX02 • CX10 ≈ CX01 • CX12 • CCX12 • CX01
  proved = p8

module KB0318 where

  p0 : X0 • X0 • X2 • CX20 ≈ X0 • CX20 • X2
  p0 = by-assoc-and (under (X0) (ε) KB0316.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • X2 • CX20 ≈ X2 • CX20
  p1 = by-assoc-and (under (ε) (X2 • CX20) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX20 • X2 ≈ X2 • CX20
  p2 = trans (sym p0) p1

  p3 : X0 • CX20 • X2 ≈ X0 • CX20 • X2
  p3 = refl

  p4 : X2 • CX20 ≈ X2 • CX20
  p4 = refl

  p5 : X0 • CX20 • X2 ≈ X2 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CX20 • X2 ≈ X2 • CX20
  proved = p5
