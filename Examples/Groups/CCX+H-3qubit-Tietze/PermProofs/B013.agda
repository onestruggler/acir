{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B013 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0010 ; module KB0011 ; module KB0013 ; module KB0023 ; module KB0028 ; module KB0029 ; module KB0033 ; module KB0046 ; module KB0120 ; module KB0125 ; module KB0160 ; module KB0186 ; module KB0216 ; module KB0477)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0002 ; module KB0020 ; module KB0025 ; module KB0043 ; module KB0122 ; module KB0123 ; module KB0124 ; module KB0165 ; module KB0328 ; module KB0709)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0000 ; module KB0018 ; module KB0019 ; module KB0042 ; module KB0090 ; module KB0097 ; module KB0149 ; module KB0221 ; module KB0228 ; module KB0264 ; module KB0435)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0088 ; module KB0152 ; module KB0202)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0041 ; module KB0260 ; module KB0423)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0196)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0188 ; module KB0291 ; module KB0336)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0259 ; module KB1097)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module symmetry_CX_h ; module symmetry_SWAP02)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module symmetry_SWAP01)

module KB2062 where

  p0 : CX02 • X2 • CX01 • CX10 • CCX12 ≈ CX02 • CX01 • CCX12 • X2
  p0 = by-assoc-and (under (CX02) (ε) KB0423.proved) Eq.refl Eq.refl

  p1 : CX02 • X2 • CX01 • CX10 • CCX12 ≈ X2 • CX02 • CX01 • CX10 • CCX12
  p1 = by-assoc-and (under (ε) (CX01 • CX10 • CCX12) KB0033.proved) Eq.refl Eq.refl

  p2 : CX02 • CX01 • CCX12 • X2 ≈ X2 • CX02 • CX01 • CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CX01 • CCX12 • X2 ≈ CX01 • CX02 • CCX12 • X2
  p3 = by-assoc-and (under (ε) (CCX12 • X2) KB0025.proved) Eq.refl Eq.refl

  p4 : CX02 • CX01 • CCX12 • X2 ≈ CX01 • CX02 • CCX12 • X2
  p4 = trans p3 (refl)

  p5 : X2 • CX02 • CX01 • CX10 • CCX12 ≈ X2 • CX01 • CX02 • CX10 • CCX12
  p5 = by-assoc-and (under (X2) (CX10 • CCX12) KB0025.proved) Eq.refl Eq.refl

  p6 : X2 • CX02 • CX01 • CX10 • CCX12 ≈ X2 • CX01 • CX02 • CX10 • CCX12
  p6 = trans p5 (refl)

  p7 : CX01 • CX02 • CCX12 • X2 ≈ X2 • CX01 • CX02 • CX10 • CCX12
  p7 = trans (sym p4) (trans p2 p6)

  p8 : X2 • CX01 • CX02 • CX10 • CCX12 ≈ CX01 • CX02 • CCX12 • X2
  p8 = sym p7

  proved : X2 • CX01 • CX02 • CX10 • CCX12 ≈ CX01 • CX02 • CCX12 • X2
  proved = p8

module KB0048 where

  p0 : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
  p0 = symmetry_SWAP01.proved

  p1 : SWAP01 ≈ SWAP01
  p1 = refl

  p2 : SWAP02 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • SWAP02
  p2 = refl

  p3 : SWAP01 ≈ SWAP02 • SWAP12 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • SWAP12 • SWAP02 ≈ SWAP01
  p4 = sym p3

  proved : SWAP02 • SWAP12 • SWAP02 ≈ SWAP01
  proved = p4

module KB0049 where

  p0 : SWAP02 • SWAP02 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
  p0 = by-assoc-and (under (SWAP02) (ε) KB0048.proved) Eq.refl Eq.refl

  p1 : SWAP02 • SWAP02 • SWAP12 • SWAP02 ≈ SWAP12 • SWAP02
  p1 = by-assoc-and (under (ε) (SWAP12 • SWAP02) KB0002.proved) Eq.refl Eq.refl

  p2 : SWAP02 • SWAP01 ≈ SWAP12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • SWAP01 ≈ SWAP02 • SWAP01
  p3 = refl

  p4 : SWAP12 • SWAP02 ≈ SWAP12 • SWAP02
  p4 = refl

  p5 : SWAP02 • SWAP01 ≈ SWAP12 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
  p6 = sym p5

  proved : SWAP12 • SWAP02 ≈ SWAP02 • SWAP01
  proved = p6

module KB0051 where

  p0 : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
  p0 = symmetry_SWAP02.proved

  p1 : SWAP02 ≈ SWAP02
  p1 = refl

  p2 : SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01
  p2 = refl

  p3 : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • SWAP12 • SWAP01 ≈ SWAP02
  p4 = sym p3

  proved : SWAP01 • SWAP12 • SWAP01 ≈ SWAP02
  proved = p4

module KB0053 where

  p0 : SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP02 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0051.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP12
  p1 = by-assoc-and (under (SWAP01 • SWAP12) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
  p2 = trans (sym p0) p1

  p3 : SWAP02 • SWAP01 ≈ SWAP02 • SWAP01
  p3 = refl

  p4 : SWAP01 • SWAP12 ≈ SWAP01 • SWAP12
  p4 = refl

  p5 : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • SWAP01 ≈ SWAP01 • SWAP12
  proved = p5

module KB0232 where

  p0 : CX21 • SWAP12 • SWAP02 ≈ CX21 • SWAP02 • SWAP01
  p0 = by-assoc-and (under (CX21) (ε) KB0049.proved) Eq.refl Eq.refl

  p1 : CX21 • SWAP12 • SWAP02 ≈ CX12 • CX21 • SWAP02
  p1 = by-assoc-and (under (ε) (SWAP02) KB0041.proved) Eq.refl Eq.refl

  p2 : CX21 • SWAP02 • SWAP01 ≈ CX12 • CX21 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX21 • SWAP02 • SWAP01 ≈ CX21 • SWAP01 • SWAP12
  p3 = by-assoc-and (under (CX21) (ε) KB0053.proved) Eq.refl Eq.refl

  p4 : CX21 • SWAP02 • SWAP01 ≈ CX21 • SWAP01 • SWAP12
  p4 = trans p3 (refl)

  p5 : CX12 • CX21 • SWAP02 ≈ CX12 • CX21 • SWAP02
  p5 = refl

  p6 : CX21 • SWAP01 • SWAP12 ≈ CX12 • CX21 • SWAP02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX21 • SWAP01 • SWAP12 ≈ CX12 • CX21 • SWAP02
  proved = p6

module KB0064 where

  p0 : CX20 ≈ SWAP01 • CX21 • SWAP01
  p0 = symmetry_CX_h.proved

  p1 : CX20 ≈ CX20
  p1 = refl

  p2 : SWAP01 • CX21 • SWAP01 ≈ SWAP01 • CX21 • SWAP01
  p2 = refl

  p3 : CX20 ≈ SWAP01 • CX21 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • CX21 • SWAP01 ≈ CX20
  p4 = sym p3

  proved : SWAP01 • CX21 • SWAP01 ≈ CX20
  proved = p4

module KB0065 where

  p0 : SWAP01 • SWAP01 • CX21 • SWAP01 ≈ SWAP01 • CX20
  p0 = by-assoc-and (under (SWAP01) (ε) KB0064.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • CX21 • SWAP01 ≈ CX21 • SWAP01
  p1 = by-assoc-and (under (ε) (CX21 • SWAP01) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CX20 ≈ CX21 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CX20 ≈ SWAP01 • CX20
  p3 = refl

  p4 : CX21 • SWAP01 ≈ CX21 • SWAP01
  p4 = refl

  p5 : SWAP01 • CX20 ≈ CX21 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CX20 ≈ CX21 • SWAP01
  proved = p5

module KB0241 where

  p0 : CX10 • SWAP01 • CX20 ≈ CX10 • CX21 • SWAP01
  p0 = by-assoc-and (under (CX10) (ε) KB0065.proved) Eq.refl Eq.refl

  p1 : CX10 • SWAP01 • CX20 ≈ CX01 • CX10 • CX20
  p1 = by-assoc-and (under (ε) (CX20) KB0042.proved) Eq.refl Eq.refl

  p2 : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
  p2 = trans (sym p0) p1

  p3 : CX10 • CX21 • SWAP01 ≈ CX10 • CX21 • SWAP01
  p3 = refl

  p4 : CX01 • CX10 • CX20 ≈ CX01 • CX10 • CX20
  p4 = refl

  p5 : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX21 • SWAP01 ≈ CX01 • CX10 • CX20
  proved = p5

module KB1029 where

  p0 : CX10 • CX21 • SWAP01 • SWAP12 ≈ CX01 • CX10 • CX20 • SWAP12
  p0 = by-assoc-and (under (ε) (SWAP12) KB0241.proved) Eq.refl Eq.refl

  p1 : CX10 • CX21 • SWAP01 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
  p1 = by-assoc-and (under (CX10) (ε) KB0232.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CX20 • SWAP12 ≈ CX01 • CX10 • CX20 • SWAP12
  p3 = refl

  p4 : CX10 • CX12 • CX21 • SWAP02 ≈ CX10 • CX12 • CX21 • SWAP02
  p4 = refl

  p5 : CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CX12 • CX21 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CX12 • CX21 • SWAP02 ≈ CX01 • CX10 • CX20 • SWAP12
  p6 = sym p5

  proved : CX10 • CX12 • CX21 • SWAP02 ≈ CX01 • CX10 • CX20 • SWAP12
  proved = p6

module KB2850 where

  p0 : CCX01 • CX10 • CX12 • CX21 • SWAP02 ≈ CCX01 • CX01 • CX10 • CX20 • SWAP12
  p0 = by-assoc-and (under (CCX01) (ε) KB1029.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX10 • CX12 • CX21 • SWAP02 ≈ CX10 • CCX01 • CX21 • SWAP02
  p1 = by-assoc-and (under (ε) (CX21 • SWAP02) KB0202.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CCX01 • CX01 • CX10 • CX20 • SWAP12
  p3 = refl

  p4 : CX10 • CCX01 • CX21 • SWAP02 ≈ CX10 • CCX01 • CX21 • SWAP02
  p4 = refl

  p5 : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX01 • CX10 • CX20 • SWAP12 ≈ CX10 • CCX01 • CX21 • SWAP02
  proved = p5

module KB3121 where

  p0 : CCX01 • CX21 • CX02 • CX20 • X2 ≈ CX01 • CCX01 • CX21 • CX20 • X2
  p0 = by-assoc-and (under (ε) (CX20 • X2) KB0291.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CX02 • CX20 • X2 ≈ CCX01 • CX21 • X0 • CX02 • CX20
  p1 = by-assoc-and (under (CCX01 • CX21) (ε) KB0260.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CCX01 • CX21 • X0 • CX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CX01 • CCX01 • CX20 • CX21 • X2
  p3 = by-assoc-and (under (CX01 • CCX01) (X2) KB0043.proved) Eq.refl Eq.refl

  p4 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CX01 • CCX01 • CX20 • CX21 • X2
  p4 = trans p3 (refl)

  p5 : CCX01 • CX21 • X0 • CX02 • CX20 ≈ CCX01 • X0 • CX21 • CX02 • CX20
  p5 = by-assoc-and (under (CCX01) (CX02 • CX20) KB0020.proved) Eq.refl Eq.refl

  p6 : CCX01 • X0 • CX21 • CX02 • CX20 ≈ CCX01 • X0 • CX02 • CX20 • CX01
  p6 = by-assoc-and (under (CCX01 • X0) (ε) KB0259.proved) Eq.refl Eq.refl

  p7 : CCX01 • X0 • CX02 • CX20 • CX01 ≈ CX02 • CCX01 • CX20 • X2 • CX01
  p7 = by-assoc-and (under (ε) (CX01) KB1097.proved) Eq.refl Eq.refl

  p8 : CCX01 • CX21 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2 • CX01
  p8 = trans p5 (trans p6 (trans p7 (refl)))

  p9 : CX01 • CCX01 • CX20 • CX21 • X2 ≈ CX02 • CCX01 • CX20 • X2 • CX01
  p9 = trans (sym p4) (trans p2 p8)

  p10 : CX02 • CCX01 • CX20 • X2 • CX01 ≈ CX01 • CCX01 • CX20 • CX21 • X2
  p10 = sym p9

  proved : CX02 • CCX01 • CX20 • X2 • CX01 ≈ CX01 • CCX01 • CX20 • CX21 • X2
  proved = p10

module KB0224 where

  p0 : CCX01 • X2 • X1 ≈ X2 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0029.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • X1 ≈ CCX01 • X1 • X2
  p1 = by-assoc-and (under (CCX01) (ε) KB0019.proved) Eq.refl Eq.refl

  p2 : X2 • CCX01 • X1 ≈ CCX01 • X1 • X2
  p2 = trans (sym p0) p1

  p3 : X2 • CCX01 • X1 ≈ X2 • CCX01 • X1
  p3 = refl

  p4 : CCX01 • X1 • X2 ≈ CCX01 • X1 • X2
  p4 = refl

  p5 : X2 • CCX01 • X1 ≈ CCX01 • X1 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • X1 • X2 ≈ X2 • CCX01 • X1
  p6 = sym p5

  proved : CCX01 • X1 • X2 ≈ X2 • CCX01 • X1
  proved = p6

module KB0662 where

  p0 : X0 • CX21 • CCX02 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
  p0 = by-assoc-and (under (X0) (ε) KB0328.proved) Eq.refl Eq.refl

  p1 : X0 • CX21 • CCX02 • CCX01 • CX21 ≈ CCX02 • X0 • CCX01 • CX21
  p1 = by-assoc-and (under (ε) (CCX01 • CX21) KB0165.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • CCX02 ≈ CCX02 • X0 • CCX01 • CX21
  p2 = trans (sym p0) p1

  p3 : X0 • CCX01 • CCX02 ≈ X0 • CCX01 • CCX02
  p3 = refl

  p4 : CCX02 • X0 • CCX01 • CX21 ≈ CCX02 • X0 • CCX01 • CX21
  p4 = refl

  p5 : X0 • CCX01 • CCX02 ≈ CCX02 • X0 • CCX01 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • X0 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX02 • X0 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
  proved = p6

module KB0187 where

  p0 : CCX01 • CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0152.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • X0 • CCX01 ≈ X0 • CCX01
  p1 = by-assoc-and (under (ε) (X0 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX12 ≈ X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX12 ≈ CCX01 • X0 • CX12
  p3 = refl

  p4 : X0 • CCX01 ≈ X0 • CCX01
  p4 = refl

  p5 : CCX01 • X0 • CX12 ≈ X0 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X0 • CX12 ≈ X0 • CCX01
  proved = p5

module KB0229 where

  p0 : CX02 • X1 • X0 ≈ CX02 • X0 • X1
  p0 = by-assoc-and (under (CX02) (ε) KB0044.proved) Eq.refl Eq.refl

  p1 : CX02 • X1 • X0 ≈ X1 • CX02 • X0
  p1 = by-assoc-and (under (ε) (X0) KB0023.proved) Eq.refl Eq.refl

  p2 : CX02 • X0 • X1 ≈ X1 • CX02 • X0
  p2 = trans (sym p0) p1

  p3 : CX02 • X0 • X1 ≈ CX02 • X0 • X1
  p3 = refl

  p4 : X1 • CX02 • X0 ≈ X1 • CX02 • X0
  p4 = refl

  p5 : CX02 • X0 • X1 ≈ X1 • CX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • X0 • X1 ≈ X1 • CX02 • X0
  proved = p5

module KB0832 where

  p0 : CX02 • X0 • CX02 • CCX01 • X1 ≈ X0 • X2 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (CCX01 • X1) KB0160.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • CX02 • CCX01 • X1 ≈ CX02 • X0 • X1 • CCX01
  p1 = by-assoc-and (under (CX02 • X0) (ε) KB0120.proved) Eq.refl Eq.refl

  p2 : X0 • X2 • CCX01 • X1 ≈ CX02 • X0 • X1 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • X2 • CCX01 • X1 ≈ X0 • X2 • CCX01 • X1
  p3 = refl

  p4 : CX02 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01) KB0229.proved) Eq.refl Eq.refl

  p5 : CX02 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CCX01
  p5 = trans p4 (refl)

  p6 : X0 • X2 • CCX01 • X1 ≈ X1 • CX02 • X0 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
  p7 = sym p6

  proved : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
  proved = p7

module KB0897 where

  p0 : CCX01 • X1 • CCX01 • X0 • CCX01 ≈ X1 • CX02 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (X0 • CCX01) KB0186.proved) Eq.refl Eq.refl

  p1 : CCX01 • X1 • CCX01 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CX12
  p1 = by-assoc-and (under (CCX01 • X1) (ε) KB0152.proved) Eq.refl Eq.refl

  p2 : X1 • CX02 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
  p3 = by-assoc-and (under (ε) (ε) KB0832.proved) Eq.refl Eq.refl

  p4 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
  p4 = trans p3 (refl)

  p5 : CCX01 • X1 • X0 • CX12 ≈ CCX01 • X0 • X1 • CX12
  p5 = by-assoc-and (under (CCX01) (CX12) KB0044.proved) Eq.refl Eq.refl

  p6 : CCX01 • X1 • X0 • CX12 ≈ CCX01 • X0 • X1 • CX12
  p6 = trans p5 (refl)

  p7 : X0 • X2 • CCX01 • X1 ≈ CCX01 • X0 • X1 • CX12
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CCX01 • X0 • X1 • CX12 ≈ X0 • X2 • CCX01 • X1
  p8 = sym p7

  proved : CCX01 • X0 • X1 • CX12 ≈ X0 • X2 • CCX01 • X1
  proved = p8

module KB3634 where

  p0 : X1 • CCX02 • CX02 • CCX01 • X0 • CX12 ≈ CCX02 • CCX01 • X1 • X0 • CX12
  p0 = by-assoc-and (under (ε) (X0 • CX12) KB0477.proved) Eq.refl Eq.refl

  p1 : X1 • CCX02 • CX02 • CCX01 • X0 • CX12 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p1 = by-assoc-and (under (X1 • CCX02 • CX02) (ε) KB0187.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ CCX02 • CCX01 • X0 • X1 • CX12
  p3 = by-assoc-and (under (CCX02 • CCX01) (CX12) KB0044.proved) Eq.refl Eq.refl

  p4 : CCX02 • CCX01 • X0 • X1 • CX12 ≈ CCX02 • X0 • X2 • CCX01 • X1
  p4 = by-assoc-and (under (CCX02) (ε) KB0897.proved) Eq.refl Eq.refl

  p5 : CCX02 • CCX01 • X1 • X0 • CX12 ≈ CCX02 • X0 • X2 • CCX01 • X1
  p5 = trans p3 (trans p4 (refl))

  p6 : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p6 = refl

  p7 : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p7 = trans (sym p5) (trans p2 p6)

  proved : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  proved = p7

module KB4008 where

  p0 : CCX02 • X0 • CCX01 • CX21 • X2 • CX21 ≈ X0 • CCX01 • CCX02 • X2 • CX21
  p0 = by-assoc-and (under (ε) (X2 • CX21) KB0662.proved) Eq.refl Eq.refl

  p1 : CCX02 • X0 • CCX01 • CX21 • X2 • CX21 ≈ CCX02 • X0 • CCX01 • X1 • X2
  p1 = by-assoc-and (under (CCX02 • X0 • CCX01) (ε) KB0196.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ CCX02 • X0 • CCX01 • X1 • X2
  p2 = trans (sym p0) p1

  p3 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ X0 • CCX01 • CCX02 • X2 • CX21
  p3 = refl

  p4 : CCX02 • X0 • CCX01 • X1 • X2 ≈ CCX02 • X0 • X2 • CCX01 • X1
  p4 = by-assoc-and (under (CCX02 • X0) (ε) KB0224.proved) Eq.refl Eq.refl

  p5 : CCX02 • X0 • X2 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p5 = by-assoc-and (under (ε) (ε) KB3634.proved) Eq.refl Eq.refl

  p6 : CCX02 • X0 • CCX01 • X1 • X2 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p6 = trans p4 (trans p5 (refl))

  p7 : X0 • CCX01 • CCX02 • X2 • CX21 ≈ X1 • CCX02 • CX02 • X0 • CCX01
  p7 = trans (sym p3) (trans p2 p6)

  p8 : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CCX02 • X2 • CX21
  p8 = sym p7

  proved : X1 • CCX02 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CCX02 • X2 • CX21
  proved = p8

module KB4158 where

  p0 : CX02 • CCX12 • CX01 • CCX01 • X0 • CCX01 ≈ CCX01 • CCX12 • CX01 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (X0 • CCX01) KB0709.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX12 • CX01 • CCX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
  p1 = by-assoc-and (under (CX02 • CCX12 • CX01) (ε) KB0152.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CCX01 • CCX12 • CX01 • X0 • CCX01
  p3 = refl

  p4 : CX02 • CCX12 • CX01 • X0 • CX12 ≈ CX02 • CCX12 • CX01 • X0 • CX12
  p4 = refl

  p5 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
  proved = p5

module KB1275 where

  p0 : CCX12 • CCX02 • CX10 • X0 ≈ CX10 • CCX02 • CCX12 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0336.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CX10 • X0 ≈ CCX12 • CCX02 • X0 • CX10
  p1 = by-assoc-and (under (CCX12 • CCX02) (ε) KB0047.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX12 • X0 ≈ CCX12 • CCX02 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX12 • X0 ≈ CX10 • CCX02 • X0 • CCX12
  p3 = by-assoc-and (under (CX10 • CCX02) (ε) KB0046.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX02 • CCX12 • X0 ≈ CX10 • CCX02 • X0 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX02 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • CX10
  p5 = refl

  p6 : CX10 • CCX02 • X0 • CCX12 ≈ CCX12 • CCX02 • X0 • CX10
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX12 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CCX12
  p7 = sym p6

  proved : CCX12 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CCX12
  proved = p7

module KB1274 where

  p0 : CCX12 • CCX02 • CX10 • X2 ≈ CX10 • CCX02 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0336.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CX10 • X2 ≈ CCX12 • CCX02 • X2 • CX10
  p1 = by-assoc-and (under (CCX12 • CCX02) (ε) KB0021.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX12 • X2 ≈ CCX12 • CCX02 • X2 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX12 • X2 ≈ CX10 • CCX02 • CCX12 • X2
  p3 = refl

  p4 : CCX12 • CCX02 • X2 • CX10 ≈ CCX12 • CCX02 • X2 • CX10
  p4 = refl

  p5 : CX10 • CCX02 • CCX12 • X2 ≈ CCX12 • CCX02 • X2 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX02 • X2 • CX10 ≈ CX10 • CCX02 • CCX12 • X2
  p6 = sym p5

  proved : CCX12 • CCX02 • X2 • CX10 ≈ CX10 • CCX02 • CCX12 • X2
  proved = p6

module KB0389 where

  p0 : CX10 • X2 • CX01 • CCX02 ≈ CX10 • CCX02 • X2
  p0 = by-assoc-and (under (CX10) (ε) KB0122.proved) Eq.refl Eq.refl

  p1 : CX10 • X2 • CX01 • CCX02 ≈ X2 • CX10 • CX01 • CCX02
  p1 = by-assoc-and (under (ε) (CX01 • CCX02) KB0021.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • X2 ≈ X2 • CX10 • CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • X2 ≈ CX10 • CCX02 • X2
  p3 = refl

  p4 : X2 • CX10 • CX01 • CCX02 ≈ X2 • CX01 • SWAP01 • CCX02
  p4 = by-assoc-and (under (X2) (CCX02) KB0088.proved) Eq.refl Eq.refl

  p5 : X2 • CX01 • SWAP01 • CCX02 ≈ X2 • CX01 • CCX12 • SWAP01
  p5 = by-assoc-and (under (X2 • CX01) (ε) KB0090.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CX01 • CCX02 ≈ X2 • CX01 • CCX12 • SWAP01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX10 • CCX02 • X2 ≈ X2 • CX01 • CCX12 • SWAP01
  p7 = trans (sym p3) (trans p2 p6)

  p8 : X2 • CX01 • CCX12 • SWAP01 ≈ CX10 • CCX02 • X2
  p8 = sym p7

  proved : X2 • CX01 • CCX12 • SWAP01 ≈ CX10 • CCX02 • X2
  proved = p8

module KB1276 where

  p0 : CCX02 • CCX12 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX02 • CCX12
  p0 = by-assoc-and (under (CCX02) (ε) KB0336.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX12 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01 • CX10
  p1 = by-assoc-and (under (ε) (CX10) KB0216.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX10 • CCX02 • CCX12 ≈ CX01 • CCX12 • CX01 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX10 • CCX02 • CCX12 ≈ CCX02 • CX10 • CCX02 • CCX12
  p3 = refl

  p4 : CX01 • CCX12 • CX01 • CX10 ≈ CX01 • CX10 • CCX12 • SWAP01
  p4 = by-assoc-and (under (CX01) (ε) KB0228.proved) Eq.refl Eq.refl

  p5 : CX01 • CX10 • CCX12 • SWAP01 ≈ CX01 • CX01 • CX10 • CCX02
  p5 = by-assoc-and (under (CX01) (ε) KB0264.proved) Eq.refl Eq.refl

  p6 : CX01 • CX01 • CX10 • CCX02 ≈ CX10 • CCX02
  p6 = by-assoc-and (under (ε) (CX10 • CCX02) KB0013.proved) Eq.refl Eq.refl

  p7 : CX01 • CCX12 • CX01 • CX10 ≈ CX10 • CCX02
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CCX02 • CX10 • CCX02 • CCX12 ≈ CX10 • CCX02
  p8 = trans (sym p3) (trans p2 p7)

  proved : CCX02 • CX10 • CCX02 • CCX12 ≈ CX10 • CCX02
  proved = p8

module KB1277 where

  p0 : CCX02 • CCX02 • CX10 • CCX02 • CCX12 ≈ CCX02 • CX10 • CCX02
  p0 = by-assoc-and (under (CCX02) (ε) KB1276.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CX10 • CCX02 • CCX12 ≈ CX10 • CCX02 • CCX12
  p1 = by-assoc-and (under (ε) (CX10 • CCX02 • CCX12) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX10 • CCX02 ≈ CX10 • CCX02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX10 • CCX02 ≈ CCX02 • CX10 • CCX02
  p3 = refl

  p4 : CX10 • CCX02 • CCX12 ≈ CX10 • CCX02 • CCX12
  p4 = refl

  p5 : CCX02 • CX10 • CCX02 ≈ CX10 • CCX02 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX10 • CCX02 ≈ CX10 • CCX02 • CCX12
  proved = p5

module KB1310 where

  p0 : CCX02 • X2 • CX01 • CCX12 • SWAP01 ≈ CCX02 • CX10 • CCX02 • X2
  p0 = by-assoc-and (under (CCX02) (ε) KB0389.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • CCX12 • SWAP01 ≈ X2 • CCX02 • CCX12 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX12 • SWAP01) KB0188.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX10 • CCX02 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX10 • CCX02 • X2 ≈ CX10 • CCX02 • CCX12 • X2
  p3 = by-assoc-and (under (ε) (X2) KB1277.proved) Eq.refl Eq.refl

  p4 : CCX02 • CX10 • CCX02 • X2 ≈ CX10 • CCX02 • CCX12 • X2
  p4 = trans p3 (refl)

  p5 : X2 • CCX02 • CCX12 • SWAP01 ≈ X2 • CCX02 • CCX12 • SWAP01
  p5 = refl

  p6 : CX10 • CCX02 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX10 • CCX02 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • SWAP01
  proved = p6

module KB5022 where

  p0 : CCX12 • CCX02 • X2 • CX10 • X0 ≈ CX10 • CCX02 • CCX12 • X2 • X0
  p0 = by-assoc-and (under (ε) (X0) KB1274.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • X2 • CX10 • X0 ≈ CCX12 • CCX02 • X2 • X0 • CX10
  p1 = by-assoc-and (under (CCX12 • CCX02 • X2) (ε) KB0047.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ CCX12 • CCX02 • X2 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ X2 • CCX02 • CCX12 • SWAP01 • X0
  p3 = by-assoc-and (under (ε) (X0) KB1310.proved) Eq.refl Eq.refl

  p4 : X2 • CCX02 • CCX12 • SWAP01 • X0 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p4 = by-assoc-and (under (X2 • CCX02 • CCX12) (ε) KB0097.proved) Eq.refl Eq.refl

  p5 : CX10 • CCX02 • CCX12 • X2 • X0 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX12 • CCX02 • X2 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • X2 • CX10
  p6 = by-assoc-and (under (CCX12 • CCX02) (CX10) KB0018.proved) Eq.refl Eq.refl

  p7 : CCX12 • CCX02 • X2 • X0 • CX10 ≈ CCX12 • CCX02 • X0 • X2 • CX10
  p7 = trans p6 (refl)

  p8 : X2 • CCX02 • CCX12 • X1 • SWAP01 ≈ CCX12 • CCX02 • X0 • X2 • CX10
  p8 = trans (sym p5) (trans p2 p7)

  p9 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p9 = sym p8

  proved : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  proved = p9

module KB5023 where

  p0 : CCX12 • CCX02 • X0 • CX10 • X2 ≈ CX10 • CCX02 • X0 • CCX12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB1275.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • X0 • CX10 • X2 ≈ CCX12 • CCX02 • X0 • X2 • CX10
  p1 = by-assoc-and (under (CCX12 • CCX02 • X0) (ε) KB0021.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ CCX12 • CCX02 • X0 • X2 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ CX10 • CCX02 • X0 • CCX12 • X2
  p3 = refl

  p4 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p4 = by-assoc-and (under (ε) (ε) KB5022.proved) Eq.refl Eq.refl

  p5 : CCX12 • CCX02 • X0 • X2 • CX10 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p5 = trans p4 (refl)

  p6 : CX10 • CCX02 • X0 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX10 • CCX02 • X0 • CCX12 • X2 ≈ X2 • CCX02 • CCX12 • X1 • SWAP01
  proved = p6

module KB0901 where

  p0 : CCX02 • X2 • CX01 • CX02 • CCX01 ≈ X2 • CCX02 • CX02 • CCX01
  p0 = by-assoc-and (under (ε) (CX02 • CCX01) KB0188.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • CX02 • CCX01 ≈ CCX02 • X2 • CCX01 • CX01
  p1 = by-assoc-and (under (CCX02 • X2) (ε) KB0123.proved) Eq.refl Eq.refl

  p2 : X2 • CCX02 • CX02 • CCX01 ≈ CCX02 • X2 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : X2 • CCX02 • CX02 • CCX01 ≈ X2 • CCX02 • CX02 • CCX01
  p3 = refl

  p4 : CCX02 • X2 • CCX01 • CX01 ≈ CCX02 • X2 • CCX01 • CX01
  p4 = refl

  p5 : X2 • CCX02 • CX02 • CCX01 ≈ CCX02 • X2 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • X2 • CCX01 • CX01 ≈ X2 • CCX02 • CX02 • CCX01
  p6 = sym p5

  proved : CCX02 • X2 • CCX01 • CX01 ≈ X2 • CCX02 • CX02 • CCX01
  proved = p6

module KB2091 where

  p0 : CCX02 • X2 • CX01 • CCX01 • X1 ≈ CCX02 • X2 • X1 • CCX01 • CX01
  p0 = by-assoc-and (under (CCX02 • X2) (ε) KB0435.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • CCX01 • X1 ≈ X2 • CCX02 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0188.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ X2 • CCX02 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ CCX02 • X1 • X2 • CCX01 • CX01
  p3 = by-assoc-and (under (CCX02) (CCX01 • CX01) KB0019.proved) Eq.refl Eq.refl

  p4 : CCX02 • X1 • X2 • CCX01 • CX01 ≈ X1 • CCX02 • X2 • CCX01 • CX01
  p4 = by-assoc-and (under (ε) (X2 • CCX01 • CX01) KB0028.proved) Eq.refl Eq.refl

  p5 : X1 • CCX02 • X2 • CCX01 • CX01 ≈ X1 • X2 • CCX02 • CX02 • CCX01
  p5 = by-assoc-and (under (X1) (ε) KB0901.proved) Eq.refl Eq.refl

  p6 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ X1 • X2 • CCX02 • CX02 • CCX01
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  p7 : X2 • CCX02 • CCX01 • X1 ≈ X2 • CCX02 • CCX01 • X1
  p7 = refl

  p8 : X1 • X2 • CCX02 • CX02 • CCX01 ≈ X2 • CCX02 • CCX01 • X1
  p8 = trans (sym p6) (trans p2 p7)

  proved : X1 • X2 • CCX02 • CX02 • CCX01 ≈ X2 • CCX02 • CCX01 • X1
  proved = p8

module KB0586 where

  p0 : CX01 • X0 • X2 • CX02 ≈ X2 • CX01 • X0 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0221.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • X2 • CX02 ≈ CX01 • CX02 • X0
  p1 = by-assoc-and (under (CX01) (ε) KB0125.proved) Eq.refl Eq.refl

  p2 : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
  p2 = trans (sym p0) p1

  p3 : X2 • CX01 • X0 • CX02 ≈ X2 • CX01 • X0 • CX02
  p3 = refl

  p4 : CX01 • CX02 • X0 ≈ CX01 • CX02 • X0
  p4 = refl

  p5 : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
  proved = p5

module KB0809 where

  p0 : X0 • X1 • CX01 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
  p0 = by-assoc-and (under (X0 • X1) (ε) KB0149.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX01 • CX02 • CCX02 ≈ CX01 • X0 • CX02 • CCX02
  p1 = by-assoc-and (under (ε) (CX02 • CCX02) KB0124.proved) Eq.refl Eq.refl

  p2 : X0 • X1 • CCX02 • CX02 ≈ CX01 • X0 • CX02 • CCX02
  p2 = trans (sym p0) p1

  p3 : X0 • X1 • CCX02 • CX02 ≈ X0 • X1 • CCX02 • CX02
  p3 = refl

  p4 : CX01 • X0 • CX02 • CCX02 ≈ CX01 • X0 • CX02 • CCX02
  p4 = refl

  p5 : X0 • X1 • CCX02 • CX02 ≈ CX01 • X0 • CX02 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • X0 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
  p6 = sym p5

  proved : CX01 • X0 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CX02
  proved = p6

module KB2793 where

  p0 : X2 • CX01 • X0 • CX02 • CCX02 ≈ X2 • X0 • X1 • CCX02 • CX02
  p0 = by-assoc-and (under (X2) (ε) KB0809.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • X0 • CX02 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
  p1 = by-assoc-and (under (ε) (CCX02) KB0586.proved) Eq.refl Eq.refl

  p2 : X2 • X0 • X1 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
  p2 = trans (sym p0) p1

  p3 : X2 • X0 • X1 • CCX02 • CX02 ≈ X0 • X2 • X1 • CCX02 • CX02
  p3 = by-assoc-and (under (ε) (X1 • CCX02 • CX02) KB0018.proved) Eq.refl Eq.refl

  p4 : X0 • X2 • X1 • CCX02 • CX02 ≈ X0 • X1 • X2 • CCX02 • CX02
  p4 = by-assoc-and (under (X0) (CCX02 • CX02) KB0019.proved) Eq.refl Eq.refl

  p5 : X2 • X0 • X1 • CCX02 • CX02 ≈ X0 • X1 • X2 • CCX02 • CX02
  p5 = trans p3 (trans p4 (refl))

  p6 : CX01 • CX02 • X0 • CCX02 ≈ CX01 • CX02 • X0 • CCX02
  p6 = refl

  p7 : X0 • X1 • X2 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
  p7 = trans (sym p5) (trans p2 p6)

  proved : X0 • X1 • X2 • CCX02 • CX02 ≈ CX01 • CX02 • X0 • CCX02
  proved = p7

module KB5463 where

  p0 : X0 • X1 • X2 • CCX02 • CX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB2793.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • X2 • CCX02 • CX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
  p1 = by-assoc-and (under (X0) (ε) KB2091.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CCX01
  p3 = refl

  p4 : X0 • X2 • CCX02 • CCX01 • X1 ≈ X0 • X2 • CCX02 • CCX01 • X1
  p4 = refl

  p5 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
  proved = p5
