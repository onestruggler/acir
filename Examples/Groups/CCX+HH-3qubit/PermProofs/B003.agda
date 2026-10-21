{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B003 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; SWAP01 ; SWAP02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r013 ; r038 ; r042 ; refl ; sym ; trans ; under ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0009 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0014 ; module KB0023 ; module KB0026 ; module KB0027 ; module KB0031 ; module KB0033 ; module KB0035 ; module KB0046 ; module KB0118 ; module KB0121 ; module KB0127 ; module KB0144 ; module KB0147 ; module KB0151 ; module KB0216 ; module KB0338)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0002 ; module KB0025 ; module KB0038 ; module KB0086 ; module KB0122 ; module KB0124 ; module KB0157 ; module KB0159 ; module KB0211)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0000 ; module KB0004 ; module KB0005 ; module KB0018 ; module KB0032 ; module KB0045 ; module KB0090 ; module KB0091 ; module KB0141 ; module KB0149 ; module KB0221)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module symmetry_CX_b)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module drel67 ; module drel70)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module drel130 ; module drel135)

module KB0180 where

  p0 : CX10 • CX10 • CCX12 • CX12 ≈ CX10 • CX12 • CCX12
  p0 = by-assoc-and (under (CX10) (ε) KB0141.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CCX12 • CX12 ≈ CCX12 • CX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX12) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CX12 • CCX12 ≈ CX10 • CX12 • CCX12
  p3 = refl

  p4 : CCX12 • CX12 ≈ CCX12 • CX12
  p4 = refl

  p5 : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX12 • CCX12 ≈ CCX12 • CX12
  proved = p5

module KB0057 where

  p0 : CX10 ≈ SWAP02 • CX12 • SWAP02
  p0 = symmetry_CX_b.proved

  p1 : CX10 ≈ CX10
  p1 = refl

  p2 : SWAP02 • CX12 • SWAP02 ≈ SWAP02 • CX12 • SWAP02
  p2 = refl

  p3 : CX10 ≈ SWAP02 • CX12 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • CX12 • SWAP02 ≈ CX10
  p4 = sym p3

  proved : SWAP02 • CX12 • SWAP02 ≈ CX10
  proved = p4

module KB0059 where

  p0 : SWAP02 • CX12 • SWAP02 • SWAP02 ≈ CX10 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0057.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX12 • SWAP02 • SWAP02 ≈ SWAP02 • CX12
  p1 = by-assoc-and (under (SWAP02 • CX12) (ε) KB0002.proved) Eq.refl Eq.refl

  p2 : CX10 • SWAP02 ≈ SWAP02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • SWAP02 ≈ CX10 • SWAP02
  p3 = refl

  p4 : SWAP02 • CX12 ≈ SWAP02 • CX12
  p4 = refl

  p5 : CX10 • SWAP02 ≈ SWAP02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP02 • CX12 ≈ CX10 • SWAP02
  p6 = sym p5

  proved : SWAP02 • CX12 ≈ CX10 • SWAP02
  proved = p6

module KB0135 where

  p0 : CX12 • CX20 ≈ CX20 • CX12 • CX10
  p0 = drel135.proved

  p1 : CX12 • CX20 ≈ CX12 • CX20
  p1 = refl

  p2 : CX20 • CX12 • CX10 ≈ CX20 • CX10 • CX12
  p2 = by-assoc-and (under (CX20) (ε) KB0026.proved) Eq.refl Eq.refl

  p3 : CX20 • CX12 • CX10 ≈ CX20 • CX10 • CX12
  p3 = trans p2 (refl)

  p4 : CX12 • CX20 ≈ CX20 • CX10 • CX12
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX20 • CX10 • CX12 ≈ CX12 • CX20
  p5 = sym p4

  proved : CX20 • CX10 • CX12 ≈ CX12 • CX20
  proved = p5

module KB0175 where

  p0 : CX20 • CX20 • CX10 • CX12 ≈ CX20 • CX12 • CX20
  p0 = by-assoc-and (under (CX20) (ε) KB0135.proved) Eq.refl Eq.refl

  p1 : CX20 • CX20 • CX10 • CX12 ≈ CX10 • CX12
  p1 = by-assoc-and (under (ε) (CX10 • CX12) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • CX12 • CX20 ≈ CX10 • CX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CX12 • CX20 ≈ CX20 • CX12 • CX20
  p3 = refl

  p4 : CX10 • CX12 ≈ CX10 • CX12
  p4 = refl

  p5 : CX20 • CX12 • CX20 ≈ CX10 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CX12 • CX20 ≈ CX10 • CX12
  proved = p5

module KB0236 where

  p0 : SWAP02 • CX12 • CX02 ≈ CX10 • SWAP02 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0059.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX12 • CX02 ≈ SWAP02 • CX02 • CX12
  p1 = by-assoc-and (under (SWAP02) (ε) KB0027.proved) Eq.refl Eq.refl

  p2 : CX10 • SWAP02 • CX02 ≈ SWAP02 • CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • SWAP02 • CX02 ≈ CX10 • CX02 • CX20
  p3 = by-assoc-and (under (CX10) (ε) KB0086.proved) Eq.refl Eq.refl

  p4 : CX10 • SWAP02 • CX02 ≈ CX10 • CX02 • CX20
  p4 = trans p3 (refl)

  p5 : SWAP02 • CX02 • CX12 ≈ CX02 • CX20 • CX12
  p5 = by-assoc-and (under (ε) (CX12) KB0086.proved) Eq.refl Eq.refl

  p6 : SWAP02 • CX02 • CX12 ≈ CX02 • CX20 • CX12
  p6 = trans p5 (refl)

  p7 : CX10 • CX02 • CX20 ≈ CX02 • CX20 • CX12
  p7 = trans (sym p4) (trans p2 p6)

  proved : CX10 • CX02 • CX20 ≈ CX02 • CX20 • CX12
  proved = p7

module KB0310 where

  p0 : SWAP02 • CX12 • SWAP02 • CX02 ≈ SWAP02 • CX12 • CX02 • CX20
  p0 = by-assoc-and (under (SWAP02 • CX12) (ε) KB0086.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX12 • SWAP02 • CX02 ≈ CX10 • CX02
  p1 = by-assoc-and (under (ε) (CX02) KB0057.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CX12 • CX02 • CX20 ≈ CX10 • CX02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CX12 • CX02 • CX20 ≈ CX10 • SWAP02 • CX02 • CX20
  p3 = by-assoc-and (under (ε) (CX02 • CX20) KB0059.proved) Eq.refl Eq.refl

  p4 : CX10 • SWAP02 • CX02 • CX20 ≈ CX10 • CX02 • CX20 • CX20
  p4 = by-assoc-and (under (CX10) (CX20) KB0086.proved) Eq.refl Eq.refl

  p5 : CX10 • CX02 • CX20 • CX20 ≈ CX02 • CX20 • CX12 • CX20
  p5 = by-assoc-and (under (ε) (CX20) KB0236.proved) Eq.refl Eq.refl

  p6 : CX02 • CX20 • CX12 • CX20 ≈ CX02 • CX10 • CX12
  p6 = by-assoc-and (under (CX02) (ε) KB0175.proved) Eq.refl Eq.refl

  p7 : SWAP02 • CX12 • CX02 • CX20 ≈ CX02 • CX10 • CX12
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  p8 : CX10 • CX02 ≈ CX10 • CX02
  p8 = refl

  p9 : CX02 • CX10 • CX12 ≈ CX10 • CX02
  p9 = trans (sym p7) (trans p2 p8)

  proved : CX02 • CX10 • CX12 ≈ CX10 • CX02
  proved = p9

module KB0315 where

  p0 : CX02 • CX10 • CX12 • CCX12 ≈ CX10 • CX02 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0310.proved) Eq.refl Eq.refl

  p1 : CX02 • CX10 • CX12 • CCX12 ≈ CX02 • CCX12 • CX12
  p1 = by-assoc-and (under (CX02) (ε) KB0180.proved) Eq.refl Eq.refl

  p2 : CX10 • CX02 • CCX12 ≈ CX02 • CCX12 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CX02 • CCX12 ≈ CX10 • CX02 • CCX12
  p3 = refl

  p4 : CX02 • CCX12 • CX12 ≈ CX02 • CCX12 • CX12
  p4 = refl

  p5 : CX10 • CX02 • CCX12 ≈ CX02 • CCX12 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CX02 • CCX12 ≈ CX02 • CCX12 • CX12
  proved = p5

module KB0339 where

  p0 : CX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX01) (ε) KB0338.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CX01 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX01 • CCX12) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX02 ≈ CX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX12 • CX01 • CCX12 ≈ CCX12 • CX01 • CCX12
  p4 = refl

  p5 : CX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
  proved = p6

module KB0412 where

  p0 : CX12 • CX01 • CX02 • X1 ≈ CX01 • CX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0127.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX02 • X1 ≈ CX12 • CX01 • X1 • CX02
  p1 = by-assoc-and (under (CX12 • CX01) (ε) KB0023.proved) Eq.refl Eq.refl

  p2 : CX01 • CX12 • X1 ≈ CX12 • CX01 • X1 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CX12 • X1 ≈ CX01 • CX12 • X1
  p3 = refl

  p4 : CX12 • CX01 • X1 • CX02 ≈ CX12 • X1 • CX01 • CX02
  p4 = by-assoc-and (under (CX12) (CX02) KB0035.proved) Eq.refl Eq.refl

  p5 : CX12 • CX01 • X1 • CX02 ≈ CX12 • X1 • CX01 • CX02
  p5 = trans p4 (refl)

  p6 : CX01 • CX12 • X1 ≈ CX12 • X1 • CX01 • CX02
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX12 • X1 • CX01 • CX02 ≈ CX01 • CX12 • X1
  p7 = sym p6

  proved : CX12 • X1 • CX01 • CX02 ≈ CX01 • CX12 • X1
  proved = p7

module KB0158 where

  p0 : X0 • X0 • X1 • CX01 ≈ X0 • CX01 • X0
  p0 = by-assoc-and (under (X0) (ε) KB0124.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • X1 • CX01 ≈ X1 • CX01
  p1 = by-assoc-and (under (ε) (X1 • CX01) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX01 • X0 ≈ X1 • CX01
  p2 = trans (sym p0) p1

  p3 : X0 • CX01 • X0 ≈ X0 • CX01 • X0
  p3 = refl

  p4 : X1 • CX01 ≈ X1 • CX01
  p4 = refl

  p5 : X0 • CX01 • X0 ≈ X1 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CX01 • X0 ≈ X1 • CX01
  proved = p5

module KB0493 where

  p0 : CCX12 • X0 • CX01 • X0 ≈ CCX12 • X1 • CX01
  p0 = by-assoc-and (under (CCX12) (ε) KB0158.proved) Eq.refl Eq.refl

  p1 : CCX12 • X0 • CX01 • X0 ≈ X0 • CCX12 • CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0046.proved) Eq.refl Eq.refl

  p2 : CCX12 • X1 • CX01 ≈ X0 • CCX12 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CCX12 • X1 • CX01 ≈ CCX12 • X1 • CX01
  p3 = refl

  p4 : X0 • CCX12 • CX01 • X0 ≈ X0 • CCX12 • CX01 • X0
  p4 = refl

  p5 : CCX12 • X1 • CX01 ≈ X0 • CCX12 • CX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01
  p6 = sym p5

  proved : X0 • CCX12 • CX01 • X0 ≈ CCX12 • X1 • CX01
  proved = p6

module KB0021 where

  p0 : CX10 • X2 ≈ X2 • CX10
  p0 = bifunct_X_CX_c.proved

  p1 : CX10 • X2 ≈ CX10 • X2
  p1 = refl

  p2 : X2 • CX10 ≈ X2 • CX10
  p2 = refl

  p3 : CX10 • X2 ≈ X2 • CX10
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX10 • X2 ≈ X2 • CX10
  proved = p3

module KB0131 where

  p0 : X2 • CCX12 ≈ CCX12 • CX10 • X2
  p0 = drel130.proved

  p1 : X2 • CCX12 ≈ X2 • CCX12
  p1 = refl

  p2 : CCX12 • CX10 • X2 ≈ CX10 • CCX12 • X2
  p2 = by-assoc-and (under (ε) (X2) KB0032.proved) Eq.refl Eq.refl

  p3 : CCX12 • CX10 • X2 ≈ CX10 • CCX12 • X2
  p3 = trans p2 (refl)

  p4 : X2 • CCX12 ≈ CX10 • CCX12 • X2
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX10 • CCX12 • X2 ≈ X2 • CCX12
  p5 = sym p4

  proved : CX10 • CCX12 • X2 ≈ X2 • CCX12
  proved = p5

module KB0168 where

  p0 : CX10 • CX10 • CCX12 • X2 ≈ CX10 • X2 • CCX12
  p0 = by-assoc-and (under (CX10) (ε) KB0131.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CCX12 • X2 ≈ CCX12 • X2
  p1 = by-assoc-and (under (ε) (CCX12 • X2) KB0005.proved) Eq.refl Eq.refl

  p2 : CX10 • X2 • CCX12 ≈ CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : CX10 • X2 • CCX12 ≈ X2 • CX10 • CCX12
  p3 = by-assoc-and (under (ε) (CCX12) KB0021.proved) Eq.refl Eq.refl

  p4 : CX10 • X2 • CCX12 ≈ X2 • CX10 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • X2 ≈ CCX12 • X2
  p5 = refl

  p6 : X2 • CX10 • CCX12 ≈ CCX12 • X2
  p6 = trans (sym p4) (trans p2 p5)

  proved : X2 • CX10 • CCX12 ≈ CCX12 • X2
  proved = p6

module KB0523 where

  p0 : CX02 • X2 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
  p0 = by-assoc-and (under (CX02) (ε) KB0168.proved) Eq.refl Eq.refl

  p1 : CX02 • X2 • CX10 • CCX12 ≈ X2 • CX02 • CX10 • CCX12
  p1 = by-assoc-and (under (ε) (CX10 • CCX12) KB0033.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • X2 ≈ X2 • CX02 • CX10 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • X2 ≈ CX02 • CCX12 • X2
  p3 = refl

  p4 : X2 • CX02 • CX10 • CCX12 ≈ X2 • CX02 • CX10 • CCX12
  p4 = refl

  p5 : CX02 • CCX12 • X2 ≈ X2 • CX02 • CX10 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X2 • CX02 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
  p6 = sym p5

  proved : X2 • CX02 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
  proved = p6

module KB0047 where

  p0 : X0 • CX10 ≈ CX10 • X0
  p0 = by-assoc-and (axiom r038) Eq.refl Eq.refl

  p1 : X0 • CX10 ≈ X0 • CX10
  p1 = refl

  p2 : CX10 • X0 ≈ CX10 • X0
  p2 = refl

  p3 : X0 • CX10 ≈ CX10 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX10 • X0 ≈ X0 • CX10
  p4 = sym p3

  proved : CX10 • X0 ≈ X0 • CX10
  proved = p4

module KB0115 where

  p0 : X1 • CX10 ≈ CX10 • X0 • X1
  p0 = drel67.proved

  p1 : X1 • CX10 ≈ X1 • CX10
  p1 = refl

  p2 : CX10 • X0 • X1 ≈ X0 • CX10 • X1
  p2 = by-assoc-and (under (ε) (X1) KB0047.proved) Eq.refl Eq.refl

  p3 : CX10 • X0 • X1 ≈ X0 • CX10 • X1
  p3 = trans p2 (refl)

  p4 : X1 • CX10 ≈ X0 • CX10 • X1
  p4 = trans (sym p1) (trans p0 p3)

  p5 : X0 • CX10 • X1 ≈ X1 • CX10
  p5 = sym p4

  proved : X0 • CX10 • X1 ≈ X1 • CX10
  proved = p5

module KB0280 where

  p0 : X0 • CX12 • CCX01 • CX10 ≈ CCX01 • X0 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0121.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX01 • CX10 ≈ X0 • CX10 • CCX01
  p1 = by-assoc-and (under (X0) (ε) KB0118.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX10 ≈ X0 • CX10 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX10 ≈ CCX01 • X0 • CX10
  p3 = refl

  p4 : X0 • CX10 • CCX01 ≈ X0 • CX10 • CCX01
  p4 = refl

  p5 : CCX01 • X0 • CX10 ≈ X0 • CX10 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X0 • CX10 ≈ X0 • CX10 • CCX01
  proved = p5

module KB0603 where

  p0 : CCX01 • X0 • CX10 • X1 ≈ X0 • CX10 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0280.proved) Eq.refl Eq.refl

  p1 : CCX01 • X0 • CX10 • X1 ≈ CCX01 • X1 • CX10
  p1 = by-assoc-and (under (CCX01) (ε) KB0115.proved) Eq.refl Eq.refl

  p2 : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
  p2 = trans (sym p0) p1

  p3 : X0 • CX10 • CCX01 • X1 ≈ X0 • CX10 • CCX01 • X1
  p3 = refl

  p4 : CCX01 • X1 • CX10 ≈ CCX01 • X1 • CX10
  p4 = refl

  p5 : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CX10 • CCX01 • X1 ≈ CCX01 • X1 • CX10
  proved = p5

module KB0694 where

  p0 : X0 • X0 • CX10 • CCX01 • X1 ≈ X0 • CCX01 • X1 • CX10
  p0 = by-assoc-and (under (X0) (ε) KB0603.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • CX10 • CCX01 • X1 ≈ CX10 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CX10 • CCX01 • X1) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • X1 • CX10 ≈ CX10 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : X0 • CCX01 • X1 • CX10 ≈ X0 • CCX01 • X1 • CX10
  p3 = refl

  p4 : CX10 • CCX01 • X1 ≈ CX10 • CCX01 • X1
  p4 = refl

  p5 : X0 • CCX01 • X1 • CX10 ≈ CX10 • CCX01 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CCX01 • X1 • CX10 ≈ CX10 • CCX01 • X1
  proved = p5

module KB0044 where

  p0 : X0 • X1 ≈ X1 • X0
  p0 = X0X1.proved

  p1 : X0 • X1 ≈ X0 • X1
  p1 = refl

  p2 : X1 • X0 ≈ X1 • X0
  p2 = refl

  p3 : X0 • X1 ≈ X1 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : X1 • X0 ≈ X0 • X1
  p4 = sym p3

  proved : X1 • X0 ≈ X0 • X1
  proved = p4

module KB0117 where

  p0 : CX12 • X1 ≈ X1 • X2 • CX12
  p0 = drel70.proved

  p1 : CX12 • X1 ≈ CX12 • X1
  p1 = refl

  p2 : X1 • X2 • CX12 ≈ X1 • X2 • CX12
  p2 = refl

  p3 : CX12 • X1 ≈ X1 • X2 • CX12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : X1 • X2 • CX12 ≈ CX12 • X1
  p4 = sym p3

  proved : X1 • X2 • CX12 ≈ CX12 • X1
  proved = p4

module KB0140 where

  p0 : X0 • CCX01 ≈ CCX01 • CX12 • X0
  p0 = by-assoc-and (axiom r042) Eq.refl Eq.refl

  p1 : X0 • CCX01 ≈ X0 • CCX01
  p1 = refl

  p2 : CCX01 • CX12 • X0 ≈ CX12 • CCX01 • X0
  p2 = by-assoc-and (under (ε) (X0) KB0031.proved) Eq.refl Eq.refl

  p3 : CCX01 • CX12 • X0 ≈ CX12 • CCX01 • X0
  p3 = trans p2 (refl)

  p4 : X0 • CCX01 ≈ CX12 • CCX01 • X0
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX12 • CCX01 • X0 ≈ X0 • CCX01
  p5 = sym p4

  proved : CX12 • CCX01 • X0 ≈ X0 • CCX01
  proved = p5

module KB0783 where

  p0 : X1 • X2 • CX12 • CCX01 • X0 ≈ X1 • X2 • X0 • CCX01
  p0 = by-assoc-and (under (X1 • X2) (ε) KB0140.proved) Eq.refl Eq.refl

  p1 : X1 • X2 • CX12 • CCX01 • X0 ≈ CX12 • X1 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0117.proved) Eq.refl Eq.refl

  p2 : X1 • X2 • X0 • CCX01 ≈ CX12 • X1 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : X1 • X2 • X0 • CCX01 ≈ X1 • X0 • X2 • CCX01
  p3 = by-assoc-and (under (X1) (CCX01) KB0018.proved) Eq.refl Eq.refl

  p4 : X1 • X0 • X2 • CCX01 ≈ X0 • X1 • X2 • CCX01
  p4 = by-assoc-and (under (ε) (X2 • CCX01) KB0044.proved) Eq.refl Eq.refl

  p5 : X1 • X2 • X0 • CCX01 ≈ X0 • X1 • X2 • CCX01
  p5 = trans p3 (trans p4 (refl))

  p6 : CX12 • X1 • CCX01 • X0 ≈ CX12 • X1 • CCX01 • X0
  p6 = refl

  p7 : X0 • X1 • X2 • CCX01 ≈ CX12 • X1 • CCX01 • X0
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX12 • X1 • CCX01 • X0 ≈ X0 • X1 • X2 • CCX01
  p8 = sym p7

  proved : CX12 • X1 • CCX01 • X0 ≈ X0 • X1 • X2 • CCX01
  proved = p8

module KB0825 where

  p0 : X0 • X1 • CX01 • CCX01 • CX01 ≈ X0 • X1 • CX02 • CCX01
  p0 = by-assoc-and (under (X0 • X1) (ε) KB0157.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX01 • CCX01 • CX01 ≈ CX01 • X0 • CCX01 • CX01
  p1 = by-assoc-and (under (ε) (CCX01 • CX01) KB0124.proved) Eq.refl Eq.refl

  p2 : X0 • X1 • CX02 • CCX01 ≈ CX01 • X0 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : X0 • X1 • CX02 • CCX01 ≈ X0 • CCX01 • X1
  p3 = by-assoc-and (under (X0) (ε) KB0151.proved) Eq.refl Eq.refl

  p4 : X0 • X1 • CX02 • CCX01 ≈ X0 • CCX01 • X1
  p4 = trans p3 (refl)

  p5 : CX01 • X0 • CCX01 • CX01 ≈ CX01 • X0 • CCX01 • CX01
  p5 = refl

  p6 : X0 • CCX01 • X1 ≈ CX01 • X0 • CCX01 • CX01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX01 • X0 • CCX01 • CX01 ≈ X0 • CCX01 • X1
  p7 = sym p6

  proved : CX01 • X0 • CCX01 • CX01 ≈ X0 • CCX01 • X1
  proved = p7

module KB0190 where

  p0 : CX01 • CX01 • X0 • CX01 ≈ CX01 • X0 • X1
  p0 = by-assoc-and (under (CX01) (ε) KB0159.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • X0 • CX01 ≈ X0 • CX01
  p1 = by-assoc-and (under (ε) (X0 • CX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • X1 ≈ X0 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • X1 ≈ CX01 • X0 • X1
  p3 = refl

  p4 : X0 • CX01 ≈ X0 • CX01
  p4 = refl

  p5 : CX01 • X0 • X1 ≈ X0 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • X1 ≈ X0 • CX01
  proved = p5

module KB0910 where

  p0 : CX01 • X0 • X1 • CX12 • X1 ≈ X0 • CX01 • CX12 • X1
  p0 = by-assoc-and (under (ε) (CX12 • X1) KB0190.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • X1 • CX12 • X1 ≈ CX01 • X0 • X2 • CX12
  p1 = by-assoc-and (under (CX01 • X0) (ε) KB0144.proved) Eq.refl Eq.refl

  p2 : X0 • CX01 • CX12 • X1 ≈ CX01 • X0 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : X0 • CX01 • CX12 • X1 ≈ X0 • CX01 • CX12 • X1
  p3 = refl

  p4 : CX01 • X0 • X2 • CX12 ≈ X2 • CX01 • X0 • CX12
  p4 = by-assoc-and (under (ε) (CX12) KB0221.proved) Eq.refl Eq.refl

  p5 : CX01 • X0 • X2 • CX12 ≈ X2 • CX01 • X0 • CX12
  p5 = trans p4 (refl)

  p6 : X0 • CX01 • CX12 • X1 ≈ X2 • CX01 • X0 • CX12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X2 • CX01 • X0 • CX12 ≈ X0 • CX01 • CX12 • X1
  p7 = sym p6

  proved : X2 • CX01 • X0 • CX12 ≈ X0 • CX01 • CX12 • X1
  proved = p7

module KB0340 where

  p0 : CCX02 • CCX02 • CCX12 • CCX02 ≈ CCX02 • CX01 • CCX12 • CX01
  p0 = by-assoc-and (under (CCX02) (ε) KB0216.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX01 • CCX12 • CX01 ≈ CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX01 • CCX12 • CX01 ≈ CX01 • CCX02 • CCX12 • CX01
  p3 = by-assoc-and (under (ε) (CCX12 • CX01) KB0038.proved) Eq.refl Eq.refl

  p4 : CCX02 • CX01 • CCX12 • CX01 ≈ CX01 • CCX02 • CCX12 • CX01
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX02 ≈ CCX12 • CCX02
  p5 = refl

  p6 : CX01 • CCX02 • CCX12 • CX01 ≈ CCX12 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX01 • CCX02 • CCX12 • CX01 ≈ CCX12 • CCX02
  proved = p6

module KB1367 where

  p0 : CX02 • CX01 • CCX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX02) (ε) KB0340.proved) Eq.refl Eq.refl

  p1 : CX02 • CX01 • CCX02 • CCX12 • CX01 ≈ CX01 • CX02 • CCX02 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CX01) KB0025.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CCX02 ≈ CX01 • CX02 • CCX02 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CCX02
  p3 = refl

  p4 : CX01 • CX02 • CCX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CX01
  p4 = by-assoc-and (under (ε) (CCX12 • CX01) KB0149.proved) Eq.refl Eq.refl

  p5 : CX01 • CX02 • CCX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CX01
  p5 = trans p4 (refl)

  p6 : CX02 • CCX12 • CCX02 ≈ CCX02 • CX02 • CCX12 • CX01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
  p7 = sym p6

  proved : CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CCX02
  proved = p7

module KB1368 where

  p0 : CCX02 • CCX02 • CX02 • CCX12 • CX01 ≈ CCX02 • CX02 • CCX12 • CCX02
  p0 = by-assoc-and (under (CCX02) (ε) KB1367.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX12 • CX01) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX02 • CCX12 • CCX02 ≈ CCX02 • CX02 • CCX12 • CCX02
  p3 = refl

  p4 : CX02 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01
  p4 = refl

  p5 : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX02 • CCX12 • CCX02 ≈ CX02 • CCX12 • CX01
  proved = p5

module KB0087 where

  p0 : SWAP01 ≈ CX01 • CX10 • CX01
  p0 = by-assoc-and (axiom r013) Eq.refl Eq.refl

  p1 : SWAP01 ≈ SWAP01
  p1 = refl

  p2 : CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01
  p2 = refl

  p3 : SWAP01 ≈ CX01 • CX10 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX01 • CX10 • CX01 ≈ SWAP01
  p4 = sym p3

  proved : CX01 • CX10 • CX01 ≈ SWAP01
  proved = p4

module KB0088 where

  p0 : CX01 • CX01 • CX10 • CX01 ≈ CX01 • SWAP01
  p0 = by-assoc-and (under (CX01) (ε) KB0087.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CX10 • CX01 ≈ CX10 • CX01
  p1 = by-assoc-and (under (ε) (CX10 • CX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • SWAP01 ≈ CX10 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • SWAP01 ≈ CX01 • SWAP01
  p3 = refl

  p4 : CX10 • CX01 ≈ CX10 • CX01
  p4 = refl

  p5 : CX01 • SWAP01 ≈ CX10 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CX01 ≈ CX01 • SWAP01
  p6 = sym p5

  proved : CX10 • CX01 ≈ CX01 • SWAP01
  proved = p6

module KB0154 where

  p0 : X2 • X2 • CX01 • CCX02 ≈ X2 • CCX02 • X2
  p0 = by-assoc-and (under (X2) (ε) KB0122.proved) Eq.refl Eq.refl

  p1 : X2 • X2 • CX01 • CCX02 ≈ CX01 • CCX02
  p1 = by-assoc-and (under (ε) (CX01 • CCX02) KB0004.proved) Eq.refl Eq.refl

  p2 : X2 • CCX02 • X2 ≈ CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : X2 • CCX02 • X2 ≈ X2 • CCX02 • X2
  p3 = refl

  p4 : CX01 • CCX02 ≈ CX01 • CCX02
  p4 = refl

  p5 : X2 • CCX02 • X2 ≈ CX01 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CCX02 • X2 ≈ CX01 • CCX02
  proved = p5

module KB0342 where

  p0 : CX01 • CCX02 • CCX12 • CX01 • CX01 ≈ CCX12 • CCX02 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0340.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • CCX12 • CX01 • CX01 ≈ CX01 • CCX02 • CCX12
  p1 = by-assoc-and (under (CX01 • CCX02 • CCX12) (ε) KB0013.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX02 • CX01 ≈ CX01 • CCX02 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX02 • CX01 ≈ CCX12 • CX01 • CCX02
  p3 = by-assoc-and (under (CCX12) (ε) KB0038.proved) Eq.refl Eq.refl

  p4 : CCX12 • CCX02 • CX01 ≈ CCX12 • CX01 • CCX02
  p4 = trans p3 (refl)

  p5 : CX01 • CCX02 • CCX12 ≈ CX01 • CCX02 • CCX12
  p5 = refl

  p6 : CCX12 • CX01 • CCX02 ≈ CX01 • CCX02 • CCX12
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX12 • CX01 • CCX02 ≈ CX01 • CCX02 • CCX12
  proved = p6

module KB0821 where

  p0 : CX10 • CCX12 • X2 • CCX02 • X2 ≈ CX10 • CCX12 • CX01 • CCX02
  p0 = by-assoc-and (under (CX10 • CCX12) (ε) KB0154.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • X2 • CCX02 • X2 ≈ X2 • CCX12 • CCX02 • X2
  p1 = by-assoc-and (under (ε) (CCX02 • X2) KB0131.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CX01 • CCX02 ≈ X2 • CCX12 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CX01 • CCX02 ≈ CX10 • CX01 • CCX02 • CCX12
  p3 = by-assoc-and (under (CX10) (ε) KB0342.proved) Eq.refl Eq.refl

  p4 : CX10 • CX01 • CCX02 • CCX12 ≈ CX01 • SWAP01 • CCX02 • CCX12
  p4 = by-assoc-and (under (ε) (CCX02 • CCX12) KB0088.proved) Eq.refl Eq.refl

  p5 : CX01 • SWAP01 • CCX02 • CCX12 ≈ CX01 • CCX12 • SWAP01 • CCX12
  p5 = by-assoc-and (under (CX01) (CCX12) KB0090.proved) Eq.refl Eq.refl

  p6 : CX01 • CCX12 • SWAP01 • CCX12 ≈ CX01 • CCX12 • CCX02 • SWAP01
  p6 = by-assoc-and (under (CX01 • CCX12) (ε) KB0091.proved) Eq.refl Eq.refl

  p7 : CX10 • CCX12 • CX01 • CCX02 ≈ CX01 • CCX12 • CCX02 • SWAP01
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  p8 : X2 • CCX12 • CCX02 • X2 ≈ X2 • CCX12 • CCX02 • X2
  p8 = refl

  p9 : CX01 • CCX12 • CCX02 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2
  p9 = trans (sym p7) (trans p2 p8)

  proved : CX01 • CCX12 • CCX02 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2
  proved = p9

module KB1378 where

  p0 : CX01 • CCX12 • CCX02 • SWAP01 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0821.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX12 • CCX02 • SWAP01 • SWAP01 ≈ CX01 • CCX12 • CCX02
  p1 = by-assoc-and (under (CX01 • CCX12 • CCX02) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CCX12 • CCX02 • X2 • SWAP01
  p3 = refl

  p4 : CX01 • CCX12 • CCX02 ≈ CX01 • CCX12 • CCX02
  p4 = refl

  p5 : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CX01 • CCX12 • CCX02
  proved = p5

module KB1379 where

  p0 : X2 • X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (X2) (ε) KB1378.proved) Eq.refl Eq.refl

  p1 : X2 • X2 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • CCX02 • X2 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX12 • CCX02 • X2 • SWAP01) KB0004.proved) Eq.refl Eq.refl

  p2 : X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • X2 • SWAP01
  p2 = trans (sym p0) p1

  p3 : X2 • CX01 • CCX12 • CCX02 ≈ X2 • CX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • CCX02 • X2 • SWAP01
  p4 = refl

  p5 : X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • X2 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX12 • CCX02 • X2 • SWAP01 ≈ X2 • CX01 • CCX12 • CCX02
  proved = p6

module KB1419 where

  p0 : CCX12 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX12 • X2 • CX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (CCX12) (ε) KB1379.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX12 • CCX02 • X2 • SWAP01 ≈ CCX02 • X2 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX02 • X2 • SWAP01) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX12 • X2 • CX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX02 • X2 • SWAP01 ≈ CCX02 • X2 • SWAP01
  p4 = refl

  p5 : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • X2 • CX01 • CCX12 • CCX02 ≈ CCX02 • X2 • SWAP01
  proved = p5

module KB0152 where

  p0 : X0 • CX12 • CCX01 • CCX01 ≈ CCX01 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0121.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX01 • CCX01 ≈ X0 • CX12
  p1 = by-assoc-and (under (X0 • CX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CCX01 ≈ X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CCX01
  p3 = refl

  p4 : X0 • CX12 ≈ X0 • CX12
  p4 = refl

  p5 : CCX01 • X0 • CCX01 ≈ X0 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X0 • CCX01 ≈ X0 • CX12
  proved = p5

module KB0184 where

  p0 : CX10 • CX12 • CCX01 • CCX01 ≈ CCX01 • CX10 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0147.proved) Eq.refl Eq.refl

  p1 : CX10 • CX12 • CCX01 • CCX01 ≈ CX10 • CX12
  p1 = by-assoc-and (under (CX10 • CX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX10 • CCX01 ≈ CX10 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX10 • CCX01 ≈ CCX01 • CX10 • CCX01
  p3 = refl

  p4 : CX10 • CX12 ≈ CX10 • CX12
  p4 = refl

  p5 : CCX01 • CX10 • CCX01 ≈ CX10 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX10 • CCX01 ≈ CX10 • CX12
  proved = p5

module KB0202 where

  p0 : CCX01 • CCX01 • CX10 • CCX01 ≈ CCX01 • CX10 • CX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0184.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CX10 • CCX01 ≈ CX10 • CCX01
  p1 = by-assoc-and (under (ε) (CX10 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX10 • CX12 ≈ CX10 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX10 • CX12 ≈ CCX01 • CX10 • CX12
  p3 = refl

  p4 : CX10 • CCX01 ≈ CX10 • CCX01
  p4 = refl

  p5 : CCX01 • CX10 • CX12 ≈ CX10 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX10 • CX12 ≈ CX10 • CCX01
  proved = p5

module KB0293 where

  p0 : CCX01 • CX10 • CX12 • CCX12 ≈ CX10 • CCX01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0202.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX10 • CX12 • CCX12 ≈ CCX01 • CCX12 • CX12
  p1 = by-assoc-and (under (CCX01) (ε) KB0180.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CCX12 ≈ CX10 • CCX01 • CCX12
  p3 = refl

  p4 : CCX01 • CCX12 • CX12 ≈ CCX01 • CCX12 • CX12
  p4 = refl

  p5 : CX10 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX12 • CX12 ≈ CX10 • CCX01 • CCX12
  p6 = sym p5

  proved : CCX01 • CCX12 • CX12 ≈ CX10 • CCX01 • CCX12
  proved = p6

module KB0366 where

  p0 : CX12 • CCX01 • CX10 • X0 ≈ CX10 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0118.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • CX10 • X0 ≈ CX12 • CCX01 • X0 • CX10
  p1 = by-assoc-and (under (CX12 • CCX01) (ε) KB0047.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • X0 ≈ CX10 • CCX01 • X0
  p3 = refl

  p4 : CX12 • CCX01 • X0 • CX10 ≈ X0 • CCX01 • CX10
  p4 = by-assoc-and (under (ε) (CX10) KB0140.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX01 • X0 • CX10 ≈ X0 • CCX01 • CX10
  p5 = trans p4 (refl)

  p6 : CX10 • CCX01 • X0 ≈ X0 • CCX01 • CX10
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX10 • CCX01 • X0 ≈ X0 • CCX01 • CX10
  proved = p6

module KB1184 where

  p0 : CCX01 • CCX12 • CX12 • X0 ≈ CX10 • CCX01 • CCX12 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0293.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CX12 • X0 ≈ CCX01 • CCX12 • X0 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0045.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CCX12 • X0 ≈ CCX01 • CCX12 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CCX12 • X0 ≈ CX10 • CCX01 • X0 • CCX12
  p3 = by-assoc-and (under (CX10 • CCX01) (ε) KB0046.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX01 • X0 • CCX12 ≈ X0 • CCX01 • CX10 • CCX12
  p4 = by-assoc-and (under (ε) (CCX12) KB0366.proved) Eq.refl Eq.refl

  p5 : CX10 • CCX01 • CCX12 • X0 ≈ X0 • CCX01 • CX10 • CCX12
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
  p6 = by-assoc-and (under (CCX01) (CX12) KB0046.proved) Eq.refl Eq.refl

  p7 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
  p7 = trans p6 (refl)

  p8 : X0 • CCX01 • CX10 • CCX12 ≈ CCX01 • X0 • CCX12 • CX12
  p8 = trans (sym p5) (trans p2 p7)

  p9 : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
  p9 = sym p8

  proved : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
  proved = p9

module KB1423 where

  p0 : CCX01 • CCX12 • CCX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX02 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (X0 • CCX01) KB0211.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX01 • X0 • CCX01 ≈ CCX01 • CCX12 • X0 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0152.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ CCX01 • CCX12 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ CX02 • CCX12 • CX02 • X0 • CCX01
  p3 = refl

  p4 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
  p4 = by-assoc-and (under (CCX01) (CX12) KB0046.proved) Eq.refl Eq.refl

  p5 : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
  p5 = by-assoc-and (under (ε) (ε) KB1184.proved) Eq.refl Eq.refl

  p6 : CCX01 • CCX12 • X0 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
  p6 = trans p4 (trans p5 (refl))

  p7 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CX10 • CCX12
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CX10 • CCX12
  proved = p7
