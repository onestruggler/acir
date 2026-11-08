{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B006 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r006 ; r008 ; r015 ; r033 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0006 ; module KB0008 ; module KB0009 ; module KB0011 ; module KB0013 ; module KB0014 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0033 ; module KB0037 ; module KB0040 ; module KB0120 ; module KB0136 ; module KB0151 ; module KB0153 ; module KB0160 ; module KB0164 ; module KB0166)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0002 ; module KB0020 ; module KB0022 ; module KB0025 ; module KB0030 ; module KB0084 ; module KB0086 ; module KB0098 ; module KB0103 ; module KB0123 ; module KB0128 ; module KB0176 ; module KB0322)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0018 ; module KB0045 ; module KB0062 ; module KB0063)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0044 ; module KB0047 ; module KB0131 ; module KB0152 ; module KB0168)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_f ; module drel131 ; module drel154 ; module elim_SWAP12)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel134 ; module symmetry_CX_j)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_SWAP_a ; module bifunct_X_SWAP_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module drel155 ; module symmetry_CCX_f ; module symmetry_CCX_g)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B007 using (module drel79)

module decodeCX12 where

  p0 : CX12 ≈ CX12
  p0 = refl

  p1 : X0 • CCX01 • X0 • CCX01 ≈ CX12 • CCX01 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01) KB0153.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • CCX01 ≈ CX12
  p2 = by-assoc-and (under (CX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p3 : X0 • CCX01 • X0 • CCX01 ≈ CX12
  p3 = trans p1 (trans p2 (refl))

  proved : CX12 ≈ X0 • CCX01 • X0 • CCX01
  proved = trans p0 (sym p3)

module KB0015 where

  p0 : X0 • SWAP12 ≈ SWAP12 • X0
  p0 = bifunct_X_SWAP_a.proved

  p1 : X0 • SWAP12 ≈ X0 • SWAP12
  p1 = refl

  p2 : SWAP12 • X0 ≈ SWAP12 • X0
  p2 = refl

  p3 : X0 • SWAP12 ≈ SWAP12 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • X0 ≈ X0 • SWAP12
  p4 = sym p3

  proved : SWAP12 • X0 ≈ X0 • SWAP12
  proved = p4

module KB0017 where

  p0 : X1 • SWAP02 ≈ SWAP02 • X1
  p0 = bifunct_X_SWAP_c.proved

  p1 : X1 • SWAP02 ≈ X1 • SWAP02
  p1 = refl

  p2 : SWAP02 • X1 ≈ SWAP02 • X1
  p2 = refl

  p3 : X1 • SWAP02 ≈ SWAP02 • X1
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • X1 ≈ X1 • SWAP02
  p4 = sym p3

  proved : SWAP02 • X1 ≈ X1 • SWAP02
  proved = p4

module KB0041 where

  p0 : CX12 • CX21 ≈ CX21 • SWAP12
  p0 = drel154.proved

  p1 : CX12 • CX21 ≈ CX12 • CX21
  p1 = refl

  p2 : CX21 • SWAP12 ≈ CX21 • SWAP12
  p2 = refl

  p3 : CX12 • CX21 ≈ CX21 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX21 • SWAP12 ≈ CX12 • CX21
  p4 = sym p3

  proved : CX21 • SWAP12 ≈ CX12 • CX21
  proved = p4

module KB0075 where

  p0 : CCX02 ≈ SWAP02 • CCX02 • SWAP02
  p0 = symmetry_CCX_f.proved

  p1 : CCX02 ≈ CCX02
  p1 = refl

  p2 : SWAP02 • CCX02 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02
  p2 = refl

  p3 : CCX02 ≈ SWAP02 • CCX02 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • CCX02 • SWAP02 ≈ CCX02
  p4 = sym p3

  proved : SWAP02 • CCX02 • SWAP02 ≈ CCX02
  proved = p4

module KB0076 where

  p0 : SWAP02 • SWAP02 • CCX02 • SWAP02 ≈ SWAP02 • CCX02
  p0 = by-assoc-and (under (SWAP02) (ε) KB0075.proved) Eq.refl Eq.refl

  p1 : SWAP02 • SWAP02 • CCX02 • SWAP02 ≈ CCX02 • SWAP02
  p1 = by-assoc-and (under (ε) (CCX02 • SWAP02) KB0002.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CCX02 ≈ CCX02 • SWAP02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CCX02 ≈ SWAP02 • CCX02
  p3 = refl

  p4 : CCX02 • SWAP02 ≈ CCX02 • SWAP02
  p4 = refl

  p5 : SWAP02 • CCX02 ≈ CCX02 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • CCX02 ≈ CCX02 • SWAP02
  proved = p5

module KB0001 where

  p0 : SWAP12 • SWAP12 ≈ ε
  p0 = elim_SWAP12.proved

  p1 : SWAP12 • SWAP12 ≈ SWAP12 • SWAP12
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : SWAP12 • SWAP12 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : SWAP12 • SWAP12 ≈ ε
  proved = p3

module KB0077 where

  p0 : CCX12 ≈ SWAP12 • CCX12 • SWAP12
  p0 = symmetry_CCX_g.proved

  p1 : CCX12 ≈ CCX12
  p1 = refl

  p2 : SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12
  p2 = refl

  p3 : CCX12 ≈ SWAP12 • CCX12 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • CCX12 • SWAP12 ≈ CCX12
  p4 = sym p3

  proved : SWAP12 • CCX12 • SWAP12 ≈ CCX12
  proved = p4

module KB0078 where

  p0 : SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12
  p0 = by-assoc-and (under (SWAP12) (ε) KB0077.proved) Eq.refl Eq.refl

  p1 : SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ CCX12 • SWAP12
  p1 = by-assoc-and (under (ε) (CCX12 • SWAP12) KB0001.proved) Eq.refl Eq.refl

  p2 : SWAP12 • CCX12 ≈ CCX12 • SWAP12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • CCX12 ≈ SWAP12 • CCX12
  p3 = refl

  p4 : CCX12 • SWAP12 ≈ CCX12 • SWAP12
  p4 = refl

  p5 : SWAP12 • CCX12 ≈ CCX12 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP12 • CCX12 ≈ CCX12 • SWAP12
  proved = p5

module KB0079 where

  p0 : SWAP12 ≈ CX12 • CX21 • CX12
  p0 = by-assoc-and (axiom r008) Eq.refl Eq.refl

  p1 : SWAP12 ≈ SWAP12
  p1 = refl

  p2 : CX12 • CX21 • CX12 ≈ CX12 • CX21 • CX12
  p2 = refl

  p3 : SWAP12 ≈ CX12 • CX21 • CX12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX12 • CX21 • CX12 ≈ SWAP12
  p4 = sym p3

  proved : CX12 • CX21 • CX12 ≈ SWAP12
  proved = p4

module KB0080 where

  p0 : CX12 • CX12 • CX21 • CX12 ≈ CX12 • SWAP12
  p0 = by-assoc-and (under (CX12) (ε) KB0079.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CX21 • CX12 ≈ CX21 • CX12
  p1 = by-assoc-and (under (ε) (CX21 • CX12) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • SWAP12 ≈ CX21 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • SWAP12 ≈ CX12 • SWAP12
  p3 = refl

  p4 : CX21 • CX12 ≈ CX21 • CX12
  p4 = refl

  p5 : CX12 • SWAP12 ≈ CX21 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX21 • CX12 ≈ CX12 • SWAP12
  p6 = sym p5

  proved : CX21 • CX12 ≈ CX12 • SWAP12
  proved = p6

module KB0092 where

  p0 : X2 ≈ SWAP02 • X0 • SWAP02
  p0 = by-assoc-and (axiom r015) Eq.refl Eq.refl

  p1 : X2 ≈ X2
  p1 = refl

  p2 : SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • SWAP02
  p2 = refl

  p3 : X2 ≈ SWAP02 • X0 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • X0 • SWAP02 ≈ X2
  p4 = sym p3

  proved : SWAP02 • X0 • SWAP02 ≈ X2
  proved = p4

module KB0093 where

  p0 : SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X2
  p0 = by-assoc-and (under (SWAP02) (ε) KB0092.proved) Eq.refl Eq.refl

  p1 : SWAP02 • SWAP02 • X0 • SWAP02 ≈ X0 • SWAP02
  p1 = by-assoc-and (under (ε) (X0 • SWAP02) KB0002.proved) Eq.refl Eq.refl

  p2 : SWAP02 • X2 ≈ X0 • SWAP02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • X2 ≈ SWAP02 • X2
  p3 = refl

  p4 : X0 • SWAP02 ≈ X0 • SWAP02
  p4 = refl

  p5 : SWAP02 • X2 ≈ X0 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • X2 ≈ X0 • SWAP02
  proved = p5

module KB0104 where

  p0 : SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX01
  p0 = by-assoc-and (under (SWAP02) (ε) KB0103.proved) Eq.refl Eq.refl

  p1 : SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ CCX12 • SWAP02
  p1 = by-assoc-and (under (ε) (CCX12 • SWAP02) KB0002.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CCX01 ≈ CCX12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CCX01 ≈ SWAP02 • CCX01
  p3 = refl

  p4 : CCX12 • SWAP02 ≈ CCX12 • SWAP02
  p4 = refl

  p5 : SWAP02 • CCX01 ≈ CCX12 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • CCX01 ≈ CCX12 • SWAP02
  proved = p5

module KB0106 where

  p0 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
  p0 = by-assoc-and (axiom r033) Eq.refl Eq.refl

  p1 : CCX01 ≈ CCX01
  p1 = refl

  p2 : SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • SWAP12
  p2 = refl

  p3 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • CCX02 • SWAP12 ≈ CCX01
  p4 = sym p3

  proved : SWAP12 • CCX02 • SWAP12 ≈ CCX01
  proved = p4

module KB0107 where

  p0 : SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CCX01
  p0 = by-assoc-and (under (SWAP12) (ε) KB0106.proved) Eq.refl Eq.refl

  p1 : SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ CCX02 • SWAP12
  p1 = by-assoc-and (under (ε) (CCX02 • SWAP12) KB0001.proved) Eq.refl Eq.refl

  p2 : SWAP12 • CCX01 ≈ CCX02 • SWAP12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • CCX01 ≈ SWAP12 • CCX01
  p3 = refl

  p4 : CCX02 • SWAP12 ≈ CCX02 • SWAP12
  p4 = refl

  p5 : SWAP12 • CCX01 ≈ CCX02 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP12 • CCX01 ≈ CCX02 • SWAP12
  proved = p5

module KB0108 where

  p0 : SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ CCX01 • SWAP12
  p0 = by-assoc-and (under (ε) (SWAP12) KB0106.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CCX02
  p1 = by-assoc-and (under (SWAP12 • CCX02) (ε) KB0001.proved) Eq.refl Eq.refl

  p2 : CCX01 • SWAP12 ≈ SWAP12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • SWAP12 ≈ CCX01 • SWAP12
  p3 = refl

  p4 : SWAP12 • CCX02 ≈ SWAP12 • CCX02
  p4 = refl

  p5 : CCX01 • SWAP12 ≈ SWAP12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP12 • CCX02 ≈ CCX01 • SWAP12
  p6 = sym p5

  proved : SWAP12 • CCX02 ≈ CCX01 • SWAP12
  proved = p6

module KB0223 where

  p0 : CCX01 • X2 • X0 ≈ X2 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0029.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • X0 ≈ CCX01 • X0 • X2
  p1 = by-assoc-and (under (CCX01) (ε) KB0018.proved) Eq.refl Eq.refl

  p2 : X2 • CCX01 • X0 ≈ CCX01 • X0 • X2
  p2 = trans (sym p0) p1

  p3 : X2 • CCX01 • X0 ≈ X2 • CCX01 • X0
  p3 = refl

  p4 : CCX01 • X0 • X2 ≈ CCX01 • X0 • X2
  p4 = refl

  p5 : X2 • CCX01 • X0 ≈ CCX01 • X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • X0 • X2 ≈ X2 • CCX01 • X0
  p6 = sym p5

  proved : CCX01 • X0 • X2 ≈ X2 • CCX01 • X0
  proved = p6

module KB0300 where

  p0 : CX21 ≈ CX20 • CX01 • CX20 • CX01
  p0 = by-assoc-and (axiom r006) Eq.refl Eq.refl

  p1 : CX21 ≈ CX21
  p1 = refl

  p2 : CX20 • CX01 • CX20 • CX01 ≈ CX20 • CX01 • CX20 • CX01
  p2 = refl

  p3 : CX21 ≈ CX20 • CX01 • CX20 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX20 • CX01 • CX20 • CX01 ≈ CX21
  p4 = sym p3

  proved : CX20 • CX01 • CX20 • CX01 ≈ CX21
  proved = p4

module KB0301 where

  p0 : CX20 • CX20 • CX01 • CX20 • CX01 ≈ CX20 • CX21
  p0 = by-assoc-and (under (CX20) (ε) KB0300.proved) Eq.refl Eq.refl

  p1 : CX20 • CX20 • CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX01
  p1 = by-assoc-and (under (ε) (CX01 • CX20 • CX01) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • CX21 ≈ CX01 • CX20 • CX01
  p2 = trans (sym p0) p1

  p3 : CX20 • CX21 ≈ CX20 • CX21
  p3 = refl

  p4 : CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX01
  p4 = refl

  p5 : CX20 • CX21 ≈ CX01 • CX20 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • CX20 • CX01 ≈ CX20 • CX21
  p6 = sym p5

  proved : CX01 • CX20 • CX01 ≈ CX20 • CX21
  proved = p6

module KB0303 where

  p0 : CX01 • CX01 • CX20 • CX01 ≈ CX01 • CX20 • CX21
  p0 = by-assoc-and (under (CX01) (ε) KB0301.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CX20 • CX01 ≈ CX20 • CX01
  p1 = by-assoc-and (under (ε) (CX20 • CX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CX20 • CX21 ≈ CX20 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX20 • CX21 ≈ CX01 • CX20 • CX21
  p3 = refl

  p4 : CX20 • CX01 ≈ CX20 • CX01
  p4 = refl

  p5 : CX01 • CX20 • CX21 ≈ CX20 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CX20 • CX21 ≈ CX20 • CX01
  proved = p5

module KB0305 where

  p0 : CX01 • CX20 • CX21 • CCX02 ≈ CX20 • CX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0303.proved) Eq.refl Eq.refl

  p1 : CX01 • CX20 • CX21 • CCX02 ≈ CX01 • CCX02 • CX20
  p1 = by-assoc-and (under (CX01) (ε) KB0176.proved) Eq.refl Eq.refl

  p2 : CX20 • CX01 • CCX02 ≈ CX01 • CCX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • CX01 • CCX02 ≈ CX20 • CX01 • CCX02
  p3 = refl

  p4 : CX01 • CCX02 • CX20 ≈ CX01 • CCX02 • CX20
  p4 = refl

  p5 : CX20 • CX01 • CCX02 ≈ CX01 • CCX02 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CX01 • CCX02 ≈ CX01 • CCX02 • CX20
  proved = p5

module KB0070 where

  p0 : CX20 ≈ SWAP12 • CX10 • SWAP12
  p0 = symmetry_CX_j.proved

  p1 : CX20 ≈ CX20
  p1 = refl

  p2 : SWAP12 • CX10 • SWAP12 ≈ SWAP12 • CX10 • SWAP12
  p2 = refl

  p3 : CX20 ≈ SWAP12 • CX10 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • CX10 • SWAP12 ≈ CX20
  p4 = sym p3

  proved : SWAP12 • CX10 • SWAP12 ≈ CX20
  proved = p4

module KB0072 where

  p0 : SWAP12 • CX10 • SWAP12 • SWAP12 ≈ CX20 • SWAP12
  p0 = by-assoc-and (under (ε) (SWAP12) KB0070.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX10 • SWAP12 • SWAP12 ≈ SWAP12 • CX10
  p1 = by-assoc-and (under (SWAP12 • CX10) (ε) KB0001.proved) Eq.refl Eq.refl

  p2 : CX20 • SWAP12 ≈ SWAP12 • CX10
  p2 = trans (sym p0) p1

  p3 : CX20 • SWAP12 ≈ CX20 • SWAP12
  p3 = refl

  p4 : SWAP12 • CX10 ≈ SWAP12 • CX10
  p4 = refl

  p5 : CX20 • SWAP12 ≈ SWAP12 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP12 • CX10 ≈ CX20 • SWAP12
  p6 = sym p5

  proved : SWAP12 • CX10 ≈ CX20 • SWAP12
  proved = p6

module KB0247 where

  p0 : SWAP12 • CX10 • X0 ≈ CX20 • SWAP12 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0072.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX10 • X0 ≈ SWAP12 • X0 • CX10
  p1 = by-assoc-and (under (SWAP12) (ε) KB0047.proved) Eq.refl Eq.refl

  p2 : CX20 • SWAP12 • X0 ≈ SWAP12 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CX20 • SWAP12 • X0 ≈ CX20 • X0 • SWAP12
  p3 = by-assoc-and (under (CX20) (ε) KB0015.proved) Eq.refl Eq.refl

  p4 : CX20 • SWAP12 • X0 ≈ CX20 • X0 • SWAP12
  p4 = trans p3 (refl)

  p5 : SWAP12 • X0 • CX10 ≈ X0 • SWAP12 • CX10
  p5 = by-assoc-and (under (ε) (CX10) KB0015.proved) Eq.refl Eq.refl

  p6 : X0 • SWAP12 • CX10 ≈ X0 • CX20 • SWAP12
  p6 = by-assoc-and (under (X0) (ε) KB0072.proved) Eq.refl Eq.refl

  p7 : SWAP12 • X0 • CX10 ≈ X0 • CX20 • SWAP12
  p7 = trans p5 (trans p6 (refl))

  p8 : CX20 • X0 • SWAP12 ≈ X0 • CX20 • SWAP12
  p8 = trans (sym p4) (trans p2 p7)

  proved : CX20 • X0 • SWAP12 ≈ X0 • CX20 • SWAP12
  proved = p8

module KB0309 where

  p0 : SWAP12 • CX10 • SWAP12 • X0 ≈ CX20 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0070.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CX10 • SWAP12 • X0 ≈ SWAP12 • CX10 • X0 • SWAP12
  p1 = by-assoc-and (under (SWAP12 • CX10) (ε) KB0015.proved) Eq.refl Eq.refl

  p2 : CX20 • X0 ≈ SWAP12 • CX10 • X0 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CX20 • X0 ≈ CX20 • X0
  p3 = refl

  p4 : SWAP12 • CX10 • X0 • SWAP12 ≈ CX20 • SWAP12 • X0 • SWAP12
  p4 = by-assoc-and (under (ε) (X0 • SWAP12) KB0072.proved) Eq.refl Eq.refl

  p5 : CX20 • SWAP12 • X0 • SWAP12 ≈ CX20 • X0 • SWAP12 • SWAP12
  p5 = by-assoc-and (under (CX20) (SWAP12) KB0015.proved) Eq.refl Eq.refl

  p6 : CX20 • X0 • SWAP12 • SWAP12 ≈ X0 • CX20 • SWAP12 • SWAP12
  p6 = by-assoc-and (under (ε) (SWAP12) KB0247.proved) Eq.refl Eq.refl

  p7 : X0 • CX20 • SWAP12 • SWAP12 ≈ X0 • CX20
  p7 = by-assoc-and (under (X0 • CX20) (ε) KB0001.proved) Eq.refl Eq.refl

  p8 : SWAP12 • CX10 • X0 • SWAP12 ≈ X0 • CX20
  p8 = trans p4 (trans p5 (trans p6 (trans p7 (refl))))

  p9 : CX20 • X0 ≈ X0 • CX20
  p9 = trans (sym p3) (trans p2 p8)

  proved : CX20 • X0 ≈ X0 • CX20
  proved = p9

module KB0260 where

  p0 : SWAP02 • CX02 • X2 ≈ CX02 • CX20 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0086.proved) Eq.refl Eq.refl

  p1 : SWAP02 • CX02 • X2 ≈ SWAP02 • X2 • CX02
  p1 = by-assoc-and (under (SWAP02) (ε) KB0033.proved) Eq.refl Eq.refl

  p2 : CX02 • CX20 • X2 ≈ SWAP02 • X2 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX20 • X2 ≈ CX02 • CX20 • X2
  p3 = refl

  p4 : SWAP02 • X2 • CX02 ≈ X0 • SWAP02 • CX02
  p4 = by-assoc-and (under (ε) (CX02) KB0093.proved) Eq.refl Eq.refl

  p5 : X0 • SWAP02 • CX02 ≈ X0 • CX02 • CX20
  p5 = by-assoc-and (under (X0) (ε) KB0086.proved) Eq.refl Eq.refl

  p6 : SWAP02 • X2 • CX02 ≈ X0 • CX02 • CX20
  p6 = trans p4 (trans p5 (refl))

  p7 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
  proved = p7

module KB0270 where

  p0 : CX02 • CX20 • SWAP02 • X0 • SWAP02 ≈ CX20 • X0 • SWAP02
  p0 = by-assoc-and (under (ε) (X0 • SWAP02) KB0098.proved) Eq.refl Eq.refl

  p1 : CX02 • CX20 • SWAP02 • X0 • SWAP02 ≈ CX02 • CX20 • X2
  p1 = by-assoc-and (under (CX02 • CX20) (ε) KB0092.proved) Eq.refl Eq.refl

  p2 : CX20 • X0 • SWAP02 ≈ CX02 • CX20 • X2
  p2 = trans (sym p0) p1

  p3 : CX20 • X0 • SWAP02 ≈ CX20 • X0 • SWAP02
  p3 = refl

  p4 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
  p4 = by-assoc-and (under (ε) (ε) KB0260.proved) Eq.refl Eq.refl

  p5 : CX02 • CX20 • X2 ≈ X0 • CX02 • CX20
  p5 = trans p4 (refl)

  p6 : CX20 • X0 • SWAP02 ≈ X0 • CX02 • CX20
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX20 • X0 • SWAP02 ≈ X0 • CX02 • CX20
  proved = p6

module KB0316 where

  p0 : CX02 • CX20 • SWAP02 • X2 ≈ CX20 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0098.proved) Eq.refl Eq.refl

  p1 : CX02 • CX20 • SWAP02 • X2 ≈ CX02 • CX20 • X0 • SWAP02
  p1 = by-assoc-and (under (CX02 • CX20) (ε) KB0093.proved) Eq.refl Eq.refl

  p2 : CX20 • X2 ≈ CX02 • CX20 • X0 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX20 • X2 ≈ CX20 • X2
  p3 = refl

  p4 : CX02 • CX20 • X0 • SWAP02 ≈ CX02 • X0 • CX02 • CX20
  p4 = by-assoc-and (under (CX02) (ε) KB0270.proved) Eq.refl Eq.refl

  p5 : CX02 • X0 • CX02 • CX20 ≈ X0 • X2 • CX20
  p5 = by-assoc-and (under (ε) (CX20) KB0160.proved) Eq.refl Eq.refl

  p6 : CX02 • CX20 • X0 • SWAP02 ≈ X0 • X2 • CX20
  p6 = trans p4 (trans p5 (refl))

  p7 : CX20 • X2 ≈ X0 • X2 • CX20
  p7 = trans (sym p3) (trans p2 p6)

  p8 : X0 • X2 • CX20 ≈ CX20 • X2
  p8 = sym p7

  proved : X0 • X2 • CX20 ≈ CX20 • X2
  proved = p8

module KB0416 where

  p0 : CCX01 • X2 • CX02 • X0 ≈ CCX01 • X0 • CX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0128.proved) Eq.refl Eq.refl

  p1 : CCX01 • X2 • CX02 • X0 ≈ X2 • CCX01 • CX02 • X0
  p1 = by-assoc-and (under (ε) (CX02 • X0) KB0029.proved) Eq.refl Eq.refl

  p2 : CCX01 • X0 • CX02 ≈ X2 • CCX01 • CX02 • X0
  p2 = trans (sym p0) p1

  p3 : CCX01 • X0 • CX02 ≈ CCX01 • X0 • CX02
  p3 = refl

  p4 : X2 • CCX01 • CX02 • X0 ≈ X2 • CX02 • CCX01 • X0
  p4 = by-assoc-and (under (X2) (X0) KB0037.proved) Eq.refl Eq.refl

  p5 : X2 • CCX01 • CX02 • X0 ≈ X2 • CX02 • CCX01 • X0
  p5 = trans p4 (refl)

  p6 : CCX01 • X0 • CX02 ≈ X2 • CX02 • CCX01 • X0
  p6 = trans (sym p3) (trans p2 p5)

  p7 : X2 • CX02 • CCX01 • X0 ≈ CCX01 • X0 • CX02
  p7 = sym p6

  proved : X2 • CX02 • CCX01 • X0 ≈ CCX01 • X0 • CX02
  proved = p7

module KB0423 where

  p0 : SWAP01 • CX01 • CX10 • CCX12 • X2 ≈ SWAP01 • CX01 • X2 • CCX12
  p0 = by-assoc-and (under (SWAP01 • CX01) (ε) KB0131.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CX01 • CX10 • CCX12 • X2 ≈ CX01 • CCX12 • X2
  p1 = by-assoc-and (under (ε) (CCX12 • X2) KB0062.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CX01 • X2 • CCX12 ≈ CX01 • CCX12 • X2
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CX01 • X2 • CCX12 ≈ CX01 • CX10 • X2 • CCX12
  p3 = by-assoc-and (under (ε) (X2 • CCX12) KB0063.proved) Eq.refl Eq.refl

  p4 : CX01 • CX10 • X2 • CCX12 ≈ CX01 • X2 • CX10 • CCX12
  p4 = by-assoc-and (under (CX01) (CCX12) KB0021.proved) Eq.refl Eq.refl

  p5 : CX01 • X2 • CX10 • CCX12 ≈ X2 • CX01 • CX10 • CCX12
  p5 = by-assoc-and (under (ε) (CX10 • CCX12) KB0022.proved) Eq.refl Eq.refl

  p6 : SWAP01 • CX01 • X2 • CCX12 ≈ X2 • CX01 • CX10 • CCX12
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  p7 : CX01 • CCX12 • X2 ≈ CX01 • CCX12 • X2
  p7 = refl

  p8 : X2 • CX01 • CX10 • CCX12 ≈ CX01 • CCX12 • X2
  p8 = trans (sym p6) (trans p2 p7)

  proved : X2 • CX01 • CX10 • CCX12 ≈ CX01 • CCX12 • X2
  proved = p8

module KB0034 where

  p0 : X1 • CX21 ≈ CX21 • X1
  p0 = drel79.proved

  p1 : X1 • CX21 ≈ X1 • CX21
  p1 = refl

  p2 : CX21 • X1 ≈ CX21 • X1
  p2 = refl

  p3 : X1 • CX21 ≈ CX21 • X1
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX21 • X1 ≈ X1 • CX21
  p4 = sym p3

  proved : CX21 • X1 ≈ X1 • CX21
  proved = p4

module KB0132 where

  p0 : X1 • CCX12 ≈ CCX12 • CX20 • X1
  p0 = drel131.proved

  p1 : X1 • CCX12 ≈ X1 • CCX12
  p1 = refl

  p2 : CCX12 • CX20 • X1 ≈ CX20 • CCX12 • X1
  p2 = by-assoc-and (under (ε) (X1) KB0040.proved) Eq.refl Eq.refl

  p3 : CCX12 • CX20 • X1 ≈ CX20 • CCX12 • X1
  p3 = trans p2 (refl)

  p4 : X1 • CCX12 ≈ CX20 • CCX12 • X1
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX20 • CCX12 • X1 ≈ X1 • CCX12
  p5 = sym p4

  proved : CX20 • CCX12 • X1 ≈ X1 • CCX12
  proved = p5

module KB0138 where

  p0 : CX21 • CCX12 ≈ CCX12 • CX20 • CX21
  p0 = drel155.proved

  p1 : CX21 • CCX12 ≈ CX21 • CCX12
  p1 = refl

  p2 : CCX12 • CX20 • CX21 ≈ CX20 • CCX12 • CX21
  p2 = by-assoc-and (under (ε) (CX21) KB0040.proved) Eq.refl Eq.refl

  p3 : CCX12 • CX20 • CX21 ≈ CX20 • CCX12 • CX21
  p3 = trans p2 (refl)

  p4 : CX21 • CCX12 ≈ CX20 • CCX12 • CX21
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX20 • CCX12 • CX21 ≈ CX21 • CCX12
  p5 = sym p4

  proved : CX20 • CCX12 • CX21 ≈ CX21 • CCX12
  proved = p5

module KB0439 where

  p0 : CX20 • CCX12 • CX21 • X1 ≈ CX21 • CCX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0138.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX12 • CX21 • X1 ≈ CX20 • CCX12 • X1 • CX21
  p1 = by-assoc-and (under (CX20 • CCX12) (ε) KB0034.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX12 • X1 ≈ CX20 • CCX12 • X1 • CX21
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX12 • X1 ≈ CX21 • CCX12 • X1
  p3 = refl

  p4 : CX20 • CCX12 • X1 • CX21 ≈ X1 • CCX12 • CX21
  p4 = by-assoc-and (under (ε) (CX21) KB0132.proved) Eq.refl Eq.refl

  p5 : CX20 • CCX12 • X1 • CX21 ≈ X1 • CCX12 • CX21
  p5 = trans p4 (refl)

  p6 : CX21 • CCX12 • X1 ≈ X1 • CCX12 • CX21
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX21 • CCX12 • X1 ≈ X1 • CCX12 • CX21
  proved = p6

module KB0024 where

  p0 : CX20 • X1 ≈ X1 • CX20
  p0 = bifunct_X_CX_f.proved

  p1 : CX20 • X1 ≈ CX20 • X1
  p1 = refl

  p2 : X1 • CX20 ≈ X1 • CX20
  p2 = refl

  p3 : CX20 • X1 ≈ X1 • CX20
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX20 • X1 ≈ X1 • CX20
  proved = p3

module KB0085 where

  p0 : CX02 • CX02 • CX20 • CX02 ≈ CX02 • SWAP02
  p0 = by-assoc-and (under (CX02) (ε) KB0084.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CX20 • CX02 ≈ CX20 • CX02
  p1 = by-assoc-and (under (ε) (CX20 • CX02) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • SWAP02 ≈ CX20 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • SWAP02 ≈ CX02 • SWAP02
  p3 = refl

  p4 : CX20 • CX02 ≈ CX20 • CX02
  p4 = refl

  p5 : CX02 • SWAP02 ≈ CX20 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX20 • CX02 ≈ CX02 • SWAP02
  p6 = sym p5

  proved : CX20 • CX02 ≈ CX02 • SWAP02
  proved = p6

module KB0476 where

  p0 : CX20 • X1 • CX02 • CCX01 ≈ CX20 • CCX01 • X1
  p0 = by-assoc-and (under (CX20) (ε) KB0151.proved) Eq.refl Eq.refl

  p1 : CX20 • X1 • CX02 • CCX01 ≈ X1 • CX20 • CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0024.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX01 • X1 ≈ X1 • CX20 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX01 • X1 ≈ CX20 • CCX01 • X1
  p3 = refl

  p4 : X1 • CX20 • CX02 • CCX01 ≈ X1 • CX02 • SWAP02 • CCX01
  p4 = by-assoc-and (under (X1) (CCX01) KB0085.proved) Eq.refl Eq.refl

  p5 : X1 • CX02 • SWAP02 • CCX01 ≈ X1 • CX02 • CCX12 • SWAP02
  p5 = by-assoc-and (under (X1 • CX02) (ε) KB0104.proved) Eq.refl Eq.refl

  p6 : X1 • CX20 • CX02 • CCX01 ≈ X1 • CX02 • CCX12 • SWAP02
  p6 = trans p4 (trans p5 (refl))

  p7 : CX20 • CCX01 • X1 ≈ X1 • CX02 • CCX12 • SWAP02
  p7 = trans (sym p3) (trans p2 p6)

  p8 : X1 • CX02 • CCX12 • SWAP02 ≈ CX20 • CCX01 • X1
  p8 = sym p7

  proved : X1 • CX02 • CCX12 • SWAP02 ≈ CX20 • CCX01 • X1
  proved = p8

module KB0480 where

  p0 : CCX01 • X0 • CCX01 • CX02 ≈ X0 • CX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0152.proved) Eq.refl Eq.refl

  p1 : CCX01 • X0 • CCX01 • CX02 ≈ CCX01 • X0 • CX02 • CCX01
  p1 = by-assoc-and (under (CCX01 • X0) (ε) KB0037.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CX02 ≈ CCX01 • X0 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • CX12 • CX02 ≈ X0 • CX02 • CX12
  p3 = by-assoc-and (under (X0) (ε) KB0027.proved) Eq.refl Eq.refl

  p4 : X0 • CX12 • CX02 ≈ X0 • CX02 • CX12
  p4 = trans p3 (refl)

  p5 : CCX01 • X0 • CX02 • CCX01 ≈ CCX01 • X0 • CX02 • CCX01
  p5 = refl

  p6 : X0 • CX02 • CX12 ≈ CCX01 • X0 • CX02 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • X0 • CX02 • CCX01 ≈ X0 • CX02 • CX12
  p7 = sym p6

  proved : CCX01 • X0 • CX02 • CCX01 ≈ X0 • CX02 • CX12
  proved = p7

module KB0514 where

  p0 : X1 • X0 • CCX02 • X0 ≈ X1 • CX21 • CCX02
  p0 = by-assoc-and (under (X1) (ε) KB0166.proved) Eq.refl Eq.refl

  p1 : X1 • X0 • CCX02 • X0 ≈ X0 • X1 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0044.proved) Eq.refl Eq.refl

  p2 : X1 • CX21 • CCX02 ≈ X0 • X1 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : X1 • CX21 • CCX02 ≈ X1 • CX21 • CCX02
  p3 = refl

  p4 : X0 • X1 • CCX02 • X0 ≈ X0 • X1 • CCX02 • X0
  p4 = refl

  p5 : X1 • CX21 • CCX02 ≈ X0 • X1 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • X1 • CCX02 • X0 ≈ X1 • CX21 • CCX02
  p6 = sym p5

  proved : X0 • X1 • CCX02 • X0 ≈ X1 • CX21 • CCX02
  proved = p6

module KB0194 where

  p0 : X2 • CX10 • CCX12 • CCX12 ≈ CCX12 • X2 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0168.proved) Eq.refl Eq.refl

  p1 : X2 • CX10 • CCX12 • CCX12 ≈ X2 • CX10
  p1 = by-assoc-and (under (X2 • CX10) (ε) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • X2 • CCX12 ≈ X2 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX12 • X2 • CCX12 ≈ CCX12 • X2 • CCX12
  p3 = refl

  p4 : X2 • CX10 ≈ X2 • CX10
  p4 = refl

  p5 : CCX12 • X2 • CCX12 ≈ X2 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • X2 • CCX12 ≈ X2 • CX10
  proved = p5

module KB0566 where

  p0 : CCX12 • X2 • CCX12 • CX20 ≈ X2 • CX10 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0194.proved) Eq.refl Eq.refl

  p1 : CCX12 • X2 • CCX12 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
  p1 = by-assoc-and (under (CCX12 • X2) (ε) KB0040.proved) Eq.refl Eq.refl

  p2 : X2 • CX10 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
  p2 = trans (sym p0) p1

  p3 : X2 • CX10 • CX20 ≈ X2 • CX10 • CX20
  p3 = refl

  p4 : CCX12 • X2 • CX20 • CCX12 ≈ CCX12 • X2 • CX20 • CCX12
  p4 = refl

  p5 : X2 • CX10 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • X2 • CX20 • CCX12 ≈ X2 • CX10 • CX20
  p6 = sym p5

  proved : CCX12 • X2 • CX20 • CCX12 ≈ X2 • CX10 • CX20
  proved = p6

module KB0614 where

  p0 : CX01 • CX20 • CX21 • X0 ≈ CX20 • CX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0303.proved) Eq.refl Eq.refl

  p1 : CX01 • CX20 • CX21 • X0 ≈ CX01 • CX20 • X0 • CX21
  p1 = by-assoc-and (under (CX01 • CX20) (ε) KB0020.proved) Eq.refl Eq.refl

  p2 : CX20 • CX01 • X0 ≈ CX01 • CX20 • X0 • CX21
  p2 = trans (sym p0) p1

  p3 : CX20 • CX01 • X0 ≈ CX20 • CX01 • X0
  p3 = refl

  p4 : CX01 • CX20 • X0 • CX21 ≈ CX01 • X0 • CX20 • CX21
  p4 = by-assoc-and (under (CX01) (CX21) KB0309.proved) Eq.refl Eq.refl

  p5 : CX01 • CX20 • X0 • CX21 ≈ CX01 • X0 • CX20 • CX21
  p5 = trans p4 (refl)

  p6 : CX20 • CX01 • X0 ≈ CX01 • X0 • CX20 • CX21
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX01 • X0 • CX20 • CX21 ≈ CX20 • CX01 • X0
  p7 = sym p6

  proved : CX01 • X0 • CX20 • CX21 ≈ CX20 • CX01 • X0
  proved = p7

module KB0657 where

  p0 : CCX12 • CX02 • CCX01 • X1 ≈ CX02 • CCX01 • CCX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0322.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX02 • CCX01 • X1 ≈ CCX12 • X1 • CCX01
  p1 = by-assoc-and (under (CCX12) (ε) KB0120.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • CCX12 • X1 ≈ CX02 • CCX01 • CCX12 • X1
  p3 = refl

  p4 : CCX12 • X1 • CCX01 ≈ CCX12 • X1 • CCX01
  p4 = refl

  p5 : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
  proved = p5

module KB0774 where

  p0 : CX21 • CCX02 • CX20 • CCX12 • X1 ≈ CX20 • CCX02 • CCX12 • X1
  p0 = by-assoc-and (under (ε) (CCX12 • X1) KB0136.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • CX20 • CCX12 • X1 ≈ CX21 • CCX02 • X1 • CCX12
  p1 = by-assoc-and (under (CX21 • CCX02) (ε) KB0132.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX02 • CCX12 • X1 ≈ CX21 • CCX02 • X1 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX02 • CCX12 • X1 ≈ CX20 • CCX02 • CCX12 • X1
  p3 = refl

  p4 : CX21 • CCX02 • X1 • CCX12 ≈ CX21 • X1 • CCX02 • CCX12
  p4 = by-assoc-and (under (CX21) (CCX12) KB0028.proved) Eq.refl Eq.refl

  p5 : CX21 • X1 • CCX02 • CCX12 ≈ X1 • CX21 • CCX02 • CCX12
  p5 = by-assoc-and (under (ε) (CCX02 • CCX12) KB0034.proved) Eq.refl Eq.refl

  p6 : CX21 • CCX02 • X1 • CCX12 ≈ X1 • CX21 • CCX02 • CCX12
  p6 = trans p4 (trans p5 (refl))

  p7 : CX20 • CCX02 • CCX12 • X1 ≈ X1 • CX21 • CCX02 • CCX12
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX20 • CCX02 • CCX12 • X1 ≈ X1 • CX21 • CCX02 • CCX12
  proved = p7

module KB0505 where

  p0 : CX01 • CX02 • CX12 • X0 ≈ CX12 • CX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0164.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CX12 • X0 ≈ CX01 • CX02 • X0 • CX12
  p1 = by-assoc-and (under (CX01 • CX02) (ε) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • X0 ≈ CX12 • CX01 • X0
  p3 = refl

  p4 : CX01 • CX02 • X0 • CX12 ≈ CX01 • CX02 • X0 • CX12
  p4 = refl

  p5 : CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
  p6 = sym p5

  proved : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
  proved = p6

module KB0813 where

  p0 : CX01 • CX02 • CCX01 • X0 • CCX01 ≈ CX01 • CX02 • X0 • CX12
  p0 = by-assoc-and (under (CX01 • CX02) (ε) KB0152.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (X0 • CCX01) KB0123.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • X0 • CX12 ≈ CCX01 • CX01 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
  p3 = by-assoc-and (under (ε) (ε) KB0505.proved) Eq.refl Eq.refl

  p4 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
  p4 = trans p3 (refl)

  p5 : CCX01 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0 • CCX01
  p5 = refl

  p6 : CX12 • CX01 • X0 ≈ CCX01 • CX01 • X0 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0
  p7 = sym p6

  proved : CCX01 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0
  proved = p7

module KB0814 where

  p0 : CCX01 • CX01 • X0 • CCX01 • CCX01 ≈ CX12 • CX01 • X0 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0813.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • X0 • CCX01 • CCX01 ≈ CCX01 • CX01 • X0
  p1 = by-assoc-and (under (CCX01 • CX01 • X0) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0 • CCX01
  p3 = refl

  p4 : CCX01 • CX01 • X0 ≈ CCX01 • CX01 • X0
  p4 = refl

  p5 : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
  proved = p5

module KB0134 where

  p0 : CX02 • CX21 ≈ CX21 • CX02 • CX01
  p0 = drel134.proved

  p1 : CX02 • CX21 ≈ CX02 • CX21
  p1 = refl

  p2 : CX21 • CX02 • CX01 ≈ CX21 • CX01 • CX02
  p2 = by-assoc-and (under (CX21) (ε) KB0025.proved) Eq.refl Eq.refl

  p3 : CX21 • CX01 • CX02 ≈ CX01 • CX21 • CX02
  p3 = by-assoc-and (under (ε) (CX02) KB0030.proved) Eq.refl Eq.refl

  p4 : CX21 • CX02 • CX01 ≈ CX01 • CX21 • CX02
  p4 = trans p2 (trans p3 (refl))

  p5 : CX02 • CX21 ≈ CX01 • CX21 • CX02
  p5 = trans (sym p1) (trans p0 p4)

  p6 : CX01 • CX21 • CX02 ≈ CX02 • CX21
  p6 = sym p5

  proved : CX01 • CX21 • CX02 ≈ CX02 • CX21
  proved = p6

module KB0173 where

  p0 : CX01 • CX21 • CX02 • CX02 ≈ CX02 • CX21 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0134.proved) Eq.refl Eq.refl

  p1 : CX01 • CX21 • CX02 • CX02 ≈ CX01 • CX21
  p1 = by-assoc-and (under (CX01 • CX21) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CX21 • CX02 ≈ CX01 • CX21
  p2 = trans (sym p0) p1

  p3 : CX02 • CX21 • CX02 ≈ CX02 • CX21 • CX02
  p3 = refl

  p4 : CX01 • CX21 ≈ CX01 • CX21
  p4 = refl

  p5 : CX02 • CX21 • CX02 ≈ CX01 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CX21 • CX02 ≈ CX01 • CX21
  proved = p5
