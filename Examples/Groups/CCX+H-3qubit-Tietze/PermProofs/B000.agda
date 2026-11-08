{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B000 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r021 ; r022 ; r024 ; r037 ; r046 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_e ; module drel127 ; module drel162 ; module elim_CCX1 ; module elim_CX02 ; module elim_CX12 ; module elim_CX20 ; module elim_X1)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel112)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module drel69 ; module drel84)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module cadd7 ; module drel90 ; module drel96)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module cadd4 ; module cadd6 ; module cflip0 ; module cflip2 ; module drel10 ; module drel106 ; module elim_CCX2)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B005 using (module drel11)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B006 using (module drel140 ; module drel82)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B007 using (module drel25 ; module drel26 ; module drel55 ; module drel61 ; module drel93 ; module drel94)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B008 using (module drel91 ; module drel98)

module decodeCCX01 where

  p0 : CCX01 ≈ CCX01
  p0 = refl

  p1 : CCX01 ≈ CCX01
  p1 = refl

  proved : CCX01 ≈ CCX01
  proved = trans p0 (sym p1)

module KB0011 where

  p0 : CCX01 • CCX01 ≈ ε
  p0 = elim_CCX2.proved

  p1 : CCX01 • CCX01 ≈ CCX01 • CCX01
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CCX01 • CCX01 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX01 • CCX01 ≈ ε
  proved = p3

module decodeCCX02 where

  p0 : CCX02 ≈ CCX02
  p0 = refl

  p1 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CCX01 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX01 • CCX01 ≈ CCX02
  p2 = by-assoc-and (under (CCX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p3 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02
  p3 = trans p1 (trans p2 (refl))

  proved : CCX02 ≈ CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  proved = trans p0 (sym p3)

module KB0003 where

  p0 : X1 • X1 ≈ ε
  p0 = elim_X1.proved

  p1 : X1 • X1 ≈ X1 • X1
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : X1 • X1 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : X1 • X1 ≈ ε
  proved = p3

module KB0010 where

  p0 : CCX02 • CCX02 ≈ ε
  p0 = elim_CCX1.proved

  p1 : CCX02 • CCX02 ≈ CCX02 • CCX02
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CCX02 • CCX02 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX02 • CCX02 ≈ ε
  proved = p3

module KB0012 where

  p0 : X0 • X0 ≈ ε
  p0 = by-assoc-and (axiom r021) Eq.refl Eq.refl

  p1 : X0 • X0 ≈ X0 • X0
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : X0 • X0 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : X0 • X0 ≈ ε
  proved = p3

module KB0023 where

  p0 : CX02 • X1 ≈ X1 • CX02
  p0 = bifunct_X_CX_e.proved

  p1 : CX02 • X1 ≈ CX02 • X1
  p1 = refl

  p2 : X1 • CX02 ≈ X1 • CX02
  p2 = refl

  p3 : CX02 • X1 ≈ X1 • CX02
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX02 • X1 ≈ X1 • CX02
  proved = p3

module KB0028 where

  p0 : X1 • CCX02 ≈ CCX02 • X1
  p0 = drel25.proved

  p1 : X1 • CCX02 ≈ X1 • CCX02
  p1 = refl

  p2 : CCX02 • X1 ≈ CCX02 • X1
  p2 = refl

  p3 : X1 • CCX02 ≈ CCX02 • X1
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX02 • X1 ≈ X1 • CCX02
  p4 = sym p3

  proved : CCX02 • X1 ≈ X1 • CCX02
  proved = p4

module KB0033 where

  p0 : CX02 • X2 ≈ X2 • CX02
  p0 = drel61.proved

  p1 : CX02 • X2 ≈ CX02 • X2
  p1 = refl

  p2 : X2 • CX02 ≈ X2 • CX02
  p2 = refl

  p3 : CX02 • X2 ≈ X2 • CX02
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX02 • X2 ≈ X2 • CX02
  proved = p3

module KB0125 where

  p0 : X0 • X2 • CX02 ≈ CX02 • X0
  p0 = drel106.proved

  p1 : X0 • X2 • CX02 ≈ X0 • X2 • CX02
  p1 = refl

  p2 : CX02 • X0 ≈ CX02 • X0
  p2 = refl

  p3 : X0 • X2 • CX02 ≈ CX02 • X0
  p3 = trans (sym p1) (trans p0 p2)

  proved : X0 • X2 • CX02 ≈ CX02 • X0
  proved = p3

module KB0008 where

  p0 : CX02 • CX02 ≈ ε
  p0 = elim_CX02.proved

  p1 : CX02 • CX02 ≈ CX02 • CX02
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX02 • CX02 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX02 • CX02 ≈ ε
  proved = p3

module KB0037 where

  p0 : CCX01 • CX02 ≈ CX02 • CCX01
  p0 = drel91.proved

  p1 : CCX01 • CX02 ≈ CCX01 • CX02
  p1 = refl

  p2 : CX02 • CCX01 ≈ CX02 • CCX01
  p2 = refl

  p3 : CCX01 • CX02 ≈ CX02 • CCX01
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX01 • CX02 ≈ CX02 • CCX01
  proved = p3

module KB0120 where

  p0 : X1 • CCX01 ≈ CCX01 • CX02 • X1
  p0 = drel96.proved

  p1 : X1 • CCX01 ≈ X1 • CCX01
  p1 = refl

  p2 : CCX01 • CX02 • X1 ≈ CX02 • CCX01 • X1
  p2 = by-assoc-and (under (ε) (X1) KB0037.proved) Eq.refl Eq.refl

  p3 : CCX01 • CX02 • X1 ≈ CX02 • CCX01 • X1
  p3 = trans p2 (refl)

  p4 : X1 • CCX01 ≈ CX02 • CCX01 • X1
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX02 • CCX01 • X1 ≈ X1 • CCX01
  p5 = sym p4

  proved : CX02 • CCX01 • X1 ≈ X1 • CCX01
  proved = p5

module KB0151 where

  p0 : CX02 • CX02 • CCX01 • X1 ≈ CX02 • X1 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB0120.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX01 • X1 ≈ CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • X1 • CCX01 ≈ CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • X1 • CCX01 ≈ X1 • CX02 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0023.proved) Eq.refl Eq.refl

  p4 : CX02 • X1 • CCX01 ≈ X1 • CX02 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • X1 ≈ CCX01 • X1
  p5 = refl

  p6 : X1 • CX02 • CCX01 ≈ CCX01 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : X1 • CX02 • CCX01 ≈ CCX01 • X1
  proved = p6

module KB0186 where

  p0 : X1 • CX02 • CCX01 • CCX01 ≈ CCX01 • X1 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0151.proved) Eq.refl Eq.refl

  p1 : X1 • CX02 • CCX01 • CCX01 ≈ X1 • CX02
  p1 = by-assoc-and (under (X1 • CX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • X1 • CCX01 ≈ X1 • CX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • X1 • CCX01 ≈ CCX01 • X1 • CCX01
  p3 = refl

  p4 : X1 • CX02 ≈ X1 • CX02
  p4 = refl

  p5 : CCX01 • X1 • CCX01 ≈ X1 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X1 • CCX01 ≈ X1 • CX02
  proved = p5

module KB0160 where

  p0 : X0 • X2 • CX02 • CX02 ≈ CX02 • X0 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0125.proved) Eq.refl Eq.refl

  p1 : X0 • X2 • CX02 • CX02 ≈ X0 • X2
  p1 = by-assoc-and (under (X0 • X2) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • X0 • CX02 ≈ X0 • X2
  p2 = trans (sym p0) p1

  p3 : CX02 • X0 • CX02 ≈ CX02 • X0 • CX02
  p3 = refl

  p4 : X0 • X2 ≈ X0 • X2
  p4 = refl

  p5 : CX02 • X0 • CX02 ≈ X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • X0 • CX02 ≈ X0 • X2
  proved = p5

module KB0191 where

  p0 : CX02 • CX02 • X0 • CX02 ≈ CX02 • X0 • X2
  p0 = by-assoc-and (under (CX02) (ε) KB0160.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • X0 • CX02 ≈ X0 • CX02
  p1 = by-assoc-and (under (ε) (X0 • CX02) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • X0 • X2 ≈ X0 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • X0 • X2 ≈ CX02 • X0 • X2
  p3 = refl

  p4 : X0 • CX02 ≈ X0 • CX02
  p4 = refl

  p5 : CX02 • X0 • X2 ≈ X0 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • X0 • X2 ≈ X0 • CX02
  proved = p5

module KB0013 where

  p0 : CX01 • CX01 ≈ ε
  p0 = by-assoc-and (axiom r022) Eq.refl Eq.refl

  p1 : CX01 • CX01 ≈ CX01 • CX01
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX01 • CX01 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX01 • CX01 ≈ ε
  proved = p3

module KB0027 where

  p0 : CX12 • CX02 ≈ CX02 • CX12
  p0 = drel11.proved

  p1 : CX12 • CX02 ≈ CX12 • CX02
  p1 = refl

  p2 : CX02 • CX12 ≈ CX02 • CX12
  p2 = refl

  p3 : CX12 • CX02 ≈ CX02 • CX12
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX12 • CX02 ≈ CX02 • CX12
  proved = p3

module KB0127 where

  p0 : CX01 • CX12 ≈ CX12 • CX01 • CX02
  p0 = drel112.proved

  p1 : CX01 • CX12 ≈ CX01 • CX12
  p1 = refl

  p2 : CX12 • CX01 • CX02 ≈ CX12 • CX01 • CX02
  p2 = refl

  p3 : CX01 • CX12 ≈ CX12 • CX01 • CX02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX12 • CX01 • CX02 ≈ CX01 • CX12
  p4 = sym p3

  proved : CX12 • CX01 • CX02 ≈ CX01 • CX12
  proved = p4

module KB0164 where

  p0 : CX12 • CX01 • CX02 • CX02 ≈ CX01 • CX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0127.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX02 • CX02 ≈ CX12 • CX01
  p1 = by-assoc-and (under (CX12 • CX01) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : CX01 • CX12 • CX02 ≈ CX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX12 • CX02 ≈ CX01 • CX02 • CX12
  p3 = by-assoc-and (under (CX01) (ε) KB0027.proved) Eq.refl Eq.refl

  p4 : CX01 • CX12 • CX02 ≈ CX01 • CX02 • CX12
  p4 = trans p3 (refl)

  p5 : CX12 • CX01 ≈ CX12 • CX01
  p5 = refl

  p6 : CX01 • CX02 • CX12 ≈ CX12 • CX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX01 • CX02 • CX12 ≈ CX12 • CX01
  proved = p6

module KB0192 where

  p0 : CX01 • CX01 • CX02 • CX12 ≈ CX01 • CX12 • CX01
  p0 = by-assoc-and (under (CX01) (ε) KB0164.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CX02 • CX12 ≈ CX02 • CX12
  p1 = by-assoc-and (under (ε) (CX02 • CX12) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CX12 • CX01 ≈ CX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CX12 • CX01 ≈ CX01 • CX12 • CX01
  p3 = refl

  p4 : CX02 • CX12 ≈ CX02 • CX12
  p4 = refl

  p5 : CX01 • CX12 • CX01 ≈ CX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CX12 • CX01 ≈ CX02 • CX12
  proved = p5

module KB0216 where

  p0 : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
  p0 = cadd7.proved

  p1 : CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01
  p1 = refl

  p2 : CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02
  p2 = refl

  p3 : CX01 • CCX12 • CX01 ≈ CCX02 • CCX12 • CCX02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
  p4 = sym p3

  proved : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
  proved = p4

module KB0477 where

  p0 : CCX02 • X1 • CX02 • CCX01 ≈ CCX02 • CCX01 • X1
  p0 = by-assoc-and (under (CCX02) (ε) KB0151.proved) Eq.refl Eq.refl

  p1 : CCX02 • X1 • CX02 • CCX01 ≈ X1 • CCX02 • CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX01 • X1 ≈ CCX02 • CCX01 • X1
  p3 = refl

  p4 : X1 • CCX02 • CX02 • CCX01 ≈ X1 • CCX02 • CX02 • CCX01
  p4 = refl

  p5 : CCX02 • CCX01 • X1 ≈ X1 • CCX02 • CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X1 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX01 • X1
  p6 = sym p5

  proved : X1 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX01 • X1
  proved = p6

module KB0046 where

  p0 : X0 • CCX12 ≈ CCX12 • X0
  p0 = by-assoc-and (axiom r037) Eq.refl Eq.refl

  p1 : X0 • CCX12 ≈ X0 • CCX12
  p1 = refl

  p2 : CCX12 • X0 ≈ CCX12 • X0
  p2 = refl

  p3 : X0 • CCX12 ≈ CCX12 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX12 • X0 ≈ X0 • CCX12
  p4 = sym p3

  proved : CCX12 • X0 ≈ X0 • CCX12
  proved = p4

module KB0039 where

  p0 : CCX02 • CX21 ≈ CX21 • CCX02
  p0 = drel93.proved

  p1 : CCX02 • CX21 ≈ CCX02 • CX21
  p1 = refl

  p2 : CX21 • CCX02 ≈ CX21 • CCX02
  p2 = refl

  p3 : CCX02 • CX21 ≈ CX21 • CCX02
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX02 • CX21 ≈ CX21 • CCX02
  proved = p3

module KB0129 where

  p0 : X0 • CCX02 ≈ CCX02 • CX21 • X0
  p0 = drel127.proved

  p1 : X0 • CCX02 ≈ X0 • CCX02
  p1 = refl

  p2 : CCX02 • CX21 • X0 ≈ CX21 • CCX02 • X0
  p2 = by-assoc-and (under (ε) (X0) KB0039.proved) Eq.refl Eq.refl

  p3 : CCX02 • CX21 • X0 ≈ CX21 • CCX02 • X0
  p3 = trans p2 (refl)

  p4 : X0 • CCX02 ≈ CX21 • CCX02 • X0
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX21 • CCX02 • X0 ≈ X0 • CCX02
  p5 = sym p4

  proved : CX21 • CCX02 • X0 ≈ X0 • CCX02
  proved = p5

module KB0166 where

  p0 : CX21 • CCX02 • X0 • X0 ≈ X0 • CCX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0129.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • X0 • X0 ≈ CX21 • CCX02
  p1 = by-assoc-and (under (CX21 • CCX02) (ε) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CCX02 • X0 ≈ CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : X0 • CCX02 • X0 ≈ X0 • CCX02 • X0
  p3 = refl

  p4 : CX21 • CCX02 ≈ CX21 • CCX02
  p4 = refl

  p5 : X0 • CCX02 • X0 ≈ CX21 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CCX02 • X0 ≈ CX21 • CCX02
  proved = p5

module KB0516 where

  p0 : CCX12 • X0 • CCX02 • X0 ≈ CCX12 • CX21 • CCX02
  p0 = by-assoc-and (under (CCX12) (ε) KB0166.proved) Eq.refl Eq.refl

  p1 : CCX12 • X0 • CCX02 • X0 ≈ X0 • CCX12 • CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0046.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX21 • CCX02 ≈ X0 • CCX12 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX21 • CCX02 ≈ CCX12 • CX21 • CCX02
  p3 = refl

  p4 : X0 • CCX12 • CCX02 • X0 ≈ X0 • CCX12 • CCX02 • X0
  p4 = refl

  p5 : CCX12 • CX21 • CCX02 ≈ X0 • CCX12 • CCX02 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CCX12 • CCX02 • X0 ≈ CCX12 • CX21 • CCX02
  p6 = sym p5

  proved : X0 • CCX12 • CCX02 • X0 ≈ CCX12 • CX21 • CCX02
  proved = p6

module KB0035 where

  p0 : X1 • CX01 ≈ CX01 • X1
  p0 = drel82.proved

  p1 : X1 • CX01 ≈ X1 • CX01
  p1 = refl

  p2 : CX01 • X1 ≈ CX01 • X1
  p2 = refl

  p3 : X1 • CX01 ≈ CX01 • X1
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX01 • X1 ≈ X1 • CX01
  p4 = sym p3

  proved : CX01 • X1 ≈ X1 • CX01
  proved = p4

module KB0139 where

  p0 : X0 • CX01 ≈ CX01 • X1 • X0
  p0 = drel162.proved

  p1 : X0 • CX01 ≈ X0 • CX01
  p1 = refl

  p2 : CX01 • X1 • X0 ≈ X1 • CX01 • X0
  p2 = by-assoc-and (under (ε) (X0) KB0035.proved) Eq.refl Eq.refl

  p3 : CX01 • X1 • X0 ≈ X1 • CX01 • X0
  p3 = trans p2 (refl)

  p4 : X0 • CX01 ≈ X1 • CX01 • X0
  p4 = trans (sym p1) (trans p0 p3)

  p5 : X1 • CX01 • X0 ≈ X0 • CX01
  p5 = sym p4

  proved : X1 • CX01 • X0 ≈ X0 • CX01
  proved = p5

module KB0780 where

  p0 : CX02 • CCX01 • X1 • CX01 • X0 ≈ CX02 • CCX01 • X0 • CX01
  p0 = by-assoc-and (under (CX02 • CCX01) (ε) KB0139.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • CX01 • X0 ≈ X1 • CCX01 • CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0120.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • X0 • CX01 ≈ CX02 • CCX01 • X0 • CX01
  p3 = refl

  p4 : X1 • CCX01 • CX01 • X0 ≈ X1 • CCX01 • CX01 • X0
  p4 = refl

  p5 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
  proved = p5

module KB0029 where

  p0 : X2 • CCX01 ≈ CCX01 • X2
  p0 = drel26.proved

  p1 : X2 • CCX01 ≈ X2 • CCX01
  p1 = refl

  p2 : CCX01 • X2 ≈ CCX01 • X2
  p2 = refl

  p3 : X2 • CCX01 ≈ CCX01 • X2
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX01 • X2 ≈ X2 • CCX01
  p4 = sym p3

  proved : CCX01 • X2 ≈ X2 • CCX01
  proved = p4

module KB0031 where

  p0 : CCX01 • CX12 ≈ CX12 • CCX01
  p0 = drel55.proved

  p1 : CCX01 • CX12 ≈ CCX01 • CX12
  p1 = refl

  p2 : CX12 • CCX01 ≈ CX12 • CCX01
  p2 = refl

  p3 : CCX01 • CX12 ≈ CX12 • CCX01
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX01 • CX12 ≈ CX12 • CCX01
  proved = p3

module KB0036 where

  p0 : X2 • CX12 ≈ CX12 • X2
  p0 = drel84.proved

  p1 : X2 • CX12 ≈ X2 • CX12
  p1 = refl

  p2 : CX12 • X2 ≈ CX12 • X2
  p2 = refl

  p3 : X2 • CX12 ≈ CX12 • X2
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX12 • X2 ≈ X2 • CX12
  p4 = sym p3

  proved : CX12 • X2 ≈ X2 • CX12
  proved = p4

module KB0116 where

  p0 : X1 • CX12 ≈ CX12 • X2 • X1
  p0 = drel69.proved

  p1 : X1 • CX12 ≈ X1 • CX12
  p1 = refl

  p2 : CX12 • X2 • X1 ≈ X2 • CX12 • X1
  p2 = by-assoc-and (under (ε) (X1) KB0036.proved) Eq.refl Eq.refl

  p3 : CX12 • X2 • X1 ≈ X2 • CX12 • X1
  p3 = trans p2 (refl)

  p4 : X1 • CX12 ≈ X2 • CX12 • X1
  p4 = trans (sym p1) (trans p0 p3)

  p5 : X2 • CX12 • X1 ≈ X1 • CX12
  p5 = sym p4

  proved : X2 • CX12 • X1 ≈ X1 • CX12
  proved = p5

module KB0144 where

  p0 : X2 • CX12 • X1 • X1 ≈ X1 • CX12 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0116.proved) Eq.refl Eq.refl

  p1 : X2 • CX12 • X1 • X1 ≈ X2 • CX12
  p1 = by-assoc-and (under (X2 • CX12) (ε) KB0003.proved) Eq.refl Eq.refl

  p2 : X1 • CX12 • X1 ≈ X2 • CX12
  p2 = trans (sym p0) p1

  p3 : X1 • CX12 • X1 ≈ X1 • CX12 • X1
  p3 = refl

  p4 : X2 • CX12 ≈ X2 • CX12
  p4 = refl

  p5 : X1 • CX12 • X1 ≈ X2 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CX12 • X1 ≈ X2 • CX12
  proved = p5

module KB0795 where

  p0 : CX02 • CCX01 • X1 • CX12 • X1 ≈ CX02 • CCX01 • X2 • CX12
  p0 = by-assoc-and (under (CX02 • CCX01) (ε) KB0144.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • CX12 • X1 ≈ X1 • CCX01 • CX12 • X1
  p1 = by-assoc-and (under (ε) (CX12 • X1) KB0120.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • X2 • CX12 ≈ X1 • CCX01 • CX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • X2 • CX12 ≈ CX02 • X2 • CCX01 • CX12
  p3 = by-assoc-and (under (CX02) (CX12) KB0029.proved) Eq.refl Eq.refl

  p4 : CX02 • X2 • CCX01 • CX12 ≈ X2 • CX02 • CCX01 • CX12
  p4 = by-assoc-and (under (ε) (CCX01 • CX12) KB0033.proved) Eq.refl Eq.refl

  p5 : X2 • CX02 • CCX01 • CX12 ≈ X2 • CX02 • CX12 • CCX01
  p5 = by-assoc-and (under (X2 • CX02) (ε) KB0031.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX01 • X2 • CX12 ≈ X2 • CX02 • CX12 • CCX01
  p6 = trans p3 (trans p4 (trans p5 (refl)))

  p7 : X1 • CCX01 • CX12 • X1 ≈ X1 • CX12 • CCX01 • X1
  p7 = by-assoc-and (under (X1) (X1) KB0031.proved) Eq.refl Eq.refl

  p8 : X1 • CCX01 • CX12 • X1 ≈ X1 • CX12 • CCX01 • X1
  p8 = trans p7 (refl)

  p9 : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
  p9 = trans (sym p6) (trans p2 p8)

  proved : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
  proved = p9

module KB0121 where

  p0 : X0 • CX12 • CCX01 ≈ CCX01 • X0
  p0 = drel98.proved

  p1 : X0 • CX12 • CCX01 ≈ X0 • CX12 • CCX01
  p1 = refl

  p2 : CCX01 • X0 ≈ CCX01 • X0
  p2 = refl

  p3 : X0 • CX12 • CCX01 ≈ CCX01 • X0
  p3 = trans (sym p1) (trans p0 p2)

  proved : X0 • CX12 • CCX01 ≈ CCX01 • X0
  proved = p3

module KB0153 where

  p0 : X0 • X0 • CX12 • CCX01 ≈ X0 • CCX01 • X0
  p0 = by-assoc-and (under (X0) (ε) KB0121.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • CX12 • CCX01 ≈ CX12 • CCX01
  p1 = by-assoc-and (under (ε) (CX12 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • X0 ≈ CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • CCX01 • X0 ≈ X0 • CCX01 • X0
  p3 = refl

  p4 : CX12 • CCX01 ≈ CX12 • CCX01
  p4 = refl

  p5 : X0 • CCX01 • X0 ≈ CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CCX01 • X0 ≈ CX12 • CCX01
  proved = p5

module KB0817 where

  p0 : X0 • CCX01 • X0 • X2 • CX02 ≈ CX12 • CCX01 • X2 • CX02
  p0 = by-assoc-and (under (ε) (X2 • CX02) KB0153.proved) Eq.refl Eq.refl

  p1 : X0 • CCX01 • X0 • X2 • CX02 ≈ X0 • CCX01 • CX02 • X0
  p1 = by-assoc-and (under (X0 • CCX01) (ε) KB0125.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • X2 • CX02 ≈ X0 • CCX01 • CX02 • X0
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX01 • X2 • CX02 ≈ CX12 • X2 • CCX01 • CX02
  p3 = by-assoc-and (under (CX12) (CX02) KB0029.proved) Eq.refl Eq.refl

  p4 : CX12 • X2 • CCX01 • CX02 ≈ X2 • CX12 • CCX01 • CX02
  p4 = by-assoc-and (under (ε) (CCX01 • CX02) KB0036.proved) Eq.refl Eq.refl

  p5 : X2 • CX12 • CCX01 • CX02 ≈ X2 • CX12 • CX02 • CCX01
  p5 = by-assoc-and (under (X2 • CX12) (ε) KB0037.proved) Eq.refl Eq.refl

  p6 : X2 • CX12 • CX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX01
  p6 = by-assoc-and (under (X2) (CCX01) KB0027.proved) Eq.refl Eq.refl

  p7 : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
  p7 = by-assoc-and (under (ε) (ε) KB0795.proved) Eq.refl Eq.refl

  p8 : CX12 • CCX01 • X2 • CX02 ≈ X1 • CX12 • CCX01 • X1
  p8 = trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (refl)))))

  p9 : X0 • CCX01 • CX02 • X0 ≈ X0 • CX02 • CCX01 • X0
  p9 = by-assoc-and (under (X0) (X0) KB0037.proved) Eq.refl Eq.refl

  p10 : X0 • CCX01 • CX02 • X0 ≈ X0 • CX02 • CCX01 • X0
  p10 = trans p9 (refl)

  p11 : X1 • CX12 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0
  p11 = trans (sym p8) (trans p2 p10)

  proved : X1 • CX12 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0
  proved = p11

module KB0014 where

  p0 : CCX12 • CCX12 ≈ ε
  p0 = by-assoc-and (axiom r024) Eq.refl Eq.refl

  p1 : CCX12 • CCX12 ≈ CCX12 • CCX12
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CCX12 • CCX12 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX12 • CCX12 ≈ ε
  proved = p3

module KB0215 where

  p0 : CX10 • CCX02 • CX10 ≈ CCX12 • CCX02 • CCX12
  p0 = cadd6.proved

  p1 : CX10 • CCX02 • CX10 ≈ CX10 • CCX02 • CX10
  p1 = refl

  p2 : CCX12 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CCX12
  p2 = refl

  p3 : CX10 • CCX02 • CX10 ≈ CCX12 • CCX02 • CCX12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
  p4 = sym p3

  proved : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
  proved = p4

module KB0219 where

  p0 : CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX12
  p0 = cflip2.proved

  p1 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (ε) KB0216.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01
  p2 = trans p1 (refl)

  p3 : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
  p3 = by-assoc-and (under (ε) (ε) KB0215.proved) Eq.refl Eq.refl

  p4 : CCX12 • CCX02 • CCX12 ≈ CX10 • CCX02 • CX10
  p4 = trans p3 (refl)

  p5 : CX01 • CCX12 • CX01 ≈ CX10 • CCX02 • CX10
  p5 = trans (sym p2) (trans p0 p4)

  p6 : CX10 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01
  p6 = sym p5

  proved : CX10 • CCX02 • CX10 ≈ CX01 • CCX12 • CX01
  proved = p6

module KB0338 where

  p0 : CCX12 • CCX02 • CCX12 • CCX12 ≈ CX10 • CCX02 • CX10 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0215.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CCX12 • CCX12 ≈ CCX12 • CCX02
  p1 = by-assoc-and (under (CCX12 • CCX02) (ε) KB0014.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CX10 • CCX12 ≈ CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CX10 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX12
  p3 = by-assoc-and (under (ε) (CCX12) KB0219.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX02 • CX10 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX12
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX02 ≈ CCX12 • CCX02
  p5 = refl

  p6 : CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX02
  proved = p6

module KB0006 where

  p0 : CX12 • CX12 ≈ ε
  p0 = elim_CX12.proved

  p1 : CX12 • CX12 ≈ CX12 • CX12
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX12 • CX12 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX12 • CX12 ≈ ε
  proved = p3

module KB0026 where

  p0 : CX10 • CX12 ≈ CX12 • CX10
  p0 = drel10.proved

  p1 : CX10 • CX12 ≈ CX10 • CX12
  p1 = refl

  p2 : CX12 • CX10 ≈ CX12 • CX10
  p2 = refl

  p3 : CX10 • CX12 ≈ CX12 • CX10
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX12 • CX10 ≈ CX10 • CX12
  p4 = sym p3

  proved : CX12 • CX10 ≈ CX10 • CX12
  proved = p4

module KB0118 where

  p0 : CX10 • CCX01 ≈ CCX01 • CX12 • CX10
  p0 = drel90.proved

  p1 : CX10 • CCX01 ≈ CX10 • CCX01
  p1 = refl

  p2 : CCX01 • CX12 • CX10 ≈ CX12 • CCX01 • CX10
  p2 = by-assoc-and (under (ε) (CX10) KB0031.proved) Eq.refl Eq.refl

  p3 : CCX01 • CX12 • CX10 ≈ CX12 • CCX01 • CX10
  p3 = trans p2 (refl)

  p4 : CX10 • CCX01 ≈ CX12 • CCX01 • CX10
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX12 • CCX01 • CX10 ≈ CX10 • CCX01
  p5 = sym p4

  proved : CX12 • CCX01 • CX10 ≈ CX10 • CCX01
  proved = p5

module KB0147 where

  p0 : CX12 • CX12 • CCX01 • CX10 ≈ CX12 • CX10 • CCX01
  p0 = by-assoc-and (under (CX12) (ε) KB0118.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX01 • CX10 ≈ CCX01 • CX10
  p1 = by-assoc-and (under (ε) (CCX01 • CX10) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CX10 • CCX01 ≈ CCX01 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CX10 • CCX01 ≈ CX10 • CX12 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0026.proved) Eq.refl Eq.refl

  p4 : CX12 • CX10 • CCX01 ≈ CX10 • CX12 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • CX10 ≈ CCX01 • CX10
  p5 = refl

  p6 : CX10 • CX12 • CCX01 ≈ CCX01 • CX10
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX10 • CX12 • CCX01 ≈ CCX01 • CX10
  proved = p6

module KB0213 where

  p0 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
  p0 = cadd4.proved

  p1 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • CX21
  p1 = refl

  p2 : CCX02 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02
  p2 = refl

  p3 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX02 • CCX01 • CCX02 ≈ CX21 • CCX01 • CX21
  p4 = sym p3

  proved : CCX02 • CCX01 • CCX02 ≈ CX21 • CCX01 • CX21
  proved = p4

module KB0217 where

  p0 : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
  p0 = cflip0.proved

  p1 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • CX21
  p1 = refl

  p2 : CX12 • CCX02 • CX12 ≈ CX12 • CCX02 • CX12
  p2 = refl

  p3 : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
  proved = p3

module KB0307 where

  p0 : CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (axiom r046) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 ≈ CCX01 • CCX02
  p1 = refl

  p2 : CCX02 • CCX01 • CCX02 • CCX01 ≈ CX21 • CCX01 • CX21 • CCX01
  p2 = by-assoc-and (under (ε) (CCX01) KB0213.proved) Eq.refl Eq.refl

  p3 : CX21 • CCX01 • CX21 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0217.proved) Eq.refl Eq.refl

  p4 : CCX02 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01
  p4 = trans p2 (trans p3 (refl))

  p5 : CCX01 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX01
  p5 = trans (sym p1) (trans p0 p4)

  p6 : CX12 • CCX02 • CX12 • CCX01 ≈ CCX01 • CCX02
  p6 = sym p5

  proved : CX12 • CCX02 • CX12 • CCX01 ≈ CCX01 • CCX02
  proved = p6

module KB0308 where

  p0 : CX12 • CX12 • CCX02 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02
  p0 = by-assoc-and (under (CX12) (ε) KB0307.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX02 • CX12 • CCX01 ≈ CCX02 • CX12 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX01) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX01 • CCX02 ≈ CX12 • CCX01 • CCX02
  p3 = refl

  p4 : CCX02 • CX12 • CCX01 ≈ CCX02 • CX12 • CCX01
  p4 = refl

  p5 : CX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX02 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02
  proved = p6

module KB0624 where

  p0 : CCX02 • CX12 • CCX01 • CX10 ≈ CX12 • CCX01 • CCX02 • CX10
  p0 = by-assoc-and (under (ε) (CX10) KB0308.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CCX01 • CX10 ≈ CCX02 • CX10 • CCX01
  p1 = by-assoc-and (under (CCX02) (ε) KB0118.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX01 • CCX02 • CX10
  p3 = refl

  p4 : CCX02 • CX10 • CCX01 ≈ CCX02 • CX10 • CCX01
  p4 = refl

  p5 : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
  proved = p5

module KB1335 where

  p0 : CX10 • CX12 • CCX01 • CCX02 • CX10 ≈ CX10 • CCX02 • CX10 • CCX01
  p0 = by-assoc-and (under (CX10) (ε) KB0624.proved) Eq.refl Eq.refl

  p1 : CX10 • CX12 • CCX01 • CCX02 • CX10 ≈ CCX01 • CX10 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CCX02 • CX10) KB0147.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX02 • CX10 • CCX01 ≈ CCX01 • CX10 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX02 • CX10 • CCX01 ≈ CX01 • CCX12 • CX01 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0219.proved) Eq.refl Eq.refl

  p4 : CX10 • CCX02 • CX10 • CCX01 ≈ CX01 • CCX12 • CX01 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • CX10 • CCX02 • CX10 ≈ CCX01 • CX01 • CCX12 • CX01
  p5 = by-assoc-and (under (CCX01) (ε) KB0219.proved) Eq.refl Eq.refl

  p6 : CCX01 • CX10 • CCX02 • CX10 ≈ CCX01 • CX01 • CCX12 • CX01
  p6 = trans p5 (refl)

  p7 : CX01 • CCX12 • CX01 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX01
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CCX01 • CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01 • CCX01
  p8 = sym p7

  proved : CCX01 • CX01 • CCX12 • CX01 ≈ CX01 • CCX12 • CX01 • CCX01
  proved = p8

module KB1396 where

  p0 : CCX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB1335.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
  p1 = by-assoc-and (under (CCX01) (ε) KB0338.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CCX01 • CCX12
  p3 = refl

  p4 : CCX01 • CCX12 • CCX02 ≈ CCX01 • CCX12 • CCX02
  p4 = refl

  p5 : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CCX02
  proved = p5

module KB1397 where

  p0 : CX01 • CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CX01 • CCX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX01) (ε) KB1396.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX12 • CX01 • CCX01 • CCX12 ≈ CCX12 • CX01 • CCX01 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX01 • CCX01 • CCX12) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CCX12 • CCX02 ≈ CX01 • CCX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX12 • CX01 • CCX01 • CCX12 ≈ CCX12 • CX01 • CCX01 • CCX12
  p4 = refl

  p5 : CX01 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX01 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CX01 • CCX01 • CCX12 ≈ CX01 • CCX01 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX12 • CX01 • CCX01 • CCX12 ≈ CX01 • CCX01 • CCX12 • CCX02
  proved = p6

module KB0009 where

  p0 : CX20 • CX20 ≈ ε
  p0 = elim_CX20.proved

  p1 : CX20 • CX20 ≈ CX20 • CX20
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX20 • CX20 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX20 • CX20 ≈ ε
  proved = p3

module KB0136 where

  p0 : CX20 • CCX02 ≈ CCX02 • CX21 • CX20
  p0 = drel140.proved

  p1 : CX20 • CCX02 ≈ CX20 • CCX02
  p1 = refl

  p2 : CCX02 • CX21 • CX20 ≈ CX21 • CCX02 • CX20
  p2 = by-assoc-and (under (ε) (CX20) KB0039.proved) Eq.refl Eq.refl

  p3 : CCX02 • CX21 • CX20 ≈ CX21 • CCX02 • CX20
  p3 = trans p2 (refl)

  p4 : CX20 • CCX02 ≈ CX21 • CCX02 • CX20
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX21 • CCX02 • CX20 ≈ CX20 • CCX02
  p5 = sym p4

  proved : CX21 • CCX02 • CX20 ≈ CX20 • CCX02
  proved = p5

module KB0177 where

  p0 : CX21 • CCX02 • CX20 • CX20 ≈ CX20 • CCX02 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0136.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • CX20 • CX20 ≈ CX21 • CCX02
  p1 = by-assoc-and (under (CX21 • CCX02) (ε) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX02 • CX20 ≈ CX20 • CCX02 • CX20
  p3 = refl

  p4 : CX21 • CCX02 ≈ CX21 • CCX02
  p4 = refl

  p5 : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
  proved = p5

module KB0040 where

  p0 : CCX12 • CX20 ≈ CX20 • CCX12
  p0 = drel94.proved

  p1 : CCX12 • CX20 ≈ CCX12 • CX20
  p1 = refl

  p2 : CX20 • CCX12 ≈ CX20 • CCX12
  p2 = refl

  p3 : CCX12 • CX20 ≈ CX20 • CCX12
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX12 • CX20 ≈ CX20 • CCX12
  proved = p3
