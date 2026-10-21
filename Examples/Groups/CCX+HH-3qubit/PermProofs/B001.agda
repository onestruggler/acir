{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B001 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX12 ; CX20 ; CX21 ; SWAP02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r010 ; r029 ; r032 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0008 ; module KB0010 ; module KB0011 ; module KB0013 ; module KB0029 ; module KB0031 ; module KB0033 ; module KB0035 ; module KB0037 ; module KB0039 ; module KB0040 ; module KB0046 ; module KB0120 ; module KB0129 ; module KB0136 ; module KB0139 ; module KB0144 ; module KB0153 ; module KB0164 ; module KB0177 ; module KB0213 ; module KB0308 ; module KB0780 ; module KB0795 ; module KB0817)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module bifunct_X_CX_b ; module bifunct_X_CX_d ; module elim_CX21 ; module elim_SWAP02)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module drel110 ; module drel41 ; module drel9)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module cadd0 ; module cadd3 ; module drel141)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module cflip1 ; module drel101 ; module drel103 ; module drel105 ; module drel126)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B007 using (module drel183 ; module drel92)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B008 using (module drel95)

module KB0002 where

  p0 : SWAP02 • SWAP02 ≈ ε
  p0 = elim_SWAP02.proved

  p1 : SWAP02 • SWAP02 ≈ SWAP02 • SWAP02
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : SWAP02 • SWAP02 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : SWAP02 • SWAP02 ≈ ε
  proved = p3

module KB0084 where

  p0 : SWAP02 ≈ CX02 • CX20 • CX02
  p0 = by-assoc-and (axiom r010) Eq.refl Eq.refl

  p1 : SWAP02 ≈ SWAP02
  p1 = refl

  p2 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02
  p2 = refl

  p3 : SWAP02 ≈ CX02 • CX20 • CX02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX02 • CX20 • CX02 ≈ SWAP02
  p4 = sym p3

  proved : CX02 • CX20 • CX02 ≈ SWAP02
  proved = p4

module KB0086 where

  p0 : CX02 • CX20 • CX02 • CX02 ≈ SWAP02 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0084.proved) Eq.refl Eq.refl

  p1 : CX02 • CX20 • CX02 • CX02 ≈ CX02 • CX20
  p1 = by-assoc-and (under (CX02 • CX20) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : SWAP02 • CX02 ≈ CX02 • CX20
  p2 = trans (sym p0) p1

  p3 : SWAP02 • CX02 ≈ SWAP02 • CX02
  p3 = refl

  p4 : CX02 • CX20 ≈ CX02 • CX20
  p4 = refl

  p5 : SWAP02 • CX02 ≈ CX02 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP02 • CX02 ≈ CX02 • CX20
  proved = p5

module KB0098 where

  p0 : CX20 ≈ SWAP02 • CX02 • SWAP02
  p0 = by-assoc-and (axiom r029) Eq.refl Eq.refl

  p1 : CX20 ≈ CX20
  p1 = refl

  p2 : SWAP02 • CX02 • SWAP02 ≈ CX02 • CX20 • SWAP02
  p2 = by-assoc-and (under (ε) (SWAP02) KB0086.proved) Eq.refl Eq.refl

  p3 : SWAP02 • CX02 • SWAP02 ≈ CX02 • CX20 • SWAP02
  p3 = trans p2 (refl)

  p4 : CX20 ≈ CX02 • CX20 • SWAP02
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX02 • CX20 • SWAP02 ≈ CX20
  p5 = sym p4

  proved : CX02 • CX20 • SWAP02 ≈ CX20
  proved = p5

module KB0099 where

  p0 : CX02 • CX20 • SWAP02 • SWAP02 ≈ CX20 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0098.proved) Eq.refl Eq.refl

  p1 : CX02 • CX20 • SWAP02 • SWAP02 ≈ CX02 • CX20
  p1 = by-assoc-and (under (CX02 • CX20) (ε) KB0002.proved) Eq.refl Eq.refl

  p2 : CX20 • SWAP02 ≈ CX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CX20 • SWAP02 ≈ CX20 • SWAP02
  p3 = refl

  p4 : CX02 • CX20 ≈ CX02 • CX20
  p4 = refl

  p5 : CX20 • SWAP02 ≈ CX02 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • SWAP02 ≈ CX02 • CX20
  proved = p5

module KB0271 where

  p0 : CCX12 • CX20 • SWAP02 ≈ CCX12 • CX02 • CX20
  p0 = by-assoc-and (under (CCX12) (ε) KB0099.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX20 • SWAP02 ≈ CX20 • CCX12 • SWAP02
  p1 = by-assoc-and (under (ε) (SWAP02) KB0040.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX02 • CX20 ≈ CCX12 • CX02 • CX20
  p3 = refl

  p4 : CX20 • CCX12 • SWAP02 ≈ CX20 • CCX12 • SWAP02
  p4 = refl

  p5 : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • CX02 • CX20 ≈ CX20 • CCX12 • SWAP02
  proved = p5

module KB0103 where

  p0 : CCX01 ≈ SWAP02 • CCX12 • SWAP02
  p0 = by-assoc-and (axiom r032) Eq.refl Eq.refl

  p1 : CCX01 ≈ CCX01
  p1 = refl

  p2 : SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02
  p2 = refl

  p3 : CCX01 ≈ SWAP02 • CCX12 • SWAP02
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP02 • CCX12 • SWAP02 ≈ CCX01
  p4 = sym p3

  proved : SWAP02 • CCX12 • SWAP02 ≈ CCX01
  proved = p4

module KB0276 where

  p0 : CX02 • CX20 • SWAP02 • CCX12 • SWAP02 ≈ CX02 • CX20 • CCX01
  p0 = by-assoc-and (under (CX02 • CX20) (ε) KB0103.proved) Eq.refl Eq.refl

  p1 : CX02 • CX20 • SWAP02 • CCX12 • SWAP02 ≈ CX20 • CCX12 • SWAP02
  p1 = by-assoc-and (under (ε) (CCX12 • SWAP02) KB0098.proved) Eq.refl Eq.refl

  p2 : CX02 • CX20 • CCX01 ≈ CX20 • CCX12 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX02 • CX20 • CCX01 ≈ CX02 • CX20 • CCX01
  p3 = refl

  p4 : CX20 • CCX12 • SWAP02 ≈ CX20 • CCX12 • SWAP02
  p4 = refl

  p5 : CX02 • CX20 • CCX01 ≈ CX20 • CCX12 • SWAP02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX20 • CCX12 • SWAP02 ≈ CX02 • CX20 • CCX01
  p6 = sym p5

  proved : CX20 • CCX12 • SWAP02 ≈ CX02 • CX20 • CCX01
  proved = p6

module KB1569 where

  p0 : CCX12 • CX02 • CX20 • CCX02 • CX20 ≈ CX20 • CCX12 • SWAP02 • CCX02 • CX20
  p0 = by-assoc-and (under (ε) (CCX02 • CX20) KB0271.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX02 • CX20 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
  p1 = by-assoc-and (under (CCX12 • CX02) (ε) KB0177.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CX02 • CX20 • CCX01 • CCX02 • CX20
  p3 = by-assoc-and (under (ε) (CCX02 • CX20) KB0276.proved) Eq.refl Eq.refl

  p4 : CX20 • CCX12 • SWAP02 • CCX02 • CX20 ≈ CX02 • CX20 • CCX01 • CCX02 • CX20
  p4 = trans p3 (refl)

  p5 : CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CX02 • CX21 • CCX02
  p5 = refl

  p6 : CX02 • CX20 • CCX01 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX02 • CX20 • CCX01 • CCX02 • CX20 ≈ CCX12 • CX02 • CX21 • CCX02
  proved = p6

module KB0123 where

  p0 : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
  p0 = drel103.proved

  p1 : CCX01 • CX01 ≈ CCX01 • CX01
  p1 = refl

  p2 : CX01 • CX02 • CCX01 ≈ CX01 • CX02 • CCX01
  p2 = refl

  p3 : CCX01 • CX01 ≈ CX01 • CX02 • CCX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX01 • CX02 • CCX01 ≈ CCX01 • CX01
  p4 = sym p3

  proved : CX01 • CX02 • CCX01 ≈ CCX01 • CX01
  proved = p4

module KB0282 where

  p0 : CX01 • CX02 • CCX01 • X1 ≈ CCX01 • CX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0123.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX01 • X1 ≈ CX01 • X1 • CCX01
  p1 = by-assoc-and (under (CX01) (ε) KB0120.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • X1 ≈ CX01 • X1 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • X1 ≈ CCX01 • X1 • CX01
  p3 = by-assoc-and (under (CCX01) (ε) KB0035.proved) Eq.refl Eq.refl

  p4 : CCX01 • CX01 • X1 ≈ CCX01 • X1 • CX01
  p4 = trans p3 (refl)

  p5 : CX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01
  p5 = by-assoc-and (under (ε) (CCX01) KB0035.proved) Eq.refl Eq.refl

  p6 : CX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01
  p6 = trans p5 (refl)

  p7 : CCX01 • X1 • CX01 ≈ X1 • CX01 • CCX01
  p7 = trans (sym p4) (trans p2 p6)

  proved : CCX01 • X1 • CX01 ≈ X1 • CX01 • CCX01
  proved = p7

module KB0394 where

  p0 : CX01 • CX02 • CCX01 • CX12 ≈ CCX01 • CX01 • CX12
  p0 = by-assoc-and (under (ε) (CX12) KB0123.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX01 • CX12 ≈ CX01 • CX02 • CX12 • CCX01
  p1 = by-assoc-and (under (CX01 • CX02) (ε) KB0031.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CX12 ≈ CX01 • CX02 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CX12 ≈ CCX01 • CX01 • CX12
  p3 = refl

  p4 : CX01 • CX02 • CX12 • CCX01 ≈ CX12 • CX01 • CCX01
  p4 = by-assoc-and (under (ε) (CCX01) KB0164.proved) Eq.refl Eq.refl

  p5 : CX01 • CX02 • CX12 • CCX01 ≈ CX12 • CX01 • CCX01
  p5 = trans p4 (refl)

  p6 : CCX01 • CX01 • CX12 ≈ CX12 • CX01 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX01 • CX01 • CX12 ≈ CX12 • CX01 • CCX01
  proved = p6

module KB0022 where

  p0 : CX01 • X2 ≈ X2 • CX01
  p0 = bifunct_X_CX_d.proved

  p1 : CX01 • X2 ≈ CX01 • X2
  p1 = refl

  p2 : X2 • CX01 ≈ X2 • CX01
  p2 = refl

  p3 : CX01 • X2 ≈ X2 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX01 • X2 ≈ X2 • CX01
  proved = p3

module KB0460 where

  p0 : CX01 • X1 • CX12 • X1 ≈ CX01 • X2 • CX12
  p0 = by-assoc-and (under (CX01) (ε) KB0144.proved) Eq.refl Eq.refl

  p1 : CX01 • X1 • CX12 • X1 ≈ X1 • CX01 • CX12 • X1
  p1 = by-assoc-and (under (ε) (CX12 • X1) KB0035.proved) Eq.refl Eq.refl

  p2 : CX01 • X2 • CX12 ≈ X1 • CX01 • CX12 • X1
  p2 = trans (sym p0) p1

  p3 : CX01 • X2 • CX12 ≈ X2 • CX01 • CX12
  p3 = by-assoc-and (under (ε) (CX12) KB0022.proved) Eq.refl Eq.refl

  p4 : CX01 • X2 • CX12 ≈ X2 • CX01 • CX12
  p4 = trans p3 (refl)

  p5 : X1 • CX01 • CX12 • X1 ≈ X1 • CX01 • CX12 • X1
  p5 = refl

  p6 : X2 • CX01 • CX12 ≈ X1 • CX01 • CX12 • X1
  p6 = trans (sym p4) (trans p2 p5)

  p7 : X1 • CX01 • CX12 • X1 ≈ X2 • CX01 • CX12
  p7 = sym p6

  proved : X1 • CX01 • CX12 • X1 ≈ X2 • CX01 • CX12
  proved = p7

module KB0819 where

  p0 : X1 • CX01 • X0 • CCX01 • X0 ≈ X1 • CX01 • CX12 • CCX01
  p0 = by-assoc-and (under (X1 • CX01) (ε) KB0153.proved) Eq.refl Eq.refl

  p1 : X1 • CX01 • X0 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX01 • X0) KB0139.proved) Eq.refl Eq.refl

  p2 : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : X1 • CX01 • CX12 • CCX01 ≈ X1 • CX01 • CX12 • CCX01
  p3 = refl

  p4 : X0 • CX01 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • X0
  p4 = refl

  p5 : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CX01 • CX12 • CCX01 ≈ X0 • CX01 • CCX01 • X0
  proved = p5

module KB0157 where

  p0 : CX01 • CX01 • CX02 • CCX01 ≈ CX01 • CCX01 • CX01
  p0 = by-assoc-and (under (CX01) (ε) KB0123.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CX02 • CCX01 ≈ CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CX01 ≈ CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CX01 ≈ CX01 • CCX01 • CX01
  p3 = refl

  p4 : CX02 • CCX01 ≈ CX02 • CCX01
  p4 = refl

  p5 : CX01 • CCX01 • CX01 ≈ CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX01 • CX01 ≈ CX02 • CCX01
  proved = p5

module KB0124 where

  p0 : X0 • X1 • CX01 ≈ CX01 • X0
  p0 = drel105.proved

  p1 : X0 • X1 • CX01 ≈ X0 • X1 • CX01
  p1 = refl

  p2 : CX01 • X0 ≈ CX01 • X0
  p2 = refl

  p3 : X0 • X1 • CX01 ≈ CX01 • X0
  p3 = trans (sym p1) (trans p0 p2)

  proved : X0 • X1 • CX01 ≈ CX01 • X0
  proved = p3

module KB0159 where

  p0 : X0 • X1 • CX01 • CX01 ≈ CX01 • X0 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0124.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX01 • CX01 ≈ X0 • X1
  p1 = by-assoc-and (under (X0 • X1) (ε) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CX01 ≈ X0 • X1
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CX01 ≈ CX01 • X0 • CX01
  p3 = refl

  p4 : X0 • X1 ≈ X0 • X1
  p4 = refl

  p5 : CX01 • X0 • CX01 ≈ X0 • X1
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • CX01 ≈ X0 • X1
  proved = p5

module KB0831 where

  p0 : CX01 • CCX01 • CX01 • X0 • CX01 ≈ CX01 • CCX01 • X0 • X1
  p0 = by-assoc-and (under (CX01 • CCX01) (ε) KB0159.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX01 • CX01 • X0 • CX01 ≈ CX02 • CCX01 • X0 • CX01
  p1 = by-assoc-and (under (ε) (X0 • CX01) KB0157.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • X0 • X1 ≈ CX02 • CCX01 • X0 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • X0 • X1 ≈ CX01 • CCX01 • X0 • X1
  p3 = refl

  p4 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
  p4 = by-assoc-and (under (ε) (ε) KB0780.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX01 • X0 • CX01 ≈ X1 • CCX01 • CX01 • X0
  p5 = trans p4 (refl)

  p6 : CX01 • CCX01 • X0 • X1 ≈ X1 • CCX01 • CX01 • X0
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX01 • CCX01 • X0 • X1 ≈ X1 • CCX01 • CX01 • X0
  proved = p6

module KB2158 where

  p0 : CCX01 • X1 • CX01 • CX12 • X1 ≈ CCX01 • X2 • CX01 • CX12
  p0 = by-assoc-and (under (CCX01) (ε) KB0460.proved) Eq.refl Eq.refl

  p1 : CCX01 • X1 • CX01 • CX12 • X1 ≈ X1 • CX01 • CCX01 • CX12 • X1
  p1 = by-assoc-and (under (ε) (CX12 • X1) KB0282.proved) Eq.refl Eq.refl

  p2 : CCX01 • X2 • CX01 • CX12 ≈ X1 • CX01 • CCX01 • CX12 • X1
  p2 = trans (sym p0) p1

  p3 : CCX01 • X2 • CX01 • CX12 ≈ X2 • CCX01 • CX01 • CX12
  p3 = by-assoc-and (under (ε) (CX01 • CX12) KB0029.proved) Eq.refl Eq.refl

  p4 : X2 • CCX01 • CX01 • CX12 ≈ X2 • CX12 • CX01 • CCX01
  p4 = by-assoc-and (under (X2) (ε) KB0394.proved) Eq.refl Eq.refl

  p5 : CCX01 • X2 • CX01 • CX12 ≈ X2 • CX12 • CX01 • CCX01
  p5 = trans p3 (trans p4 (refl))

  p6 : X1 • CX01 • CCX01 • CX12 • X1 ≈ X1 • CX01 • CX12 • CCX01 • X1
  p6 = by-assoc-and (under (X1 • CX01) (X1) KB0031.proved) Eq.refl Eq.refl

  p7 : X1 • CX01 • CX12 • CCX01 • X1 ≈ X0 • CX01 • CCX01 • X0 • X1
  p7 = by-assoc-and (under (ε) (X1) KB0819.proved) Eq.refl Eq.refl

  p8 : X0 • CX01 • CCX01 • X0 • X1 ≈ X0 • X1 • CCX01 • CX01 • X0
  p8 = by-assoc-and (under (X0) (ε) KB0831.proved) Eq.refl Eq.refl

  p9 : X1 • CX01 • CCX01 • CX12 • X1 ≈ X0 • X1 • CCX01 • CX01 • X0
  p9 = trans p6 (trans p7 (trans p8 (refl)))

  p10 : X2 • CX12 • CX01 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • X0
  p10 = trans (sym p5) (trans p2 p9)

  p11 : X0 • X1 • CCX01 • CX01 • X0 ≈ X2 • CX12 • CX01 • CCX01
  p11 = sym p10

  proved : X0 • X1 • CCX01 • CX01 • X0 ≈ X2 • CX12 • CX01 • CCX01
  proved = p11

module KB0038 where

  p0 : CCX02 • CX01 ≈ CX01 • CCX02
  p0 = drel92.proved

  p1 : CCX02 • CX01 ≈ CCX02 • CX01
  p1 = refl

  p2 : CX01 • CCX02 ≈ CX01 • CCX02
  p2 = refl

  p3 : CCX02 • CX01 ≈ CX01 • CCX02
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX02 • CX01 ≈ CX01 • CCX02
  proved = p3

module KB0119 where

  p0 : CX02 • CCX02 ≈ CCX02 • CX01 • CX02
  p0 = drel95.proved

  p1 : CX02 • CCX02 ≈ CX02 • CCX02
  p1 = refl

  p2 : CCX02 • CX01 • CX02 ≈ CX01 • CCX02 • CX02
  p2 = by-assoc-and (under (ε) (CX02) KB0038.proved) Eq.refl Eq.refl

  p3 : CCX02 • CX01 • CX02 ≈ CX01 • CCX02 • CX02
  p3 = trans p2 (refl)

  p4 : CX02 • CCX02 ≈ CX01 • CCX02 • CX02
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX01 • CCX02 • CX02 ≈ CX02 • CCX02
  p5 = sym p4

  proved : CX01 • CCX02 • CX02 ≈ CX02 • CCX02
  proved = p5

module KB0025 where

  p0 : CX01 • CX02 ≈ CX02 • CX01
  p0 = drel9.proved

  p1 : CX01 • CX02 ≈ CX01 • CX02
  p1 = refl

  p2 : CX02 • CX01 ≈ CX02 • CX01
  p2 = refl

  p3 : CX01 • CX02 ≈ CX02 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX02 • CX01 ≈ CX01 • CX02
  p4 = sym p3

  proved : CX02 • CX01 ≈ CX01 • CX02
  proved = p4

module KB0030 where

  p0 : CX01 • CX21 ≈ CX21 • CX01
  p0 = drel41.proved

  p1 : CX01 • CX21 ≈ CX01 • CX21
  p1 = refl

  p2 : CX21 • CX01 ≈ CX21 • CX01
  p2 = refl

  p3 : CX01 • CX21 ≈ CX21 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX21 • CX01 ≈ CX01 • CX21
  p4 = sym p3

  proved : CX21 • CX01 ≈ CX01 • CX21
  proved = p4

module KB0126 where

  p0 : CX21 • CX02 ≈ CX02 • CX21 • CX01
  p0 = drel110.proved

  p1 : CX21 • CX02 ≈ CX21 • CX02
  p1 = refl

  p2 : CX02 • CX21 • CX01 ≈ CX02 • CX01 • CX21
  p2 = by-assoc-and (under (CX02) (ε) KB0030.proved) Eq.refl Eq.refl

  p3 : CX02 • CX01 • CX21 ≈ CX01 • CX02 • CX21
  p3 = by-assoc-and (under (ε) (CX21) KB0025.proved) Eq.refl Eq.refl

  p4 : CX02 • CX21 • CX01 ≈ CX01 • CX02 • CX21
  p4 = trans p2 (trans p3 (refl))

  p5 : CX21 • CX02 ≈ CX01 • CX02 • CX21
  p5 = trans (sym p1) (trans p0 p4)

  p6 : CX01 • CX02 • CX21 ≈ CX21 • CX02
  p6 = sym p5

  proved : CX01 • CX02 • CX21 ≈ CX21 • CX02
  proved = p6

module KB0407 where

  p0 : CCX02 • CX01 • CX02 • CX21 ≈ CCX02 • CX21 • CX02
  p0 = by-assoc-and (under (CCX02) (ε) KB0126.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX01 • CX02 • CX21 ≈ CX01 • CCX02 • CX02 • CX21
  p1 = by-assoc-and (under (ε) (CX02 • CX21) KB0038.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX21 • CX02 ≈ CX01 • CCX02 • CX02 • CX21
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX21 • CX02 ≈ CX21 • CCX02 • CX02
  p3 = by-assoc-and (under (ε) (CX02) KB0039.proved) Eq.refl Eq.refl

  p4 : CCX02 • CX21 • CX02 ≈ CX21 • CCX02 • CX02
  p4 = trans p3 (refl)

  p5 : CX01 • CCX02 • CX02 • CX21 ≈ CX02 • CCX02 • CX21
  p5 = by-assoc-and (under (ε) (CX21) KB0119.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX02 • CX21 ≈ CX02 • CX21 • CCX02
  p6 = by-assoc-and (under (CX02) (ε) KB0039.proved) Eq.refl Eq.refl

  p7 : CX01 • CCX02 • CX02 • CX21 ≈ CX02 • CX21 • CCX02
  p7 = trans p5 (trans p6 (refl))

  p8 : CX21 • CCX02 • CX02 ≈ CX02 • CX21 • CCX02
  p8 = trans (sym p4) (trans p2 p7)

  proved : CX21 • CCX02 • CX02 ≈ CX02 • CX21 • CCX02
  proved = p8

module KB0007 where

  p0 : CX21 • CX21 ≈ ε
  p0 = elim_CX21.proved

  p1 : CX21 • CX21 ≈ CX21 • CX21
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX21 • CX21 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX21 • CX21 ≈ ε
  proved = p3

module KB0020 where

  p0 : CX21 • X0 ≈ X0 • CX21
  p0 = bifunct_X_CX_b.proved

  p1 : CX21 • X0 ≈ CX21 • X0
  p1 = refl

  p2 : X0 • CX21 ≈ X0 • CX21
  p2 = refl

  p3 : CX21 • X0 ≈ X0 • CX21
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX21 • X0 ≈ X0 • CX21
  proved = p3

module KB0165 where

  p0 : CX21 • CX21 • CCX02 • X0 ≈ CX21 • X0 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0129.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX02 • X0 ≈ CCX02 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • X0) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • X0 • CCX02 ≈ CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : CX21 • X0 • CCX02 ≈ X0 • CX21 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0020.proved) Eq.refl Eq.refl

  p4 : CX21 • X0 • CCX02 ≈ X0 • CX21 • CCX02
  p4 = trans p3 (refl)

  p5 : CCX02 • X0 ≈ CCX02 • X0
  p5 = refl

  p6 : X0 • CX21 • CCX02 ≈ CCX02 • X0
  p6 = trans (sym p4) (trans p2 p5)

  proved : X0 • CX21 • CCX02 ≈ CCX02 • X0
  proved = p6

module KB0511 where

  p0 : CCX12 • X0 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
  p0 = by-assoc-and (under (CCX12) (ε) KB0165.proved) Eq.refl Eq.refl

  p1 : CCX12 • X0 • CX21 • CCX02 ≈ X0 • CCX12 • CX21 • CCX02
  p1 = by-assoc-and (under (ε) (CX21 • CCX02) KB0046.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX02 • X0 ≈ X0 • CCX12 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX02 • X0 ≈ CCX12 • CCX02 • X0
  p3 = refl

  p4 : X0 • CCX12 • CX21 • CCX02 ≈ X0 • CCX12 • CX21 • CCX02
  p4 = refl

  p5 : CCX12 • CCX02 • X0 ≈ X0 • CCX12 • CX21 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CCX12 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
  p6 = sym p5

  proved : X0 • CCX12 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0
  proved = p6

module KB2277 where

  p0 : X0 • CCX12 • CX21 • CCX02 • CX02 ≈ CCX12 • CCX02 • X0 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0511.proved) Eq.refl Eq.refl

  p1 : X0 • CCX12 • CX21 • CCX02 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
  p1 = by-assoc-and (under (X0 • CCX12) (ε) KB0407.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX02 • X0 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX02 • X0 • CX02 ≈ CCX12 • CCX02 • X0 • CX02
  p3 = refl

  p4 : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
  p4 = refl

  p5 : CCX12 • CCX02 • X0 • CX02 ≈ X0 • CCX12 • CX02 • CX21 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0 • CX02
  p6 = sym p5

  proved : X0 • CCX12 • CX02 • CX21 • CCX02 ≈ CCX12 • CCX02 • X0 • CX02
  proved = p6

module KB0211 where

  p0 : CX02 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX01
  p0 = cadd0.proved

  p1 : CX02 • CCX12 • CX02 ≈ CX02 • CCX12 • CX02
  p1 = refl

  p2 : CCX01 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CCX01
  p2 = refl

  p3 : CX02 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
  p4 = sym p3

  proved : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
  proved = p4

module KB0328 where

  p0 : CCX02 • CCX02 • CCX01 • CCX02 ≈ CCX02 • CX21 • CCX01 • CX21
  p0 = by-assoc-and (under (CCX02) (ε) KB0213.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX02 • CCX01 • CCX02 ≈ CCX01 • CCX02
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX21 • CCX01 • CX21 ≈ CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX21 • CCX01 • CX21 ≈ CX21 • CCX02 • CCX01 • CX21
  p3 = by-assoc-and (under (ε) (CCX01 • CX21) KB0039.proved) Eq.refl Eq.refl

  p4 : CCX02 • CX21 • CCX01 • CX21 ≈ CX21 • CCX02 • CCX01 • CX21
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX02 ≈ CCX01 • CCX02
  p5 = refl

  p6 : CX21 • CCX02 • CCX01 • CX21 ≈ CCX01 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX21 • CCX02 • CCX01 • CX21 ≈ CCX01 • CCX02
  proved = p6

module KB0330 where

  p0 : CX21 • CCX02 • CCX01 • CX21 • CX21 ≈ CCX01 • CCX02 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0328.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • CCX01 • CX21 • CX21 ≈ CX21 • CCX02 • CCX01
  p1 = by-assoc-and (under (CX21 • CCX02 • CCX01) (ε) KB0007.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • CX21 ≈ CX21 • CCX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX02 • CX21 ≈ CCX01 • CX21 • CCX02
  p3 = by-assoc-and (under (CCX01) (ε) KB0039.proved) Eq.refl Eq.refl

  p4 : CCX01 • CCX02 • CX21 ≈ CCX01 • CX21 • CCX02
  p4 = trans p3 (refl)

  p5 : CX21 • CCX02 • CCX01 ≈ CX21 • CCX02 • CCX01
  p5 = refl

  p6 : CCX01 • CX21 • CCX02 ≈ CX21 • CCX02 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX01 • CX21 • CCX02 ≈ CX21 • CCX02 • CCX01
  proved = p6

module KB0043 where

  p0 : CX21 • CX20 ≈ CX20 • CX21
  p0 = drel183.proved

  p1 : CX21 • CX20 ≈ CX21 • CX20
  p1 = refl

  p2 : CX20 • CX21 ≈ CX20 • CX21
  p2 = refl

  p3 : CX21 • CX20 ≈ CX20 • CX21
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX21 • CX20 ≈ CX20 • CX21
  proved = p3

module KB0176 where

  p0 : CX21 • CX21 • CCX02 • CX20 ≈ CX21 • CX20 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0136.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX02 • CX20 ≈ CCX02 • CX20
  p1 = by-assoc-and (under (ε) (CCX02 • CX20) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CX20 • CCX02 ≈ CCX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CX21 • CX20 • CCX02 ≈ CX20 • CX21 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB0043.proved) Eq.refl Eq.refl

  p4 : CX21 • CX20 • CCX02 ≈ CX20 • CX21 • CCX02
  p4 = trans p3 (refl)

  p5 : CCX02 • CX20 ≈ CCX02 • CX20
  p5 = refl

  p6 : CX20 • CX21 • CCX02 ≈ CCX02 • CX20
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX20 • CX21 • CCX02 ≈ CCX02 • CX20
  proved = p6

module KB0212 where

  p0 : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
  p0 = cadd3.proved

  p1 : CX20 • CCX01 • CX20 ≈ CX20 • CCX01 • CX20
  p1 = refl

  p2 : CCX12 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CCX12
  p2 = refl

  p3 : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
  p4 = sym p3

  proved : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
  proved = p4

module KB0218 where

  p0 : CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX12
  p0 = cflip1.proved

  p1 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (ε) KB0211.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02
  p2 = trans p1 (refl)

  p3 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
  p3 = by-assoc-and (under (ε) (ε) KB0212.proved) Eq.refl Eq.refl

  p4 : CCX12 • CCX01 • CCX12 ≈ CX20 • CCX01 • CX20
  p4 = trans p3 (refl)

  p5 : CX02 • CCX12 • CX02 ≈ CX20 • CCX01 • CX20
  p5 = trans (sym p2) (trans p0 p4)

  p6 : CX20 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02
  p6 = sym p5

  proved : CX20 • CCX01 • CX20 ≈ CX02 • CCX12 • CX02
  proved = p6

module KB1457 where

  p0 : CX20 • CCX01 • CX20 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
  p0 = by-assoc-and (under (ε) (CX21 • CCX02) KB0218.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX01 • CX20 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  p1 = by-assoc-and (under (CX20 • CCX01) (ε) KB0176.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
  p3 = refl

  p4 : CX20 • CCX01 • CCX02 • CX20 ≈ CX20 • CCX01 • CCX02 • CX20
  p4 = refl

  p5 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  proved = p5

module KB3195 where

  p0 : CCX01 • CCX12 • CCX01 • CX21 • CCX02 ≈ CCX01 • CCX12 • CX21 • CCX02 • CCX01
  p0 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0330.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX01 • CX21 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
  p1 = by-assoc-and (under (ε) (CX21 • CCX02) KB0211.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX02 • CCX01
  p3 = refl

  p4 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  p4 = by-assoc-and (under (ε) (ε) KB1457.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX12 • CX02 • CX21 • CCX02 ≈ CX20 • CCX01 • CCX02 • CX20
  p5 = trans p4 (refl)

  p6 : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX20 • CCX01 • CCX02 • CX20
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX01 • CCX12 • CX21 • CCX02 • CCX01 ≈ CX20 • CCX01 • CCX02 • CX20
  proved = p6

module KB0128 where

  p0 : X0 • CX02 ≈ CX02 • X2 • X0
  p0 = drel126.proved

  p1 : X0 • CX02 ≈ X0 • CX02
  p1 = refl

  p2 : CX02 • X2 • X0 ≈ X2 • CX02 • X0
  p2 = by-assoc-and (under (ε) (X0) KB0033.proved) Eq.refl Eq.refl

  p3 : CX02 • X2 • X0 ≈ X2 • CX02 • X0
  p3 = trans p2 (refl)

  p4 : X0 • CX02 ≈ X2 • CX02 • X0
  p4 = trans (sym p1) (trans p0 p3)

  p5 : X2 • CX02 • X0 ≈ X0 • CX02
  p5 = sym p4

  proved : X2 • CX02 • X0 ≈ X0 • CX02
  proved = p5

module KB0122 where

  p0 : X2 • CX01 • CCX02 ≈ CCX02 • X2
  p0 = drel101.proved

  p1 : X2 • CX01 • CCX02 ≈ X2 • CX01 • CCX02
  p1 = refl

  p2 : CCX02 • X2 ≈ CCX02 • X2
  p2 = refl

  p3 : X2 • CX01 • CCX02 ≈ CCX02 • X2
  p3 = trans (sym p1) (trans p0 p2)

  proved : X2 • CX01 • CCX02 ≈ CCX02 • X2
  proved = p3

module KB0281 where

  p0 : X2 • CX01 • CCX02 • CX02 ≈ CCX02 • X2 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0122.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • CCX02 • CX02 ≈ X2 • CX02 • CCX02
  p1 = by-assoc-and (under (X2) (ε) KB0119.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • CX02 ≈ CCX02 • X2 • CX02
  p3 = refl

  p4 : X2 • CX02 • CCX02 ≈ X2 • CX02 • CCX02
  p4 = refl

  p5 : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
  proved = p5

module KB0604 where

  p0 : CCX02 • X2 • CX02 • X0 ≈ X2 • CX02 • CCX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0281.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX02 • X0 ≈ CCX02 • X0 • CX02
  p1 = by-assoc-and (under (CCX02) (ε) KB0128.proved) Eq.refl Eq.refl

  p2 : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : X2 • CX02 • CCX02 • X0 ≈ X2 • CX02 • CCX02 • X0
  p3 = refl

  p4 : CCX02 • X0 • CX02 ≈ CCX02 • X0 • CX02
  p4 = refl

  p5 : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CX02 • CCX02 • X0 ≈ CCX02 • X0 • CX02
  proved = p5

module KB3819 where

  p0 : X2 • CX02 • CCX02 • X0 • CCX01 • X0 ≈ CCX02 • X0 • CX02 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (CCX01 • X0) KB0604.proved) Eq.refl Eq.refl

  p1 : X2 • CX02 • CCX02 • X0 • CCX01 • X0 ≈ X2 • CX02 • CCX02 • CX12 • CCX01
  p1 = by-assoc-and (under (X2 • CX02 • CCX02) (ε) KB0153.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X2 • CX02 • CCX02 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ CCX02 • X0 • CX02 • CCX01 • X0
  p3 = refl

  p4 : X2 • CX02 • CCX02 • CX12 • CCX01 ≈ X2 • CX02 • CX12 • CCX01 • CCX02
  p4 = by-assoc-and (under (X2 • CX02) (ε) KB0308.proved) Eq.refl Eq.refl

  p5 : X2 • CX02 • CX12 • CCX01 • CCX02 ≈ X1 • CX12 • CCX01 • X1 • CCX02
  p5 = by-assoc-and (under (ε) (CCX02) KB0795.proved) Eq.refl Eq.refl

  p6 : X1 • CX12 • CCX01 • X1 • CCX02 ≈ X0 • CX02 • CCX01 • X0 • CCX02
  p6 = by-assoc-and (under (ε) (CCX02) KB0817.proved) Eq.refl Eq.refl

  p7 : X2 • CX02 • CCX02 • CX12 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX02
  p7 = trans p4 (trans p5 (trans p6 (refl)))

  p8 : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • CCX02
  p8 = trans (sym p3) (trans p2 p7)

  proved : CCX02 • X0 • CX02 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • CCX02
  proved = p8

module KB0137 where

  p0 : CX01 • CCX01 ≈ CCX01 • CX02 • CX01
  p0 = drel141.proved

  p1 : CX01 • CCX01 ≈ CX01 • CCX01
  p1 = refl

  p2 : CCX01 • CX02 • CX01 ≈ CX02 • CCX01 • CX01
  p2 = by-assoc-and (under (ε) (CX01) KB0037.proved) Eq.refl Eq.refl

  p3 : CCX01 • CX02 • CX01 ≈ CX02 • CCX01 • CX01
  p3 = trans p2 (refl)

  p4 : CX01 • CCX01 ≈ CX02 • CCX01 • CX01
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX02 • CCX01 • CX01 ≈ CX01 • CCX01
  p5 = sym p4

  proved : CX02 • CCX01 • CX01 ≈ CX01 • CCX01
  proved = p5

module KB0320 where

  p0 : CCX01 • CCX01 • CCX12 • CCX01 ≈ CCX01 • CX02 • CCX12 • CX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0211.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01
  p1 = by-assoc-and (under (ε) (CCX12 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX02 • CCX12 • CX02 ≈ CCX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX02 • CCX12 • CX02 ≈ CX02 • CCX01 • CCX12 • CX02
  p3 = by-assoc-and (under (ε) (CCX12 • CX02) KB0037.proved) Eq.refl Eq.refl

  p4 : CCX01 • CX02 • CCX12 • CX02 ≈ CX02 • CCX01 • CCX12 • CX02
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX01 ≈ CCX12 • CCX01
  p5 = refl

  p6 : CX02 • CCX01 • CCX12 • CX02 ≈ CCX12 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX02 • CCX01 • CCX12 • CX02 ≈ CCX12 • CCX01
  proved = p6

module KB0322 where

  p0 : CX02 • CCX01 • CCX12 • CX02 • CX02 ≈ CCX12 • CCX01 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB0320.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • CCX12 • CX02 • CX02 ≈ CX02 • CCX01 • CCX12
  p1 = by-assoc-and (under (CX02 • CCX01 • CCX12) (ε) KB0008.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX01 • CX02 ≈ CX02 • CCX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX01 • CX02 ≈ CCX12 • CX02 • CCX01
  p3 = by-assoc-and (under (CCX12) (ε) KB0037.proved) Eq.refl Eq.refl

  p4 : CCX12 • CCX01 • CX02 ≈ CCX12 • CX02 • CCX01
  p4 = trans p3 (refl)

  p5 : CX02 • CCX01 • CCX12 ≈ CX02 • CCX01 • CCX12
  p5 = refl

  p6 : CCX12 • CX02 • CCX01 ≈ CX02 • CCX01 • CCX12
  p6 = trans (sym p4) (trans p2 p5)

  proved : CCX12 • CX02 • CCX01 ≈ CX02 • CCX01 • CCX12
  proved = p6

module KB0658 where

  p0 : CCX12 • CX02 • CCX01 • CX01 ≈ CX02 • CCX01 • CCX12 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0322.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX02 • CCX01 • CX01 ≈ CCX12 • CX01 • CCX01
  p1 = by-assoc-and (under (CCX12) (ε) KB0137.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX01 • CCX12 • CX01
  p3 = refl

  p4 : CCX12 • CX01 • CCX01 ≈ CCX12 • CX01 • CCX01
  p4 = refl

  p5 : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
  proved = p5

module KB0709 where

  p0 : CX02 • CX02 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01 • CCX01
  p0 = by-assoc-and (under (CX02) (ε) KB0658.proved) Eq.refl Eq.refl

  p1 : CX02 • CX02 • CCX01 • CCX12 • CX01 ≈ CCX01 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX01) KB0008.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX01 • CCX01
  p3 = refl

  p4 : CCX01 • CCX12 • CX01 ≈ CCX01 • CCX12 • CX01
  p4 = refl

  p5 : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
  proved = p5
