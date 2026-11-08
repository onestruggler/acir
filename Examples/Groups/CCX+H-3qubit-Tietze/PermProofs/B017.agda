{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B017 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r009 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0006 ; module KB0009 ; module KB0026 ; module KB0027 ; module KB0039 ; module KB0040 ; module KB0136 ; module KB0215 ; module KB0217 ; module KB0219)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0007 ; module KB0086 ; module KB0119 ; module KB0176 ; module KB0211 ; module KB0330 ; module KB0407)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0063 ; module KB0090 ; module KB0097)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0310 ; module KB0315)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0001 ; module KB0078 ; module KB0080 ; module KB0138)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB1266)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0504)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B009 using (module KB1357)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0248)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0049 ; module KB0053)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0775)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B016 using (module KB0811 ; module KB3908)

module KB4310 where

  p0 : CX10 • CX02 • CCX12 • CCX01 • SWAP02 ≈ CX10 • X1 • CCX12 • CCX01 • X1
  p0 = by-assoc-and (under (CX10) (ε) KB0811.proved) Eq.refl Eq.refl

  p1 : CX10 • CX02 • CCX12 • CCX01 • SWAP02 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
  p1 = by-assoc-and (under (ε) (CCX01 • SWAP02) KB0315.proved) Eq.refl Eq.refl

  p2 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ CX02 • CCX12 • CX12 • CCX01 • SWAP02
  p2 = trans (sym p0) p1

  p3 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ CX10 • X1 • CCX12 • CCX01 • X1
  p3 = refl

  p4 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p4 = by-assoc-and (under (ε) (ε) KB3908.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX12 • CX12 • CCX01 • SWAP02 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p5 = trans p4 (refl)

  p6 : CX10 • X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX10 • X1 • CCX12 • CCX01 • X1 ≈ X1 • CCX12 • CCX01 • X1 • CX10
  proved = p6

module KB1048 where

  p0 : CX10 • CCX01 • SWAP01 • CCX02 ≈ CX01 • CX10 • CCX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0248.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX01 • SWAP01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
  p1 = by-assoc-and (under (CX10 • CCX01) (ε) KB0090.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CCX01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CCX01 • CCX02 ≈ CX01 • CX10 • CCX01 • CCX02
  p3 = refl

  p4 : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX10 • CCX01 • CCX12 • SWAP01
  p4 = refl

  p5 : CX01 • CX10 • CCX01 • CCX02 ≈ CX10 • CCX01 • CCX12 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02
  p6 = sym p5

  proved : CX10 • CCX01 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02
  proved = p6

module KB4626 where

  p0 : CX10 • CCX01 • CCX12 • SWAP01 • X0 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
  p0 = by-assoc-and (under (ε) (X0) KB1048.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX01 • CCX12 • SWAP01 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
  p1 = by-assoc-and (under (CX10 • CCX01 • CCX12) (ε) KB0097.proved) Eq.refl Eq.refl

  p2 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
  p3 = refl

  p4 : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
  p4 = refl

  p5 : CX01 • CX10 • CCX01 • CCX02 • X0 ≈ CX10 • CCX01 • CCX12 • X1 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
  p6 = sym p5

  proved : CX10 • CCX01 • CCX12 • X1 • SWAP01 ≈ CX01 • CX10 • CCX01 • CCX02 • X0
  proved = p6

module KB0081 where

  p0 : CX02 ≈ SWAP12 • CX01 • SWAP12
  p0 = by-assoc-and (axiom r009) Eq.refl Eq.refl

  p1 : CX02 ≈ CX02
  p1 = refl

  p2 : SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12
  p2 = refl

  p3 : CX02 ≈ SWAP12 • CX01 • SWAP12
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP12 • CX01 • SWAP12 ≈ CX02
  p4 = sym p3

  proved : SWAP12 • CX01 • SWAP12 ≈ CX02
  proved = p4

module KB0082 where

  p0 : SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX02
  p0 = by-assoc-and (under (SWAP12) (ε) KB0081.proved) Eq.refl Eq.refl

  p1 : SWAP12 • SWAP12 • CX01 • SWAP12 ≈ CX01 • SWAP12
  p1 = by-assoc-and (under (ε) (CX01 • SWAP12) KB0001.proved) Eq.refl Eq.refl

  p2 : SWAP12 • CX02 ≈ CX01 • SWAP12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • CX02 ≈ SWAP12 • CX02
  p3 = refl

  p4 : CX01 • SWAP12 ≈ CX01 • SWAP12
  p4 = refl

  p5 : SWAP12 • CX02 ≈ CX01 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP12 • CX02 ≈ CX01 • SWAP12
  proved = p5

module KB0253 where

  p0 : CCX02 • CX21 • CX12 ≈ CCX02 • CX12 • SWAP12
  p0 = by-assoc-and (under (CCX02) (ε) KB0080.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX21 • CX12 ≈ CX21 • CCX02 • CX12
  p1 = by-assoc-and (under (ε) (CX12) KB0039.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX12 • SWAP12 ≈ CCX02 • CX12 • SWAP12
  p3 = refl

  p4 : CX21 • CCX02 • CX12 ≈ CX21 • CCX02 • CX12
  p4 = refl

  p5 : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX12 • SWAP12 ≈ CX21 • CCX02 • CX12
  proved = p5

module KB1066 where

  p0 : CCX02 • CX12 • SWAP12 • SWAP02 ≈ CX21 • CCX02 • CX12 • SWAP02
  p0 = by-assoc-and (under (ε) (SWAP02) KB0253.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • SWAP12 • SWAP02 ≈ CCX02 • CX12 • SWAP02 • SWAP01
  p1 = by-assoc-and (under (CCX02 • CX12) (ε) KB0049.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • SWAP02 ≈ CCX02 • CX12 • SWAP02 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • SWAP02 ≈ CX21 • CCX02 • CX12 • SWAP02
  p3 = refl

  p4 : CCX02 • CX12 • SWAP02 • SWAP01 ≈ CCX02 • CX12 • SWAP01 • SWAP12
  p4 = by-assoc-and (under (CCX02 • CX12) (ε) KB0053.proved) Eq.refl Eq.refl

  p5 : CCX02 • CX12 • SWAP02 • SWAP01 ≈ CCX02 • CX12 • SWAP01 • SWAP12
  p5 = trans p4 (refl)

  p6 : CX21 • CCX02 • CX12 • SWAP02 ≈ CCX02 • CX12 • SWAP01 • SWAP12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX02 • CX12 • SWAP01 • SWAP12 ≈ CX21 • CCX02 • CX12 • SWAP02
  p7 = sym p6

  proved : CCX02 • CX12 • SWAP01 • SWAP12 ≈ CX21 • CCX02 • CX12 • SWAP02
  proved = p7

module KB1215 where

  p0 : CX01 • CCX02 • CX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
  p0 = by-assoc-and (under (CX01 • CCX02) (ε) KB0310.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • CX02 • CX10 • CX12 ≈ CX02 • CCX02 • CX10 • CX12
  p1 = by-assoc-and (under (ε) (CX10 • CX12) KB0119.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX02 • CX10 • CX02 ≈ CX02 • CCX02 • CX10 • CX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX02 • CX10 • CX02 ≈ CX01 • CCX02 • CX10 • CX02
  p3 = refl

  p4 : CX02 • CCX02 • CX10 • CX12 ≈ CX02 • CCX02 • CX10 • CX12
  p4 = refl

  p5 : CX01 • CCX02 • CX10 • CX02 ≈ CX02 • CCX02 • CX10 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
  p6 = sym p5

  proved : CX02 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
  proved = p6

module KB4678 where

  p0 : CCX02 • CX12 • SWAP01 • SWAP12 • CX02 ≈ CX21 • CCX02 • CX12 • SWAP02 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB1066.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • SWAP01 • SWAP12 • CX02 ≈ CCX02 • CX12 • SWAP01 • CX01 • SWAP12
  p1 = by-assoc-and (under (CCX02 • CX12 • SWAP01) (ε) KB0082.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CCX02 • CX12 • SWAP01 • CX01 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CX21 • CCX02 • CX12 • CX02 • CX20
  p3 = by-assoc-and (under (CX21 • CCX02 • CX12) (ε) KB0086.proved) Eq.refl Eq.refl

  p4 : CX21 • CCX02 • CX12 • CX02 • CX20 ≈ CX21 • CCX02 • CX02 • CX12 • CX20
  p4 = by-assoc-and (under (CX21 • CCX02) (CX20) KB0027.proved) Eq.refl Eq.refl

  p5 : CX21 • CCX02 • CX02 • CX12 • CX20 ≈ CX02 • CX21 • CCX02 • CX12 • CX20
  p5 = by-assoc-and (under (ε) (CX12 • CX20) KB0407.proved) Eq.refl Eq.refl

  p6 : CX02 • CX21 • CCX02 • CX12 • CX20 ≈ CX02 • CX20 • CCX02 • CX10 • CX12
  p6 = by-assoc-and (under (CX02) (ε) KB0775.proved) Eq.refl Eq.refl

  p7 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CX02 • CX20 • CCX02 • CX10 • CX12
  p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

  p8 : CCX02 • CX12 • SWAP01 • CX01 • SWAP12 ≈ CCX02 • CX12 • CX01 • CX10 • SWAP12
  p8 = by-assoc-and (under (CCX02 • CX12) (SWAP12) KB0063.proved) Eq.refl Eq.refl

  p9 : CCX02 • CX12 • CX01 • CX10 • SWAP12 ≈ CX02 • CCX02 • CX12 • CX10 • SWAP12
  p9 = by-assoc-and (under (ε) (CX10 • SWAP12) KB0504.proved) Eq.refl Eq.refl

  p10 : CX02 • CCX02 • CX12 • CX10 • SWAP12 ≈ CX02 • CCX02 • CX10 • CX12 • SWAP12
  p10 = by-assoc-and (under (CX02 • CCX02) (SWAP12) KB0026.proved) Eq.refl Eq.refl

  p11 : CX02 • CCX02 • CX10 • CX12 • SWAP12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
  p11 = by-assoc-and (under (ε) (SWAP12) KB1215.proved) Eq.refl Eq.refl

  p12 : CCX02 • CX12 • SWAP01 • CX01 • SWAP12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
  p12 = trans p8 (trans p9 (trans p10 (trans p11 (refl))))

  p13 : CX02 • CX20 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
  p13 = trans (sym p7) (trans p2 p12)

  proved : CX02 • CX20 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
  proved = p13

module KB1070 where

  p0 : CCX02 • CX12 • SWAP12 • CCX12 ≈ CX21 • CCX02 • CX12 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB0253.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • SWAP12 • CCX12 ≈ CCX02 • CX12 • CCX12 • SWAP12
  p1 = by-assoc-and (under (CCX02 • CX12) (ε) KB0078.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • CCX12 ≈ CCX02 • CX12 • CCX12 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • CCX12 ≈ CX21 • CCX02 • CX12 • CCX12
  p3 = refl

  p4 : CCX02 • CX12 • CCX12 • SWAP12 ≈ CCX02 • CX12 • CCX12 • SWAP12
  p4 = refl

  p5 : CX21 • CCX02 • CX12 • CCX12 ≈ CCX02 • CX12 • CCX12 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX12 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12
  p6 = sym p5

  proved : CCX02 • CX12 • CCX12 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12
  proved = p6

module KB4692 where

  p0 : CCX02 • CX12 • CCX12 • SWAP12 • CX02 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
  p0 = by-assoc-and (under (ε) (CX02) KB1070.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CCX12 • SWAP12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
  p1 = by-assoc-and (under (CCX02 • CX12 • CCX12) (ε) KB0082.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
  p3 = refl

  p4 : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
  p4 = refl

  p5 : CX21 • CCX02 • CX12 • CCX12 • CX02 ≈ CCX02 • CX12 • CCX12 • CX01 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
  p6 = sym p5

  proved : CCX02 • CX12 • CCX12 • CX01 • SWAP12 ≈ CX21 • CCX02 • CX12 • CCX12 • CX02
  proved = p6

module KB5007 where

  p0 : CCX01 • CCX12 • CCX01 • CX21 • CCX01 ≈ CCX01 • CCX12 • CX21 • CCX01 • CCX02
  p0 = by-assoc-and (under (CCX01 • CCX12) (ε) KB1266.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CCX01 • CX21 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
  p1 = by-assoc-and (under (ε) (CX21 • CCX01) KB0211.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CCX01 • CCX12 • CX21 • CCX01 • CCX02
  p3 = refl

  p4 : CX02 • CCX12 • CX02 • CX21 • CCX01 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
  p4 = refl

  p5 : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CCX12 • CX21 • CCX01 • CCX02 ≈ CX02 • CCX12 • CX02 • CX21 • CCX01
  proved = p5

module KB0547 where

  p0 : CCX12 • CX20 • CX21 • CCX02 ≈ CCX12 • CCX02 • CX20
  p0 = by-assoc-and (under (CCX12) (ε) KB0176.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX20 • CX21 • CCX02 ≈ CX20 • CCX12 • CX21 • CCX02
  p1 = by-assoc-and (under (ε) (CX21 • CCX02) KB0040.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX02 • CX20 ≈ CX20 • CCX12 • CX21 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX02 • CX20 ≈ CCX12 • CCX02 • CX20
  p3 = refl

  p4 : CX20 • CCX12 • CX21 • CCX02 ≈ CX21 • CCX12 • CCX02
  p4 = by-assoc-and (under (ε) (CCX02) KB0138.proved) Eq.refl Eq.refl

  p5 : CX20 • CCX12 • CX21 • CCX02 ≈ CX21 • CCX12 • CCX02
  p5 = trans p4 (refl)

  p6 : CCX12 • CCX02 • CX20 ≈ CX21 • CCX12 • CCX02
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX12 • CCX02 • CX20 ≈ CX21 • CCX12 • CCX02
  proved = p6

module KB0665 where

  p0 : CCX01 • CX21 • CCX02 • CX20 ≈ CX21 • CCX02 • CCX01 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB0330.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CCX02 • CX20 ≈ CCX01 • CX20 • CCX02
  p1 = by-assoc-and (under (CCX01) (ε) KB0136.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CCX01 • CX20 ≈ CCX01 • CX20 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX02 • CCX01 • CX20
  p3 = refl

  p4 : CCX01 • CX20 • CCX02 ≈ CCX01 • CX20 • CCX02
  p4 = refl

  p5 : CX21 • CCX02 • CCX01 • CX20 ≈ CCX01 • CX20 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX02 • CCX01 • CX20 ≈ CCX01 • CX20 • CCX02
  proved = p5

module KB0716 where

  p0 : CX21 • CX21 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CX20 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0665.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX02 • CCX01 • CX20 ≈ CCX02 • CCX01 • CX20
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CX20) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CX20 • CCX02 ≈ CX21 • CCX01 • CX20 • CCX02
  p3 = refl

  p4 : CCX02 • CCX01 • CX20 ≈ CCX02 • CCX01 • CX20
  p4 = refl

  p5 : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX01 • CX20 • CCX02 ≈ CCX02 • CCX01 • CX20
  proved = p5

module KB1359 where

  p0 : CCX12 • CX21 • CCX01 • CX20 • CCX02 ≈ CX21 • CCX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB1357.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX21 • CCX01 • CX20 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
  p1 = by-assoc-and (under (CCX12) (ε) KB0716.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX12 • CCX02 ≈ CX21 • CCX01 • CCX12 • CCX02
  p3 = refl

  p4 : CCX12 • CCX02 • CCX01 • CX20 ≈ CCX12 • CCX02 • CCX01 • CX20
  p4 = refl

  p5 : CX21 • CCX01 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01 • CX20
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX12 • CCX02 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02
  proved = p6

module KB1404 where

  p0 : CCX12 • CCX02 • CCX01 • CX20 • CX20 ≈ CX21 • CCX01 • CCX12 • CCX02 • CX20
  p0 = by-assoc-and (under (ε) (CX20) KB1359.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CCX01 • CX20 • CX20 ≈ CCX12 • CCX02 • CCX01
  p1 = by-assoc-and (under (CCX12 • CCX02 • CCX01) (ε) KB0009.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CCX12 • CCX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CX21 • CCX01 • CX21 • CCX12 • CCX02
  p3 = by-assoc-and (under (CX21 • CCX01) (ε) KB0547.proved) Eq.refl Eq.refl

  p4 : CX21 • CCX01 • CX21 • CCX12 • CCX02 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX02
  p4 = by-assoc-and (under (ε) (CCX12 • CCX02) KB0217.proved) Eq.refl Eq.refl

  p5 : CX21 • CCX01 • CCX12 • CCX02 • CX20 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX02
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX12 • CCX02 • CCX01 ≈ CCX12 • CCX02 • CCX01
  p6 = refl

  p7 : CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01
  p7 = trans (sym p5) (trans p2 p6)

  proved : CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX01
  proved = p7

module KB1405 where

  p0 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CX12 • CCX12 • CCX02 • CCX01
  p0 = by-assoc-and (under (CX12) (ε) KB1404.proved) Eq.refl Eq.refl

  p1 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX12 • CCX02) KB0006.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CCX02 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CCX02 • CCX01 ≈ CX12 • CCX12 • CCX02 • CCX01
  p3 = refl

  p4 : CCX02 • CX12 • CCX12 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX02
  p4 = refl

  p5 : CX12 • CCX12 • CCX02 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CX12 • CCX12 • CCX02 ≈ CX12 • CCX12 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX02 • CX12 • CCX12 • CCX02 ≈ CX12 • CCX12 • CCX02 • CCX01
  proved = p6

module KB0972 where

  p0 : CX12 • CX10 • CCX02 • CX10 ≈ CX12 • CX01 • CCX12 • CX01
  p0 = by-assoc-and (under (CX12) (ε) KB0219.proved) Eq.refl Eq.refl

  p1 : CX12 • CX10 • CCX02 • CX10 ≈ CX10 • CX12 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CCX02 • CX10) KB0026.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • CCX12 • CX01 ≈ CX12 • CX01 • CCX12 • CX01
  p3 = refl

  p4 : CX10 • CX12 • CCX02 • CX10 ≈ CX10 • CX12 • CCX02 • CX10
  p4 = refl

  p5 : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
  proved = p5

module KB4453 where

  p0 : CCX02 • CX12 • CX01 • CCX12 • CX01 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
  p0 = by-assoc-and (under (CCX02) (ε) KB0972.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CX01 • CCX12 • CX01 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CCX12 • CX01) KB0504.proved) Eq.refl Eq.refl

  p2 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
  p3 = refl

  p4 : CX02 • CCX02 • CX12 • CCX12 • CX01 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p4 = refl

  p5 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  proved = p5

module KB5250 where

  p0 : CCX02 • CX12 • CCX12 • CCX02 • CCX12 ≈ CX12 • CCX12 • CCX02 • CCX01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB1405.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CCX12 • CCX02 • CCX12 ≈ CCX02 • CX12 • CX10 • CCX02 • CX10
  p1 = by-assoc-and (under (CCX02 • CX12) (ε) KB0215.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CCX02 • CX12 • CX10 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX12 • CCX12 • CCX02 • CCX01 • CCX12
  p3 = refl

  p4 : CCX02 • CX12 • CX10 • CCX02 • CX10 ≈ CCX02 • CX10 • CX12 • CCX02 • CX10
  p4 = by-assoc-and (under (CCX02) (CCX02 • CX10) KB0026.proved) Eq.refl Eq.refl

  p5 : CCX02 • CX10 • CX12 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p5 = by-assoc-and (under (ε) (ε) KB4453.proved) Eq.refl Eq.refl

  p6 : CCX02 • CX12 • CX10 • CCX02 • CX10 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX12 • CCX12 • CCX02 • CCX01 • CCX12 ≈ CX02 • CCX02 • CX12 • CCX12 • CX01
  proved = p7
