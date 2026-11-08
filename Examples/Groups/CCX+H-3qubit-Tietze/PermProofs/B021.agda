{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B021 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0011 ; module KB0012 ; module KB0013 ; module KB0014 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0036 ; module KB0129 ; module KB0153 ; module KB0166 ; module KB0215 ; module KB0219 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0025 ; module KB0123 ; module KB0124 ; module KB0212 ; module KB0218 ; module KB0322)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0018 ; module KB0045 ; module KB0150 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0140 ; module KB0190 ; module KB0339)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0285)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0055 ; module KB0170)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0515)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0193 ; module KB0331 ; module KB0390)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0671 ; module KB0706 ; module KB0751 ; module KB0826 ; module KB1272 ; module KB1273 ; module KB1329 ; module KB1377 ; module KB1761 ; module KB2769)

module KB3164 where

  p0 : CCX12 • CCX02 • CCX12 • CX02 • CCX01 ≈ CCX12 • CCX02 • CX02 • CCX01 • CCX12
  p0 = by-assoc-and (under (CCX12 • CCX02) (ε) KB0322.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CCX12 • CX02 • CCX01 ≈ CX10 • CCX02 • CX10 • CX02 • CCX01
  p1 = by-assoc-and (under (ε) (CX02 • CCX01) KB0215.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX10 • CCX02 • CX10 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01 • CCX12
  p3 = refl

  p4 : CX10 • CCX02 • CX10 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX01
  p4 = by-assoc-and (under (ε) (CX02 • CCX01) KB0219.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • CX01 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01
  p5 = by-assoc-and (under (CX01 • CCX12) (ε) KB0123.proved) Eq.refl Eq.refl

  p6 : CX10 • CCX02 • CX10 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01
  p6 = trans p4 (trans p5 (refl))

  p7 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01
  p7 = trans (sym p3) (trans p2 p6)

  proved : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01
  proved = p7

module KB3165 where

  p0 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01 • CCX12
  p0 = by-assoc-and (under (ε) (CCX12) KB3164.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01
  p1 = by-assoc-and (under (CCX12 • CCX02 • CX02 • CCX01) (ε) KB0014.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01 • CCX12
  p3 = refl

  p4 : CCX12 • CCX02 • CX02 • CCX01 ≈ CCX12 • CCX02 • CX02 • CCX01
  p4 = refl

  p5 : CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01
  proved = p5

module KB3166 where

  p0 : CX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
  p0 = by-assoc-and (under (CX01) (ε) KB3165.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX01 • CCX12) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX12 • CCX01 • CX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p3 = by-assoc-and (under (ε) (ε) KB1761.proved) Eq.refl Eq.refl

  p4 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p4 = trans p3 (refl)

  p5 : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12
  p5 = refl

  p6 : CCX02 • CCX12 • CCX01 • CX01 ≈ CCX12 • CCX01 • CX01 • CCX12
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX02 • CCX12 • CCX01 • CX01
  p7 = sym p6

  proved : CCX12 • CCX01 • CX01 • CCX12 ≈ CCX02 • CCX12 • CCX01 • CX01
  proved = p7

module KB3229 where

  p0 : CCX12 • CCX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CCX01 • CX01 • CCX12 • CCX02
  p0 = by-assoc-and (under (CCX12 • CCX01) (ε) KB0339.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX01 • CCX12 • CX01 • CCX12 ≈ CX20 • CCX01 • CX20 • CX01 • CCX12
  p1 = by-assoc-and (under (ε) (CX01 • CCX12) KB0212.proved) Eq.refl Eq.refl

  p2 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CX20 • CCX01 • CX20 • CX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CX01 • CCX02
  p3 = by-assoc-and (under (ε) (CCX02) KB3166.proved) Eq.refl Eq.refl

  p4 : CCX12 • CCX01 • CX01 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CX01 • CCX02
  p4 = trans p3 (refl)

  p5 : CX20 • CCX01 • CX20 • CX01 • CCX12 ≈ CX02 • CCX12 • CX02 • CX01 • CCX12
  p5 = by-assoc-and (under (ε) (CX01 • CCX12) KB0218.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX12 • CX02 • CX01 • CCX12 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
  p6 = by-assoc-and (under (CX02 • CCX12) (CCX12) KB0025.proved) Eq.refl Eq.refl

  p7 : CX20 • CCX01 • CX20 • CX01 • CCX12 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
  p7 = trans p5 (trans p6 (refl))

  p8 : CCX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
  p8 = trans (sym p4) (trans p2 p7)

  proved : CCX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CX01 • CX02 • CCX12
  proved = p8

module KB4079 where

  p0 : CCX02 • X0 • CCX02 • X2 • CCX12 • CX01 ≈ CCX02 • X0 • X2 • CCX12 • CCX02
  p0 = by-assoc-and (under (CCX02 • X0) (ε) KB0671.proved) Eq.refl Eq.refl

  p1 : CCX02 • X0 • CCX02 • X2 • CCX12 • CX01 ≈ X0 • CX21 • X2 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (X2 • CCX12 • CX01) KB0193.proved) Eq.refl Eq.refl

  p2 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ CCX02 • X0 • X2 • CCX12 • CCX02
  p3 = refl

  p4 : X0 • CX21 • X2 • CCX12 • CX01 ≈ X0 • CX21 • X2 • CCX12 • CX01
  p4 = refl

  p5 : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X0 • X2 • CCX12 • CCX02 ≈ X0 • CX21 • X2 • CCX12 • CX01
  proved = p5

module KB4332 where

  p0 : CX01 • X0 • CCX01 • X1 • CX20 • CCX12 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
  p0 = by-assoc-and (under (ε) (CX20 • CCX12) KB0826.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • CCX01 • X1 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
  p1 = by-assoc-and (under (CX01 • X0 • CCX01) (ε) KB0170.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
  p2 = trans (sym p0) p1

  p3 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
  p3 = refl

  p4 : CX01 • X0 • CCX01 • CCX12 • X1 ≈ CX01 • X0 • CCX01 • CCX12 • X1
  p4 = refl

  p5 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • X0 • CCX01 • CCX12 • X1 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
  p6 = sym p5

  proved : CX01 • X0 • CCX01 • CCX12 • X1 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
  proved = p6

module KB5019 where

  p0 : CCX01 • CCX02 • X2 • CX12 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB1272.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • X2 • CX12 • X0 ≈ CCX01 • CCX02 • X2 • X0 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX02 • X2) (ε) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CCX01 • CCX02 • X2 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p3 = refl

  p4 : CCX01 • CCX02 • X2 • X0 • CX12 ≈ CCX01 • CCX02 • X0 • X2 • CX12
  p4 = by-assoc-and (under (CCX01 • CCX02) (CX12) KB0018.proved) Eq.refl Eq.refl

  p5 : CCX01 • CCX02 • X2 • X0 • CX12 ≈ CCX01 • CCX02 • X0 • X2 • CX12
  p5 = trans p4 (refl)

  p6 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CCX01 • CCX02 • X0 • X2 • CX12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p7 = sym p6

  proved : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  proved = p7

module KB5021 where

  p0 : CCX01 • CCX02 • X0 • CX12 • X2 ≈ CX12 • CCX02 • CCX01 • X0 • X2
  p0 = by-assoc-and (under (ε) (X2) KB1273.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • X0 • CX12 • X2 ≈ CCX01 • CCX02 • X0 • X2 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX02 • X0) (ε) KB0036.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ CCX01 • CCX02 • X0 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ X0 • CCX02 • CCX01 • SWAP12 • X2
  p3 = by-assoc-and (under (ε) (X2) KB1329.proved) Eq.refl Eq.refl

  p4 : X0 • CCX02 • CCX01 • SWAP12 • X2 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
  p4 = by-assoc-and (under (X0 • CCX02 • CCX01) (ε) KB0055.proved) Eq.refl Eq.refl

  p5 : CX12 • CCX02 • CCX01 • X0 • X2 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p6 = by-assoc-and (under (ε) (ε) KB5019.proved) Eq.refl Eq.refl

  p7 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p7 = trans p6 (refl)

  p8 : X0 • CCX02 • CCX01 • X1 • SWAP12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
  p8 = trans (sym p5) (trans p2 p7)

  p9 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
  p9 = sym p8

  proved : CX12 • CCX02 • X2 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X1 • SWAP12
  proved = p9

module KB5198 where

  p0 : CCX02 • CCX01 • X0 • SWAP12 • X2 ≈ X0 • CX12 • CCX02 • CCX01 • X2
  p0 = by-assoc-and (under (ε) (X2) KB1377.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX01 • X0 • SWAP12 • X2 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
  p1 = by-assoc-and (under (CCX02 • CCX01 • X0) (ε) KB0055.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
  p2 = trans (sym p0) p1

  p3 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ X0 • CX12 • CCX02 • X2 • CCX01
  p3 = by-assoc-and (under (X0 • CX12 • CCX02) (ε) KB0029.proved) Eq.refl Eq.refl

  p4 : X0 • CX12 • CCX02 • CCX01 • X2 ≈ X0 • CX12 • CCX02 • X2 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
  p5 = refl

  p6 : X0 • CX12 • CCX02 • X2 • CCX01 ≈ CCX02 • CCX01 • X0 • X1 • SWAP12
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ X0 • CX12 • CCX02 • X2 • CCX01
  p7 = sym p6

  proved : CCX02 • CCX01 • X0 • X1 • SWAP12 ≈ X0 • CX12 • CCX02 • X2 • CCX01
  proved = p7

module KB5458 where

  p0 : X0 • X1 • X2 • CCX01 • CX01 • CCX02 ≈ CX01 • CX02 • X0 • CCX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB2769.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • X2 • CCX01 • CX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
  p1 = by-assoc-and (under (X0 • X1) (ε) KB0390.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ CX01 • CX02 • X0 • CCX01 • CCX02
  p3 = refl

  p4 : X0 • X1 • CCX01 • CCX02 • X2 ≈ X0 • X1 • CCX01 • CCX02 • X2
  p4 = refl

  p5 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
  proved = p5

module KB5514 where

  p0 : CCX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CCX01 • CCX12 • CCX02 • CX02 • CCX01
  p0 = by-assoc-and (under (CCX01) (ε) KB3165.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • CCX12 • CCX01 • CX01 • CCX12 ≈ CX01 • CCX12 • CX02 • CX01 • CCX12
  p1 = by-assoc-and (under (ε) (CX01 • CCX12) KB0706.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX02 • CX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX01 • CCX12 • CCX02 • CX02 • CCX01
  p3 = refl

  p4 : CX01 • CCX12 • CX02 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
  p4 = by-assoc-and (under (CX01 • CCX12) (CCX12) KB0025.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • CX02 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
  p5 = trans p4 (refl)

  p6 : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
  p6 = trans (sym p3) (trans p2 p5)

  proved : CCX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX12
  proved = p6

module braid0 where

  p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0150.proved) Eq.refl Eq.refl

  p1 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
  p1 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
  p2 = by-assoc-and (under (X0 • CX02) (CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) KB0011.proved) Eq.refl Eq.refl

  p3 : X0 • CX02 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0
  p3 = by-assoc-and (under (X0 • CX02 • CCX02 • CCX01) (X1 • CCX01 • X1 • X0) KB0012.proved) Eq.refl Eq.refl

  p4 : X0 • CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 • X0
  p4 = by-assoc-and (under (X0) (CCX01 • X1 • X0) KB0751.proved) Eq.refl Eq.refl

  p5 : X0 • X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 • X0 ≈ CX01 • X0 • CCX02 • CCX01 • CCX01 • X1 • X0
  p5 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • X1 • X0) KB0124.proved) Eq.refl Eq.refl

  p6 : CX01 • X0 • CCX02 • CCX01 • CCX01 • X1 • X0 ≈ CX01 • X0 • CCX02 • X1 • X0
  p6 = by-assoc-and (under (CX01 • X0 • CCX02) (X1 • X0) KB0011.proved) Eq.refl Eq.refl

  p7 : CX01 • X0 • CCX02 • X1 • X0 ≈ CX01 • X0 • X1 • CCX02 • X0
  p7 = by-assoc-and (under (CX01 • X0) (X0) KB0028.proved) Eq.refl Eq.refl

  p8 : CX01 • X0 • X1 • CCX02 • X0 ≈ X0 • CX01 • CCX02 • X0
  p8 = by-assoc-and (under (ε) (CCX02 • X0) KB0190.proved) Eq.refl Eq.refl

  p9 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX01 • CCX02 • X0
  p9 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (refl)))))))))

  p10 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p10 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p11 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p11 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p12 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p12 = by-assoc-and (under (ε) (CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0515.proved) Eq.refl Eq.refl

  p13 : CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p13 = by-assoc-and (under (CX12 • CX21 • CCX02) (X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p14 : CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p14 = by-assoc-and (under (CX12) (CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0129.proved) Eq.refl Eq.refl

  p15 : CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p15 = by-assoc-and (under (ε) (CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p16 : X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p16 = by-assoc-and (under (X0 • CX12 • CCX02 • CX12) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0150.proved) Eq.refl Eq.refl

  p17 : X0 • CX12 • CCX02 • CX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p17 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0027.proved) Eq.refl Eq.refl

  p18 : X0 • CX12 • CCX02 • CX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p18 = by-assoc-and (under (X0) (CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0285.proved) Eq.refl Eq.refl

  p19 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p19 = by-assoc-and (under (X0 • CX01) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0307.proved) Eq.refl Eq.refl

  p20 : X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0
  p20 = by-assoc-and (under (X0 • CX01 • CCX01 • CCX02) (CCX01 • CCX02 • CCX01 • X0) KB0012.proved) Eq.refl Eq.refl

  p21 : X0 • CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0
  p21 = by-assoc-and (under (X0 • CX01) (CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p22 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • CCX01 • CCX01 • X0
  p22 = by-assoc-and (under (X0 • CX01) (CCX01 • X0) KB0331.proved) Eq.refl Eq.refl

  p23 : X0 • CX01 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • X0
  p23 = by-assoc-and (under (X0 • CX01 • CCX02) (X0) KB0011.proved) Eq.refl Eq.refl

  p24 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • X0
  p24 = trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (refl))))))))))))))

  proved : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  proved = trans p9 (sym p24)

module braid1 where

  p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p2 = by-assoc-and (under (ε) (CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0515.proved) Eq.refl Eq.refl

  p3 : CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p4 : CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p4 = by-assoc-and (under (CX12) (CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0129.proved) Eq.refl Eq.refl

  p5 : CX12 • X0 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p5 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0045.proved) Eq.refl Eq.refl

  p6 : X0 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
  p6 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) KB0307.proved) Eq.refl Eq.refl

  p7 : X0 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0
  p7 = by-assoc-and (under (X0 • CCX01 • CCX02) (CCX01 • CCX02 • CCX01 • X0) KB0012.proved) Eq.refl Eq.refl

  p8 : X0 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0
  p8 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0) KB0214.proved) Eq.refl Eq.refl

  p9 : X0 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • CCX01 • X0
  p9 = by-assoc-and (under (X0) (CCX01 • X0) KB0331.proved) Eq.refl Eq.refl

  p10 : X0 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CCX02 • X0
  p10 = by-assoc-and (under (X0 • CCX02) (X0) KB0011.proved) Eq.refl Eq.refl

  p11 : X0 • CCX02 • X0 ≈ CX21 • CCX02
  p11 = by-assoc-and (under (ε) (ε) KB0166.proved) Eq.refl Eq.refl

  p12 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX21 • CCX02
  p12 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (refl))))))))))))

  p13 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
  p13 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0) KB0153.proved) Eq.refl Eq.refl

  p14 : CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
  p14 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0) KB0140.proved) Eq.refl Eq.refl

  p15 : X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
  p15 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0) KB0011.proved) Eq.refl Eq.refl

  p16 : X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • CCX01 • X0
  p16 = by-assoc-and (under (X0 • CCX02 • CCX01) (CCX01 • X0) KB0012.proved) Eq.refl Eq.refl

  p17 : X0 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CCX02 • X0
  p17 = by-assoc-and (under (X0 • CCX02) (X0) KB0011.proved) Eq.refl Eq.refl

  p18 : X0 • CCX02 • X0 ≈ CX21 • CCX02
  p18 = by-assoc-and (under (ε) (ε) KB0166.proved) Eq.refl Eq.refl

  p19 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX21 • CCX02
  p19 = trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (refl))))))

  proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
  proved = trans p12 (sym p19)
