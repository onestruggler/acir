{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B020 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0014 ; module KB0026 ; module KB0027 ; module KB0028 ; module KB0029 ; module KB0031 ; module KB0035 ; module KB0036 ; module KB0046 ; module KB0120 ; module KB0129 ; module KB0147 ; module KB0151 ; module KB0160 ; module KB0164 ; module KB0219 ; module KB0308 ; module KB0338)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0007 ; module KB0030 ; module KB0119 ; module KB0122 ; module KB0123 ; module KB0128 ; module KB0137 ; module KB0320 ; module KB0330)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0018 ; module KB0019 ; module KB0045 ; module KB0090 ; module KB0141 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0044 ; module KB0047 ; module KB0140 ; module KB0152 ; module KB0280 ; module KB0293 ; module KB0340 ; module KB0825)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0001 ; module KB0078 ; module KB0108)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0061 ; module KB0261)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0130 ; module KB0188 ; module KB1362)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B011 using (module KB0142 ; module KB1661)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B012 using (module KB0055)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B013 using (module KB0586)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0148 ; module KB0287 ; module KB0753 ; module KB0818)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B016 using (module KB0143)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0181 ; module KB0183 ; module KB0222 ; module KB0234 ; module KB0283 ; module KB0306 ; module KB0332 ; module KB0334 ; module KB0341 ; module KB0417 ; module KB0486 ; module KB0561)

module KB0655 where

  p0 : CX01 • CX02 • CCX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX01) (ε) KB0320.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX01 • CCX12 • CX02 ≈ CCX01 • CX01 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (CCX12 • CX02) KB0123.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX01 ≈ CX01 • CCX12 • CCX01
  p3 = refl

  p4 : CCX01 • CX01 • CCX12 • CX02 ≈ CCX01 • CX01 • CCX12 • CX02
  p4 = refl

  p5 : CX01 • CCX12 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
  p6 = sym p5

  proved : CCX01 • CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
  proved = p6

module KB0664 where

  p0 : CCX01 • CX21 • CCX02 • X0 ≈ CX21 • CCX02 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0330.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CCX02 • X0 ≈ CCX01 • X0 • CCX02
  p1 = by-assoc-and (under (CCX01) (ε) KB0129.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CCX01 • X0 ≈ CX21 • CCX02 • CCX01 • X0
  p3 = refl

  p4 : CCX01 • X0 • CCX02 ≈ CCX01 • X0 • CCX02
  p4 = refl

  p5 : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX02 • CCX01 • X0 ≈ CCX01 • X0 • CCX02
  proved = p5

module KB0671 where

  p0 : X2 • CX01 • CCX02 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
  p0 = by-assoc-and (under (X2) (ε) KB0340.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • CCX02 • CCX12 • CX01 ≈ CCX02 • X2 • CCX12 • CX01
  p1 = by-assoc-and (under (ε) (CCX12 • CX01) KB0122.proved) Eq.refl Eq.refl

  p2 : X2 • CCX12 • CCX02 ≈ CCX02 • X2 • CCX12 • CX01
  p2 = trans (sym p0) p1

  p3 : X2 • CCX12 • CCX02 ≈ X2 • CCX12 • CCX02
  p3 = refl

  p4 : CCX02 • X2 • CCX12 • CX01 ≈ CCX02 • X2 • CCX12 • CX01
  p4 = refl

  p5 : X2 • CCX12 • CCX02 ≈ CCX02 • X2 • CCX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • X2 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX02 • X2 • CCX12 • CX01 ≈ X2 • CCX12 • CCX02
  proved = p6

module KB0706 where

  p0 : CCX01 • CCX01 • CX01 • CCX12 • CX02 ≈ CCX01 • CX01 • CCX12 • CCX01
  p0 = by-assoc-and (under (CCX01) (ε) KB0655.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CX02
  p1 = by-assoc-and (under (ε) (CX01 • CCX12 • CX02) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CCX12 • CCX01 ≈ CX01 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CCX12 • CCX01 ≈ CCX01 • CX01 • CCX12 • CCX01
  p3 = refl

  p4 : CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CX02
  p4 = refl

  p5 : CCX01 • CX01 • CCX12 • CCX01 ≈ CX01 • CCX12 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX01 • CCX12 • CCX01 ≈ CX01 • CCX12 • CX02
  proved = p5

module KB0715 where

  p0 : CX21 • CX21 • CCX02 • CCX01 • X0 ≈ CX21 • CCX01 • X0 • CCX02
  p0 = by-assoc-and (under (CX21) (ε) KB0664.proved) Eq.refl Eq.refl

  p1 : CX21 • CX21 • CCX02 • CCX01 • X0 ≈ CCX02 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • X0) KB0007.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • X0 • CCX02 ≈ CCX02 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • X0 • CCX02 ≈ CX21 • CCX01 • X0 • CCX02
  p3 = refl

  p4 : CCX02 • CCX01 • X0 ≈ CCX02 • CCX01 • X0
  p4 = refl

  p5 : CX21 • CCX01 • X0 • CCX02 ≈ CCX02 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX21 • CCX01 • X0 • CCX02 ≈ CCX02 • CCX01 • X0
  proved = p5

module KB0742 where

  p0 : CX21 • CCX01 • X0 • CCX02 • CCX02 ≈ CCX02 • CCX01 • X0 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0715.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX01 • X0 • CCX02 • CCX02 ≈ CX21 • CCX01 • X0
  p1 = by-assoc-and (under (CX21 • CCX01 • X0) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX01 • X0 • CCX02 ≈ CX21 • CCX01 • X0
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX01 • X0 • CCX02 ≈ CCX02 • CCX01 • X0 • CCX02
  p3 = refl

  p4 : CX21 • CCX01 • X0 ≈ CX21 • CCX01 • X0
  p4 = refl

  p5 : CCX02 • CCX01 • X0 • CCX02 ≈ CX21 • CCX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CCX01 • X0 • CCX02 ≈ CX21 • CCX01 • X0
  proved = p5

module KB0751 where

  p0 : CX01 • CCX02 • CX02 • CCX01 • X1 ≈ CX01 • CCX02 • X1 • CCX01
  p0 = by-assoc-and (under (CX01 • CCX02) (ε) KB0120.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • CX02 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0119.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX02 • X1 • CCX01 ≈ CX02 • CCX02 • CCX01 • X1
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX02 • X1 • CCX01 ≈ CX01 • X1 • CCX02 • CCX01
  p3 = by-assoc-and (under (CX01) (CCX01) KB0028.proved) Eq.refl Eq.refl

  p4 : CX01 • X1 • CCX02 • CCX01 ≈ X1 • CX01 • CCX02 • CCX01
  p4 = by-assoc-and (under (ε) (CCX02 • CCX01) KB0035.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX02 • X1 • CCX01 ≈ X1 • CX01 • CCX02 • CCX01
  p5 = trans p3 (trans p4 (refl))

  p6 : CX02 • CCX02 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1
  p6 = refl

  p7 : X1 • CX01 • CCX02 • CCX01 ≈ CX02 • CCX02 • CCX01 • X1
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CX02 • CCX02 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01
  p8 = sym p7

  proved : CX02 • CCX02 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01
  proved = p8

module KB0762 where

  p0 : CX01 • CCX02 • X2 • CX02 • X0 ≈ X2 • CCX02 • CX02 • X0
  p0 = by-assoc-and (under (ε) (CX02 • X0) KB0130.proved) Eq.refl Eq.refl

  p1 : CX01 • CCX02 • X2 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
  p1 = by-assoc-and (under (CX01 • CCX02) (ε) KB0128.proved) Eq.refl Eq.refl

  p2 : X2 • CCX02 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : X2 • CCX02 • CX02 • X0 ≈ X2 • CCX02 • CX02 • X0
  p3 = refl

  p4 : CX01 • CCX02 • X0 • CX02 ≈ CX01 • CCX02 • X0 • CX02
  p4 = refl

  p5 : X2 • CCX02 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
  p6 = sym p5

  proved : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
  proved = p6

module KB0788 where

  p0 : CX02 • CCX01 • X1 • CX10 • X1 ≈ CX02 • CCX01 • X0 • CX10
  p0 = by-assoc-and (under (CX02 • CCX01) (ε) KB0142.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • CX10 • X1 ≈ X1 • CCX01 • CX10 • X1
  p1 = by-assoc-and (under (ε) (CX10 • X1) KB0120.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • X0 • CX10 ≈ X1 • CCX01 • CX10 • X1
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX01 • X0 • CX10 ≈ CX02 • X0 • CX10 • CCX01
  p3 = by-assoc-and (under (CX02) (ε) KB0280.proved) Eq.refl Eq.refl

  p4 : CX02 • CCX01 • X0 • CX10 ≈ CX02 • X0 • CX10 • CCX01
  p4 = trans p3 (refl)

  p5 : X1 • CCX01 • CX10 • X1 ≈ X1 • CCX01 • CX10 • X1
  p5 = refl

  p6 : CX02 • X0 • CX10 • CCX01 ≈ X1 • CCX01 • CX10 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX02 • X0 • CX10 • CCX01 ≈ X1 • CCX01 • CX10 • X1
  proved = p6

module KB0805 where

  p0 : X0 • X1 • CX10 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • CX10
  p0 = by-assoc-and (under (X0 • X1) (ε) KB0147.proved) Eq.refl Eq.refl

  p1 : X0 • X1 • CX10 • CX12 • CCX01 ≈ CX10 • X1 • CX12 • CCX01
  p1 = by-assoc-and (under (ε) (CX12 • CCX01) KB0143.proved) Eq.refl Eq.refl

  p2 : X0 • X1 • CCX01 • CX10 ≈ CX10 • X1 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • X1 • CCX01 • CX10 ≈ X0 • X1 • CCX01 • CX10
  p3 = refl

  p4 : CX10 • X1 • CX12 • CCX01 ≈ CX10 • X1 • CX12 • CCX01
  p4 = refl

  p5 : X0 • X1 • CCX01 • CX10 ≈ CX10 • X1 • CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • CX10
  p6 = sym p5

  proved : CX10 • X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • CX10
  proved = p6

module KB0815 where

  p0 : X1 • CX02 • CCX01 • X0 • CCX01 ≈ X1 • CX02 • X0 • CX12
  p0 = by-assoc-and (under (X1 • CX02) (ε) KB0152.proved) Eq.refl Eq.refl

  p1 : X1 • CX02 • CCX01 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (X0 • CCX01) KB0151.proved) Eq.refl Eq.refl

  p2 : X1 • CX02 • X0 • CX12 ≈ CCX01 • X1 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : X1 • CX02 • X0 • CX12 ≈ X1 • CX02 • X0 • CX12
  p3 = refl

  p4 : CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01
  p4 = by-assoc-and (under (CCX01) (CCX01) KB0044.proved) Eq.refl Eq.refl

  p5 : CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01
  p5 = trans p4 (refl)

  p6 : X1 • CX02 • X0 • CX12 ≈ CCX01 • X0 • X1 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX01 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CX12
  p7 = sym p6

  proved : CCX01 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CX12
  proved = p7

module KB0826 where

  p0 : CX01 • CX01 • X0 • CCX01 • CX01 ≈ CX01 • X0 • CCX01 • X1
  p0 = by-assoc-and (under (CX01) (ε) KB0825.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • X0 • CCX01 • CX01 ≈ X0 • CCX01 • CX01
  p1 = by-assoc-and (under (ε) (X0 • CCX01 • CX01) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CCX01 • X1 ≈ X0 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CCX01 • X1 ≈ CX01 • X0 • CCX01 • X1
  p3 = refl

  p4 : X0 • CCX01 • CX01 ≈ X0 • CCX01 • CX01
  p4 = refl

  p5 : CX01 • X0 • CCX01 • X1 ≈ X0 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • CCX01 • X1 ≈ X0 • CCX01 • CX01
  proved = p5

module KB0835 where

  p0 : CX02 • X0 • CX02 • CCX01 • CX01 ≈ X0 • X2 • CCX01 • CX01
  p0 = by-assoc-and (under (ε) (CCX01 • CX01) KB0160.proved) Eq.refl Eq.refl

  p1 : CX02 • X0 • CX02 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
  p1 = by-assoc-and (under (CX02 • X0) (ε) KB0137.proved) Eq.refl Eq.refl

  p2 : X0 • X2 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • X2 • CCX01 • CX01 ≈ X0 • X2 • CCX01 • CX01
  p3 = refl

  p4 : CX02 • X0 • CX01 • CCX01 ≈ CX02 • X0 • CX01 • CCX01
  p4 = refl

  p5 : X0 • X2 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX02 • X0 • CX01 • CCX01 ≈ X0 • X2 • CCX01 • CX01
  p6 = sym p5

  proved : CX02 • X0 • CX01 • CCX01 ≈ X0 • X2 • CCX01 • CX01
  proved = p6

module KB0836 where

  p0 : CX02 • CCX02 • CX02 • X0 • CX02 ≈ CX02 • CCX02 • X0 • X2
  p0 = by-assoc-and (under (CX02 • CCX02) (ε) KB0160.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX02 • CX02 • X0 • CX02 ≈ CX01 • CCX02 • X0 • CX02
  p1 = by-assoc-and (under (ε) (X0 • CX02) KB0148.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX02 • X0 • X2 ≈ CX01 • CCX02 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : CX02 • CCX02 • X0 • X2 ≈ CX02 • CCX02 • X0 • X2
  p3 = refl

  p4 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
  p4 = by-assoc-and (under (ε) (ε) KB0762.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
  p5 = trans p4 (refl)

  p6 : CX02 • CCX02 • X0 • X2 ≈ X2 • CCX02 • CX02 • X0
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX02 • CCX02 • X0 • X2 ≈ X2 • CCX02 • CX02 • X0
  proved = p6

module KB0884 where

  p0 : CX12 • CCX12 • CX12 • CCX01 • X0 ≈ CX10 • CCX12 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (CCX01 • X0) KB0181.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX12 • CX12 • CCX01 • X0 ≈ CX12 • CCX12 • X0 • CCX01
  p1 = by-assoc-and (under (CX12 • CCX12) (ε) KB0140.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CCX01 • X0 ≈ CX12 • CCX12 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CCX01 • X0 ≈ CX10 • CCX12 • CCX01 • X0
  p3 = refl

  p4 : CX12 • CCX12 • X0 • CCX01 ≈ CX12 • X0 • CCX12 • CCX01
  p4 = by-assoc-and (under (CX12) (CCX01) KB0046.proved) Eq.refl Eq.refl

  p5 : CX12 • X0 • CCX12 • CCX01 ≈ X0 • CX12 • CCX12 • CCX01
  p5 = by-assoc-and (under (ε) (CCX12 • CCX01) KB0045.proved) Eq.refl Eq.refl

  p6 : CX12 • CCX12 • X0 • CCX01 ≈ X0 • CX12 • CCX12 • CCX01
  p6 = trans p4 (trans p5 (refl))

  p7 : CX10 • CCX12 • CCX01 • X0 ≈ X0 • CX12 • CCX12 • CCX01
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX10 • CCX12 • CCX01 • X0 ≈ X0 • CX12 • CCX12 • CCX01
  proved = p7

module KB0890 where

  p0 : CX12 • X1 • X2 • CX02 • X0 ≈ X1 • CX12 • CX02 • X0
  p0 = by-assoc-and (under (ε) (CX02 • X0) KB0183.proved) Eq.refl Eq.refl

  p1 : CX12 • X1 • X2 • CX02 • X0 ≈ CX12 • X1 • X0 • CX02
  p1 = by-assoc-and (under (CX12 • X1) (ε) KB0128.proved) Eq.refl Eq.refl

  p2 : X1 • CX12 • CX02 • X0 ≈ CX12 • X1 • X0 • CX02
  p2 = trans (sym p0) p1

  p3 : X1 • CX12 • CX02 • X0 ≈ X1 • CX02 • CX12 • X0
  p3 = by-assoc-and (under (X1) (X0) KB0027.proved) Eq.refl Eq.refl

  p4 : X1 • CX02 • CX12 • X0 ≈ X1 • CX02 • X0 • CX12
  p4 = by-assoc-and (under (X1 • CX02) (ε) KB0045.proved) Eq.refl Eq.refl

  p5 : X1 • CX12 • CX02 • X0 ≈ X1 • CX02 • X0 • CX12
  p5 = trans p3 (trans p4 (refl))

  p6 : CX12 • X1 • X0 • CX02 ≈ CX12 • X0 • X1 • CX02
  p6 = by-assoc-and (under (CX12) (CX02) KB0044.proved) Eq.refl Eq.refl

  p7 : CX12 • X0 • X1 • CX02 ≈ X0 • CX12 • X1 • CX02
  p7 = by-assoc-and (under (ε) (X1 • CX02) KB0045.proved) Eq.refl Eq.refl

  p8 : X0 • CX12 • X1 • CX02 ≈ X0 • CX02 • CX12 • X1
  p8 = by-assoc-and (under (X0) (ε) KB0222.proved) Eq.refl Eq.refl

  p9 : CX12 • X1 • X0 • CX02 ≈ X0 • CX02 • CX12 • X1
  p9 = trans p6 (trans p7 (trans p8 (refl)))

  p10 : X1 • CX02 • X0 • CX12 ≈ X0 • CX02 • CX12 • X1
  p10 = trans (sym p5) (trans p2 p9)

  proved : X1 • CX02 • X0 • CX12 ≈ X0 • CX02 • CX12 • X1
  proved = p10

module KB0904 where

  p0 : CCX02 • X2 • CX01 • CX02 • CX12 ≈ X2 • CCX02 • CX02 • CX12
  p0 = by-assoc-and (under (ε) (CX02 • CX12) KB0188.proved) Eq.refl Eq.refl

  p1 : CCX02 • X2 • CX01 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
  p1 = by-assoc-and (under (CCX02 • X2) (ε) KB0164.proved) Eq.refl Eq.refl

  p2 : X2 • CCX02 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
  p2 = trans (sym p0) p1

  p3 : X2 • CCX02 • CX02 • CX12 ≈ X2 • CCX02 • CX02 • CX12
  p3 = refl

  p4 : CCX02 • X2 • CX12 • CX01 ≈ CCX02 • X2 • CX12 • CX01
  p4 = refl

  p5 : X2 • CCX02 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • X2 • CX12 • CX01 ≈ X2 • CCX02 • CX02 • CX12
  p6 = sym p5

  proved : CCX02 • X2 • CX12 • CX01 ≈ X2 • CCX02 • CX02 • CX12
  proved = p6

module KB0963 where

  p0 : CCX01 • CCX02 • CCX01 • X2 ≈ CX12 • CCX02 • CX12 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0214.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • X2 ≈ CCX01 • CCX02 • X2 • CCX01
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • X2 ≈ CCX01 • CCX02 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX12 • X2 ≈ CX12 • CCX02 • X2 • CX12
  p3 = by-assoc-and (under (CX12 • CCX02) (ε) KB0036.proved) Eq.refl Eq.refl

  p4 : CX12 • CCX02 • CX12 • X2 ≈ CX12 • CCX02 • X2 • CX12
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX02 • X2 • CCX01 ≈ CCX01 • CCX02 • X2 • CCX01
  p5 = refl

  p6 : CX12 • CCX02 • X2 • CX12 ≈ CCX01 • CCX02 • X2 • CCX01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • CCX02 • X2 • CCX01 ≈ CX12 • CCX02 • X2 • CX12
  p7 = sym p6

  proved : CCX01 • CCX02 • X2 • CCX01 ≈ CX12 • CCX02 • X2 • CX12
  proved = p7

module KB0973 where

  p0 : CX10 • CCX02 • CX10 • X0 ≈ CX01 • CCX12 • CX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0219.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX02 • CX10 • X0 ≈ CX10 • CCX02 • X0 • CX10
  p1 = by-assoc-and (under (CX10 • CCX02) (ε) KB0047.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CX01 • X0 ≈ CX10 • CCX02 • X0 • CX10
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CX01 • X0 ≈ CX01 • CCX12 • CX01 • X0
  p3 = refl

  p4 : CX10 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CX10
  p4 = refl

  p5 : CX01 • CCX12 • CX01 • X0 ≈ CX10 • CCX02 • X0 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CCX02 • X0 • CX10 ≈ CX01 • CCX12 • CX01 • X0
  p6 = sym p5

  proved : CX10 • CCX02 • X0 • CX10 ≈ CX01 • CCX12 • CX01 • X0
  proved = p6

module KB0997 where

  p0 : CCX01 • CX12 • CX21 • X2 ≈ CCX01 • X1 • CX12 • CX21
  p0 = by-assoc-and (under (CCX01) (ε) KB0234.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX12 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2
  p1 = by-assoc-and (under (ε) (CX21 • X2) KB0031.proved) Eq.refl Eq.refl

  p2 : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
  p2 = trans (sym p0) p1

  p3 : CCX01 • X1 • CX12 • CX21 ≈ CCX01 • X1 • CX12 • CX21
  p3 = refl

  p4 : CX12 • CCX01 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2
  p4 = refl

  p5 : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
  proved = p5

module KB1100 where

  p0 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0261.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • SWAP01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
  p1 = by-assoc-and (under (CX12 • CX01) (ε) KB0090.proved) Eq.refl Eq.refl

  p2 : CX10 • CX12 • CX01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX10 • CX12 • CX01 • CCX02 ≈ CX10 • CX12 • CX01 • CCX02
  p3 = refl

  p4 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX12 • CX01 • CCX12 • SWAP01
  p4 = refl

  p5 : CX10 • CX12 • CX01 • CCX02 ≈ CX12 • CX01 • CCX12 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
  p6 = sym p5

  proved : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
  proved = p6

module KB1173 where

  p0 : SWAP12 • CCX12 • X2 • CX12 ≈ SWAP12 • X2 • CX12 • CCX12
  p0 = by-assoc-and (under (SWAP12) (ε) KB0287.proved) Eq.refl Eq.refl

  p1 : SWAP12 • CCX12 • X2 • CX12 ≈ CCX12 • SWAP12 • X2 • CX12
  p1 = by-assoc-and (under (ε) (X2 • CX12) KB0078.proved) Eq.refl Eq.refl

  p2 : SWAP12 • X2 • CX12 • CCX12 ≈ CCX12 • SWAP12 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : SWAP12 • X2 • CX12 • CCX12 ≈ X1 • SWAP12 • CX12 • CCX12
  p3 = by-assoc-and (under (ε) (CX12 • CCX12) KB0055.proved) Eq.refl Eq.refl

  p4 : X1 • SWAP12 • CX12 • CCX12 ≈ X1 • CX12 • CX21 • CCX12
  p4 = by-assoc-and (under (X1) (CCX12) KB0061.proved) Eq.refl Eq.refl

  p5 : SWAP12 • X2 • CX12 • CCX12 ≈ X1 • CX12 • CX21 • CCX12
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX12 • SWAP12 • X2 • CX12 ≈ CCX12 • X1 • SWAP12 • CX12
  p6 = by-assoc-and (under (CCX12) (CX12) KB0055.proved) Eq.refl Eq.refl

  p7 : CCX12 • X1 • SWAP12 • CX12 ≈ CCX12 • X1 • CX12 • CX21
  p7 = by-assoc-and (under (CCX12 • X1) (ε) KB0061.proved) Eq.refl Eq.refl

  p8 : CCX12 • SWAP12 • X2 • CX12 ≈ CCX12 • X1 • CX12 • CX21
  p8 = trans p6 (trans p7 (refl))

  p9 : X1 • CX12 • CX21 • CCX12 ≈ CCX12 • X1 • CX12 • CX21
  p9 = trans (sym p5) (trans p2 p8)

  p10 : CCX12 • X1 • CX12 • CX21 ≈ X1 • CX12 • CX21 • CCX12
  p10 = sym p9

  proved : CCX12 • X1 • CX12 • CX21 ≈ X1 • CX12 • CX21 • CCX12
  proved = p10

module KB1209 where

  p0 : CCX02 • CX12 • CCX01 • X2 ≈ CX12 • CCX01 • CCX02 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0308.proved) Eq.refl Eq.refl

  p1 : CCX02 • CX12 • CCX01 • X2 ≈ CCX02 • CX12 • X2 • CCX01
  p1 = by-assoc-and (under (CCX02 • CX12) (ε) KB0029.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX01 • CCX02 • X2 ≈ CCX02 • CX12 • X2 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX01 • CCX02 • X2 ≈ CX12 • CCX01 • CCX02 • X2
  p3 = refl

  p4 : CCX02 • CX12 • X2 • CCX01 ≈ CCX02 • X2 • CX12 • CCX01
  p4 = by-assoc-and (under (CCX02) (CCX01) KB0036.proved) Eq.refl Eq.refl

  p5 : CCX02 • CX12 • X2 • CCX01 ≈ CCX02 • X2 • CX12 • CCX01
  p5 = trans p4 (refl)

  p6 : CX12 • CCX01 • CCX02 • X2 ≈ CCX02 • X2 • CX12 • CCX01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX02 • X2 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02 • X2
  p7 = sym p6

  proved : CCX02 • X2 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02 • X2
  proved = p7

module KB1272 where

  p0 : CCX01 • CCX02 • CX12 • X2 ≈ CX12 • CCX02 • CCX01 • X2
  p0 = by-assoc-and (under (ε) (X2) KB0334.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CX12 • X2 ≈ CCX01 • CCX02 • X2 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0036.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX01 • X2 ≈ CCX01 • CCX02 • X2 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX01 • X2 ≈ CX12 • CCX02 • X2 • CCX01
  p3 = by-assoc-and (under (CX12 • CCX02) (ε) KB0029.proved) Eq.refl Eq.refl

  p4 : CX12 • CCX02 • CCX01 • X2 ≈ CX12 • CCX02 • X2 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • CCX02 • X2 • CX12 ≈ CCX01 • CCX02 • X2 • CX12
  p5 = refl

  p6 : CX12 • CCX02 • X2 • CCX01 ≈ CCX01 • CCX02 • X2 • CX12
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • CCX02 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01
  p7 = sym p6

  proved : CCX01 • CCX02 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01
  proved = p7

module KB1273 where

  p0 : CCX01 • CCX02 • CX12 • X0 ≈ CX12 • CCX02 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0334.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CX12 • X0 ≈ CCX01 • CCX02 • X0 • CX12
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0045.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CCX01 • X0 ≈ CCX01 • CCX02 • X0 • CX12
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0
  p3 = refl

  p4 : CCX01 • CCX02 • X0 • CX12 ≈ CCX01 • CCX02 • X0 • CX12
  p4 = refl

  p5 : CX12 • CCX02 • CCX01 • X0 ≈ CCX01 • CCX02 • X0 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX02 • X0 • CX12 ≈ CX12 • CCX02 • CCX01 • X0
  p6 = sym p5

  proved : CCX01 • CCX02 • X0 • CX12 ≈ CX12 • CCX02 • CCX01 • X0
  proved = p6

module KB1329 where

  p0 : CCX02 • X0 • CX12 • CX21 • CCX02 ≈ X0 • CCX02 • SWAP12 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0561.proved) Eq.refl Eq.refl

  p1 : CCX02 • X0 • CX12 • CX21 • CCX02 ≈ CCX02 • CX12 • CCX02 • X0
  p1 = by-assoc-and (under (CCX02) (ε) KB0417.proved) Eq.refl Eq.refl

  p2 : X0 • CCX02 • SWAP12 • CCX02 ≈ CCX02 • CX12 • CCX02 • X0
  p2 = trans (sym p0) p1

  p3 : X0 • CCX02 • SWAP12 • CCX02 ≈ X0 • CCX02 • CCX01 • SWAP12
  p3 = by-assoc-and (under (X0 • CCX02) (ε) KB0108.proved) Eq.refl Eq.refl

  p4 : X0 • CCX02 • SWAP12 • CCX02 ≈ X0 • CCX02 • CCX01 • SWAP12
  p4 = trans p3 (refl)

  p5 : CCX02 • CX12 • CCX02 • X0 ≈ CX12 • CCX02 • CCX01 • X0
  p5 = by-assoc-and (under (ε) (X0) KB0332.proved) Eq.refl Eq.refl

  p6 : CCX02 • CX12 • CCX02 • X0 ≈ CX12 • CCX02 • CCX01 • X0
  p6 = trans p5 (refl)

  p7 : X0 • CCX02 • CCX01 • SWAP12 ≈ CX12 • CCX02 • CCX01 • X0
  p7 = trans (sym p4) (trans p2 p6)

  p8 : CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • SWAP12
  p8 = sym p7

  proved : CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • SWAP12
  proved = p8

module KB1363 where

  p0 : CCX12 • CCX12 • CX12 • CCX02 • CX10 ≈ CCX12 • CX12 • CCX02 • CCX12
  p0 = by-assoc-and (under (CCX12) (ε) KB1362.proved) Eq.refl Eq.refl

  p1 : CCX12 • CCX12 • CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10
  p1 = by-assoc-and (under (ε) (CX12 • CCX02 • CX10) KB0014.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX12 • CCX02 • CCX12 ≈ CCX12 • CX12 • CCX02 • CCX12
  p3 = refl

  p4 : CX12 • CCX02 • CX10 ≈ CX12 • CCX02 • CX10
  p4 = refl

  p5 : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • CX12 • CCX02 • CCX12 ≈ CX12 • CCX02 • CX10
  proved = p5

module KB1365 where

  p0 : CX20 • CX01 • CCX12 • CX01 • CCX12 ≈ CX20 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX20) (ε) KB0338.proved) Eq.refl Eq.refl

  p1 : CX20 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21 • CX01 • CCX12
  p1 = by-assoc-and (under (ε) (CX01 • CCX12) KB0306.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX21 • CX01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX12 • CCX02 ≈ CX20 • CCX12 • CCX02
  p3 = refl

  p4 : CX01 • CCX12 • CX21 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
  p4 = by-assoc-and (under (CX01 • CCX12) (CCX12) KB0030.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX12 • CX21 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
  p5 = trans p4 (refl)

  p6 : CX20 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CX20 • CCX12 • CCX02
  p7 = sym p6

  proved : CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CX20 • CCX12 • CCX02
  proved = p7

module KB1366 where

  p0 : CX01 • CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CX01 • CX20 • CCX12 • CCX02
  p0 = by-assoc-and (under (CX01) (ε) KB1365.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CCX12 • CX01 • CX21 • CCX12
  p1 = by-assoc-and (under (ε) (CCX12 • CX01 • CX21 • CCX12) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CX20 • CCX12 • CCX02 ≈ CCX12 • CX01 • CX21 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX01 • CX20 • CCX12 • CCX02 ≈ CX01 • CX20 • CCX12 • CCX02
  p3 = refl

  p4 : CCX12 • CX01 • CX21 • CCX12 ≈ CCX12 • CX01 • CX21 • CCX12
  p4 = refl

  p5 : CX01 • CX20 • CCX12 • CCX02 ≈ CCX12 • CX01 • CX21 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • CX01 • CX21 • CCX12 ≈ CX01 • CX20 • CCX12 • CCX02
  p6 = sym p5

  proved : CCX12 • CX01 • CX21 • CCX12 ≈ CX01 • CX20 • CCX12 • CCX02
  proved = p6

module KB1376 where

  p0 : CX12 • CCX02 • CCX01 • SWAP12 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0 • SWAP12
  p0 = by-assoc-and (under (ε) (SWAP12) KB0818.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • CCX01 • SWAP12 • SWAP12 ≈ CX12 • CCX02 • CCX01
  p1 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) KB0001.proved) Eq.refl Eq.refl

  p2 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CCX02 • CCX01 • X0 • SWAP12
  p3 = refl

  p4 : CX12 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
  p4 = refl

  p5 : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CX12 • CCX02 • CCX01
  proved = p5

module KB1377 where

  p0 : X0 • X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
  p0 = by-assoc-and (under (X0) (ε) KB1376.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • CCX02 • CCX01 • X0 • SWAP12 ≈ CCX02 • CCX01 • X0 • SWAP12
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • X0 • SWAP12) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • X0 • SWAP12
  p2 = trans (sym p0) p1

  p3 : X0 • CX12 • CCX02 • CCX01 ≈ X0 • CX12 • CCX02 • CCX01
  p3 = refl

  p4 : CCX02 • CCX01 • X0 • SWAP12 ≈ CCX02 • CCX01 • X0 • SWAP12
  p4 = refl

  p5 : X0 • CX12 • CCX02 • CCX01 ≈ CCX02 • CCX01 • X0 • SWAP12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
  p6 = sym p5

  proved : CCX02 • CCX01 • X0 • SWAP12 ≈ X0 • CX12 • CCX02 • CCX01
  proved = p6

module KB1576 where

  p0 : CX10 • CCX12 • CX12 • CCX01 • CX01 ≈ CX10 • CCX12 • CX01 • CX12 • CCX01
  p0 = by-assoc-and (under (CX10 • CCX12) (ε) KB0283.proved) Eq.refl Eq.refl

  p1 : CX10 • CCX12 • CX12 • CCX01 • CX01 ≈ CX12 • CCX12 • CCX01 • CX01
  p1 = by-assoc-and (under (ε) (CCX01 • CX01) KB0141.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX12 • CX01 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX12 • CX01 • CX12 • CCX01 ≈ CX10 • CCX12 • CX01 • CX12 • CCX01
  p3 = refl

  p4 : CX12 • CCX12 • CCX01 • CX01 ≈ CX12 • CCX12 • CCX01 • CX01
  p4 = refl

  p5 : CX10 • CCX12 • CX01 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX10 • CCX12 • CX01 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CX01
  proved = p5

module KB1720 where

  p0 : X2 • CX01 • CCX02 • CX12 • CCX02 ≈ X2 • CX01 • CX12 • CCX02 • CCX01
  p0 = by-assoc-and (under (X2 • CX01) (ε) KB0332.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • CCX02 • CX12 • CCX02 ≈ CCX02 • X2 • CX12 • CCX02
  p1 = by-assoc-and (under (ε) (CX12 • CCX02) KB0122.proved) Eq.refl Eq.refl

  p2 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
  p2 = trans (sym p0) p1

  p3 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ X2 • CX01 • CX12 • CCX02 • CCX01
  p3 = refl

  p4 : CCX02 • X2 • CX12 • CCX02 ≈ CCX02 • X2 • CX12 • CCX02
  p4 = refl

  p5 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
  proved = p5

module KB1761 where

  p0 : CCX02 • CCX12 • CX01 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
  p0 = by-assoc-and (under (ε) (CX02 • CCX01) KB0341.proved) Eq.refl Eq.refl

  p1 : CCX02 • CCX12 • CX01 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p1 = by-assoc-and (under (CCX02 • CCX12) (ε) KB0123.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
  p3 = refl

  p4 : CCX02 • CCX12 • CCX01 • CX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p4 = refl

  p5 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
  proved = p5

module KB2234 where

  p0 : CX12 • X2 • CX10 • CCX02 • X2 ≈ CX12 • CX01 • CCX12 • SWAP01
  p0 = by-assoc-and (under (CX12) (ε) KB0486.proved) Eq.refl Eq.refl

  p1 : CX12 • X2 • CX10 • CCX02 • X2 ≈ X2 • CX12 • CX10 • CCX02 • X2
  p1 = by-assoc-and (under (ε) (CX10 • CCX02 • X2) KB0036.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • CCX12 • SWAP01 ≈ X2 • CX12 • CX10 • CCX02 • X2
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX10 • CX12 • CX01 • CCX02
  p3 = by-assoc-and (under (ε) (ε) KB1100.proved) Eq.refl Eq.refl

  p4 : CX10 • CX12 • CX01 • CCX02 ≈ CX02 • CX10 • CCX02 • CX02
  p4 = by-assoc-and (under (ε) (ε) KB1661.proved) Eq.refl Eq.refl

  p5 : CX12 • CX01 • CCX12 • SWAP01 ≈ CX02 • CX10 • CCX02 • CX02
  p5 = trans p3 (trans p4 (refl))

  p6 : X2 • CX12 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CX12 • CCX02 • X2
  p6 = by-assoc-and (under (X2) (CCX02 • X2) KB0026.proved) Eq.refl Eq.refl

  p7 : X2 • CX12 • CX10 • CCX02 • X2 ≈ X2 • CX10 • CX12 • CCX02 • X2
  p7 = trans p6 (refl)

  p8 : CX02 • CX10 • CCX02 • CX02 ≈ X2 • CX10 • CX12 • CCX02 • X2
  p8 = trans (sym p5) (trans p2 p7)

  p9 : X2 • CX10 • CX12 • CCX02 • X2 ≈ CX02 • CX10 • CCX02 • CX02
  p9 = sym p8

  proved : X2 • CX10 • CX12 • CCX02 • X2 ≈ CX02 • CX10 • CCX02 • CX02
  proved = p9

module KB2769 where

  p0 : X2 • CX01 • X0 • CX02 • CCX01 ≈ X2 • X0 • X1 • CCX01 • CX01
  p0 = by-assoc-and (under (X2) (ε) KB0753.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • X0 • CX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01) KB0586.proved) Eq.refl Eq.refl

  p2 : X2 • X0 • X1 • CCX01 • CX01 ≈ CX01 • CX02 • X0 • CCX01
  p2 = trans (sym p0) p1

  p3 : X2 • X0 • X1 • CCX01 • CX01 ≈ X0 • X2 • X1 • CCX01 • CX01
  p3 = by-assoc-and (under (ε) (X1 • CCX01 • CX01) KB0018.proved) Eq.refl Eq.refl

  p4 : X0 • X2 • X1 • CCX01 • CX01 ≈ X0 • X1 • X2 • CCX01 • CX01
  p4 = by-assoc-and (under (X0) (CCX01 • CX01) KB0019.proved) Eq.refl Eq.refl

  p5 : X2 • X0 • X1 • CCX01 • CX01 ≈ X0 • X1 • X2 • CCX01 • CX01
  p5 = trans p3 (trans p4 (refl))

  p6 : CX01 • CX02 • X0 • CCX01 ≈ CX01 • CX02 • X0 • CCX01
  p6 = refl

  p7 : X0 • X1 • X2 • CCX01 • CX01 ≈ CX01 • CX02 • X0 • CCX01
  p7 = trans (sym p5) (trans p2 p6)

  proved : X0 • X1 • X2 • CCX01 • CX01 ≈ CX01 • CX02 • X0 • CCX01
  proved = p7

module KB3112 where

  p0 : CCX12 • X2 • CX12 • CCX01 • CX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
  p0 = by-assoc-and (under (ε) (CCX01 • CX01) KB0287.proved) Eq.refl Eq.refl

  p1 : CCX12 • X2 • CX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
  p1 = by-assoc-and (under (CCX12 • X2) (ε) KB0283.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
  p3 = refl

  p4 : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
  p4 = refl

  p5 : X2 • CX12 • CCX12 • CCX01 • CX01 ≈ CCX12 • X2 • CX01 • CX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
  p6 = sym p5

  proved : CCX12 • X2 • CX01 • CX12 • CCX01 ≈ X2 • CX12 • CCX12 • CCX01 • CX01
  proved = p6

module KB3123 where

  p0 : CCX01 • CCX12 • CX12 • CX21 • X2 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
  p0 = by-assoc-and (under (ε) (CX21 • X2) KB0293.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX12 • CX12 • CX21 • X2 ≈ CCX01 • CCX12 • X1 • CX12 • CX21
  p1 = by-assoc-and (under (CCX01 • CCX12) (ε) KB0234.proved) Eq.refl Eq.refl

  p2 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CCX01 • CCX12 • X1 • CX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
  p3 = refl

  p4 : CCX01 • CCX12 • X1 • CX12 • CX21 ≈ CCX01 • X1 • CX12 • CX21 • CCX12
  p4 = by-assoc-and (under (CCX01) (ε) KB1173.proved) Eq.refl Eq.refl

  p5 : CCX01 • X1 • CX12 • CX21 • CCX12 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
  p5 = by-assoc-and (under (ε) (CCX12) KB0997.proved) Eq.refl Eq.refl

  p6 : CCX01 • CCX12 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
  p6 = trans p4 (trans p5 (refl))

  p7 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
  p7 = trans (sym p3) (trans p2 p6)

  p8 : CX12 • CCX01 • CX21 • X2 • CCX12 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
  p8 = sym p7

  proved : CX12 • CCX01 • CX21 • X2 • CCX12 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
  proved = p8
