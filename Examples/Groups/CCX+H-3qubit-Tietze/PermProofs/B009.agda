{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B009 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX20 ; CX21 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0009 ; module KB0010 ; module KB0039)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0007 ; module KB0043 ; module KB0211 ; module KB0328)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0138 ; module KB0223)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B007 using (module KB0317 ; module KB0323 ; module KB1265 ; module KB1266)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0291 ; module KB0325)

module KB5008 where

  p0 : CCX01 • CX21 • CCX01 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX02 • CCX12 • CCX01
  p0 = by-assoc-and (under (ε) (CCX12 • CCX01) KB1266.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX21 • CCX01 • CCX12 • CCX01 ≈ CCX01 • CX21 • CX02 • CCX12 • CX02
  p1 = by-assoc-and (under (CCX01 • CX21) (ε) KB0211.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CCX01 • CX21 • CX02 • CCX12 • CX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX21 • CCX01 • CCX02 • CCX12 • CCX01
  p3 = refl

  p4 : CCX01 • CX21 • CX02 • CCX12 • CX02 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
  p4 = by-assoc-and (under (ε) (CCX12 • CX02) KB0291.proved) Eq.refl Eq.refl

  p5 : CCX01 • CX21 • CX02 • CCX12 • CX02 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
  p5 = trans p4 (refl)

  p6 : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX21 • CCX01 • CCX02 • CCX12 • CCX01 ≈ CX01 • CCX01 • CX21 • CCX12 • CX02
  proved = p6

module KB0179 where

  p0 : CX20 • CX20 • CCX12 • CX21 ≈ CX20 • CX21 • CCX12
  p0 = by-assoc-and (under (CX20) (ε) KB0138.proved) Eq.refl Eq.refl

  p1 : CX20 • CX20 • CCX12 • CX21 ≈ CCX12 • CX21
  p1 = by-assoc-and (under (ε) (CCX12 • CX21) KB0009.proved) Eq.refl Eq.refl

  p2 : CX20 • CX21 • CCX12 ≈ CCX12 • CX21
  p2 = trans (sym p0) p1

  p3 : CX20 • CX21 • CCX12 ≈ CX20 • CX21 • CCX12
  p3 = refl

  p4 : CCX12 • CX21 ≈ CCX12 • CX21
  p4 = refl

  p5 : CX20 • CX21 • CCX12 ≈ CCX12 • CX21
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CX21 • CCX12 ≈ CCX12 • CX21
  proved = p5

module KB1357 where

  p0 : CX21 • CX20 • CCX12 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
  p0 = by-assoc-and (under (CX21) (ε) KB0323.proved) Eq.refl Eq.refl

  p1 : CX21 • CX20 • CCX12 • CCX01 • CX20 ≈ CX20 • CX21 • CCX12 • CCX01 • CX20
  p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX20) KB0043.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX12 ≈ CX20 • CX21 • CCX12 • CCX01 • CX20
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX12 ≈ CX21 • CCX01 • CCX12
  p3 = refl

  p4 : CX20 • CX21 • CCX12 • CCX01 • CX20 ≈ CCX12 • CX21 • CCX01 • CX20
  p4 = by-assoc-and (under (ε) (CCX01 • CX20) KB0179.proved) Eq.refl Eq.refl

  p5 : CX20 • CX21 • CCX12 • CCX01 • CX20 ≈ CCX12 • CX21 • CCX01 • CX20
  p5 = trans p4 (refl)

  p6 : CX21 • CCX01 • CCX12 ≈ CCX12 • CX21 • CCX01 • CX20
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX12 • CX21 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
  p7 = sym p6

  proved : CCX12 • CX21 • CCX01 • CX20 ≈ CX21 • CCX01 • CCX12
  proved = p7

module KB5146 where

  p0 : CCX12 • CX21 • CCX01 • CX20 • X2 • CX20 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
  p0 = by-assoc-and (under (ε) (X2 • CX20) KB1357.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX21 • CCX01 • CX20 • X2 • CX20 ≈ CCX12 • CX21 • CCX01 • X0 • X2
  p1 = by-assoc-and (under (CCX12 • CX21 • CCX01) (ε) KB0317.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CCX12 • CX21 • CCX01 • X0 • X2
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
  p3 = refl

  p4 : CCX12 • CX21 • CCX01 • X0 • X2 ≈ CCX12 • CX21 • X2 • CCX01 • X0
  p4 = by-assoc-and (under (CCX12 • CX21) (ε) KB0223.proved) Eq.refl Eq.refl

  p5 : CCX12 • CX21 • CCX01 • X0 • X2 ≈ CCX12 • CX21 • X2 • CCX01 • X0
  p5 = trans p4 (refl)

  p6 : CX21 • CCX01 • CCX12 • X2 • CX20 ≈ CCX12 • CX21 • X2 • CCX01 • X0
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CCX12 • CX21 • X2 • CCX01 • X0 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
  p7 = sym p6

  proved : CCX12 • CX21 • X2 • CCX01 • X0 ≈ CX21 • CCX01 • CCX12 • X2 • CX20
  proved = p7

module KB0661 where

  p0 : CCX01 • CX20 • CCX12 • CX21 ≈ CX20 • CCX12 • CCX01 • CX21
  p0 = by-assoc-and (under (ε) (CX21) KB0325.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX20 • CCX12 • CX21 ≈ CCX01 • CX21 • CCX12
  p1 = by-assoc-and (under (CCX01) (ε) KB0138.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX12 • CCX01 • CX21 ≈ CX20 • CCX12 • CCX01 • CX21
  p3 = refl

  p4 : CCX01 • CX21 • CCX12 ≈ CCX01 • CX21 • CCX12
  p4 = refl

  p5 : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
  proved = p5

module KB2914 where

  p0 : CX20 • CCX12 • CCX01 • CX21 • CCX01 • CCX02 ≈ CX20 • CCX12 • CX21 • CCX01
  p0 = by-assoc-and (under (CX20 • CCX12) (ε) KB1265.proved) Eq.refl Eq.refl

  p1 : CX20 • CCX12 • CCX01 • CX21 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
  p1 = by-assoc-and (under (ε) (CCX01 • CCX02) KB0661.proved) Eq.refl Eq.refl

  p2 : CX20 • CCX12 • CX21 • CCX01 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX20 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX12 • CCX01
  p3 = by-assoc-and (under (ε) (CCX01) KB0138.proved) Eq.refl Eq.refl

  p4 : CX20 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX12 • CCX01
  p4 = trans p3 (refl)

  p5 : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
  p5 = refl

  p6 : CX21 • CCX12 • CCX01 ≈ CCX01 • CX21 • CCX12 • CCX01 • CCX02
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX12 • CCX01
  p7 = sym p6

  proved : CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX12 • CCX01
  proved = p7

module KB5482 where

  p0 : CX21 • CCX02 • CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CX21 • CCX02 • CX21 • CCX12 • CCX01
  p0 = by-assoc-and (under (CX21 • CCX02) (ε) KB2914.proved) Eq.refl Eq.refl

  p1 : CX21 • CCX02 • CCX01 • CX21 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
  p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CCX02) KB0328.proved) Eq.refl Eq.refl

  p2 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CX21 • CX21 • CCX02 • CCX12 • CCX01
  p3 = by-assoc-and (under (CX21) (CCX12 • CCX01) KB0039.proved) Eq.refl Eq.refl

  p4 : CX21 • CX21 • CCX02 • CCX12 • CCX01 ≈ CCX02 • CCX12 • CCX01
  p4 = by-assoc-and (under (ε) (CCX02 • CCX12 • CCX01) KB0007.proved) Eq.refl Eq.refl

  p5 : CX21 • CCX02 • CX21 • CCX12 • CCX01 ≈ CCX02 • CCX12 • CCX01
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
  p6 = refl

  p7 : CCX02 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01 • CCX02
  p7 = trans (sym p5) (trans p2 p6)

  p8 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01
  p8 = sym p7

  proved : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01
  proved = p8

module KB5483 where

  p0 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB5482.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX12 • CCX01 • CCX02 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
  p1 = by-assoc-and (under (CCX01 • CCX02 • CCX12 • CCX01) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CCX12 • CCX01 • CCX02
  p3 = refl

  p4 : CCX01 • CCX02 • CCX12 • CCX01 ≈ CCX01 • CCX02 • CCX12 • CCX01
  p4 = refl

  p5 : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • CCX12 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX12 • CCX01
  proved = p5
