{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B026 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX02 ; CX10 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0014 ; module KB0026 ; module KB0029 ; module KB0036 ; module KB0118 ; module KB0120 ; module KB0147 ; module KB0215 ; module KB0307)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0004 ; module KB0018 ; module KB0045 ; module KB0150 ; module KB0214)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0047 ; module KB0140 ; module KB0366)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B004 using (module KB0337 ; module KB0623)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0481)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B015 using (module KB0146)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0963)

module invol3 where

  p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0481.proved) Eq.refl Eq.refl

  p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0118.proved) Eq.refl Eq.refl

  p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p5 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p6 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p6 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0366.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p7 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p8 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p8 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p9 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p9 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0963.proved) Eq.refl Eq.refl

  p10 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p10 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p11 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p11 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2 • CX10) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p12 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p12 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p13 : X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p13 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p14 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p14 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0036.proved) Eq.refl Eq.refl

  p15 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • X2 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p15 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p16 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • X2 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p16 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0004.proved) Eq.refl Eq.refl

  p17 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CCX01 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0147.proved) Eq.refl Eq.refl

  p18 : X2 • CX10 • CX12 • CCX02 • X0 • CCX01 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0623.proved) Eq.refl Eq.refl

  p19 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p20 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p21 : X2 • CX10 • CCX01 • CCX02 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CX10 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (X2 • CX10 • CCX01) (CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0337.proved) Eq.refl Eq.refl

  p22 : X2 • CX10 • CCX01 • CX10 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p22 = by-assoc-and (under (X2) (CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0146.proved) Eq.refl Eq.refl

  p23 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX12 • X0 • CCX01 • X2 • X0
  p23 = by-assoc-and (under (X2 • CX12 • CCX01 • CCX12) (CCX12 • X0 • CCX01 • X2 • X0) KB0010.proved) Eq.refl Eq.refl

  p24 : X2 • CX12 • CCX01 • CCX12 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • X0 • CCX01 • X2 • X0
  p24 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0) KB0014.proved) Eq.refl Eq.refl

  p25 : X2 • CX12 • CCX01 • X0 • CCX01 • X2 • X0 ≈ X2 • X0 • CCX01 • CCX01 • X2 • X0
  p25 = by-assoc-and (under (X2) (CCX01 • X2 • X0) KB0140.proved) Eq.refl Eq.refl

  p26 : X2 • X0 • CCX01 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CCX01 • X2 • X0
  p26 = by-assoc-and (under (ε) (CCX01 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p27 : X0 • X2 • CCX01 • CCX01 • X2 • X0 ≈ X0 • X2 • X2 • X0
  p27 = by-assoc-and (under (X0 • X2) (X2 • X0) KB0011.proved) Eq.refl Eq.refl

  p28 : X0 • X2 • X2 • X0 ≈ X0 • X0
  p28 = by-assoc-and (under (X0) (X0) KB0004.proved) Eq.refl Eq.refl

  p29 : X0 • X0 ≈ ε
  p29 = by-assoc-and (under (ε) (ε) KB0012.proved) Eq.refl Eq.refl

  p30 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ ε
  p30 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (refl))))))))))))))))))))))))))))))

  p31 : ε ≈ ε
  p31 = refl

  proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ ε
  proved = trans p30 (sym p31)

module invol4 where

  p0 : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • X1 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1 • CCX01 • X1) KB0150.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • CCX01 • X1 ≈ X1 • CCX01 • CCX01 • X1
  p1 = by-assoc-and (under (ε) (CCX01 • X1) KB0120.proved) Eq.refl Eq.refl

  p2 : X1 • CCX01 • CCX01 • X1 ≈ X1 • X1
  p2 = by-assoc-and (under (X1) (X1) KB0011.proved) Eq.refl Eq.refl

  p3 : X1 • X1 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0003.proved) Eq.refl Eq.refl

  p4 : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ ε
  p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

  p5 : ε ≈ ε
  p5 = refl

  proved : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ ε
  proved = trans p4 (sym p5)

module invol5 where

  p0 : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX02 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p2 : CCX01 • CCX02 • CCX02 • CCX01 ≈ CCX01 • CCX01
  p2 = by-assoc-and (under (CCX01) (CCX01) KB0010.proved) Eq.refl Eq.refl

  p3 : CCX01 • CCX01 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0011.proved) Eq.refl Eq.refl

  p4 : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ ε
  p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

  p5 : ε ≈ ε
  p5 = refl

  proved : CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ ε
  proved = trans p4 (sym p5)

module invol6 where

  p0 : CCX01 • CCX01 ≈ ε
  p0 = by-assoc-and (under (ε) (ε) KB0011.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 ≈ ε
  p1 = trans p0 (refl)

  p2 : ε ≈ ε
  p2 = refl

  proved : CCX01 • CCX01 ≈ ε
  proved = trans p1 (sym p2)
