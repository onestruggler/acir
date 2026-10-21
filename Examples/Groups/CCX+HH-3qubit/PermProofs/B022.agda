{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B022 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX10 ; CX12 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0006 ; module KB0011 ; module KB0012 ; module KB0026 ; module KB0029 ; module KB0118 ; module KB0147 ; module KB0153 ; module KB0215 ; module KB0219)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B002 using (module KB0004 ; module KB0018 ; module KB0045 ; module KB0214 ; module KB0221)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B003 using (module KB0021 ; module KB0047 ; module KB0140 ; module KB0180 ; module KB0280 ; module KB0366)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B006 using (module KB0813)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B008 using (module KB0481)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B019 using (module KB0181 ; module KB0331 ; module KB0519)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B020 using (module KB0963 ; module KB0973 ; module KB1209 ; module KB1363 ; module KB1576)

module braid2 where

  p0 : X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p0 = by-assoc-and (under (ε) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0153.proved) Eq.refl Eq.refl

  p1 : CX12 • CCX01 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p1 = by-assoc-and (under (ε) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0140.proved) Eq.refl Eq.refl

  p2 : X0 • CCX01 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X0 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p2 = by-assoc-and (under (X0) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0029.proved) Eq.refl Eq.refl

  p3 : X0 • X2 • CCX01 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X0 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p3 = by-assoc-and (under (X0 • X2) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0011.proved) Eq.refl Eq.refl

  p4 : X0 • X2 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X0 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p4 = by-assoc-and (under (X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0018.proved) Eq.refl Eq.refl

  p5 : X0 • X0 • X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p5 = by-assoc-and (under (ε) (X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0012.proved) Eq.refl Eq.refl

  p6 : X2 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X2 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p6 = by-assoc-and (under (X2) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0215.proved) Eq.refl Eq.refl

  p7 : X2 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X2 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0
  p7 = by-assoc-and (under (X2) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0) KB0219.proved) Eq.refl Eq.refl

  p8 : X2 • CX01 • CCX12 • CX01 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X2 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • X0 • CCX01 • X0
  p8 = by-assoc-and (under (X2 • CX01 • CCX12 • CX01 • X0) (X0 • X0 • CCX01 • X0) KB0029.proved) Eq.refl Eq.refl

  p9 : X2 • CX01 • CCX12 • CX01 • X0 • X2 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X2 • CX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • X0
  p9 = by-assoc-and (under (X2 • CX01 • CCX12) (CCX01 • X0 • X0 • CCX01 • X0) KB0221.proved) Eq.refl Eq.refl

  p10 : X2 • CX01 • CCX12 • X2 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX01 • CX10 • CCX12 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • X0
  p10 = by-assoc-and (under (ε) (CX01 • X0 • CCX01 • X0 • X0 • CCX01 • X0) KB0519.proved) Eq.refl Eq.refl

  p11 : CX01 • CX10 • CCX12 • CX01 • X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX01 • CX10 • CCX12 • CX01 • CX12 • CCX01 • X0 • CCX01 • X0
  p11 = by-assoc-and (under (CX01 • CX10 • CCX12 • CX01) (X0 • CCX01 • X0) KB0153.proved) Eq.refl Eq.refl

  p12 : CX01 • CX10 • CCX12 • CX01 • CX12 • CCX01 • X0 • CCX01 • X0 ≈ CX01 • CX12 • CCX12 • CCX01 • CX01 • X0 • CCX01 • X0
  p12 = by-assoc-and (under (CX01) (X0 • CCX01 • X0) KB1576.proved) Eq.refl Eq.refl

  p13 : CX01 • CX12 • CCX12 • CCX01 • CX01 • X0 • CCX01 • X0 ≈ CX01 • CX12 • CCX12 • CX12 • CX01 • X0 • X0
  p13 = by-assoc-and (under (CX01 • CX12 • CCX12) (X0) KB0813.proved) Eq.refl Eq.refl

  p14 : CX01 • CX12 • CCX12 • CX12 • CX01 • X0 • X0 ≈ CX01 • CX10 • CCX12 • CX01 • X0 • X0
  p14 = by-assoc-and (under (CX01) (CX01 • X0 • X0) KB0181.proved) Eq.refl Eq.refl

  p15 : CX01 • CX10 • CCX12 • CX01 • X0 • X0 ≈ CX01 • CX10 • CCX12 • CX01
  p15 = by-assoc-and (under (CX01 • CX10 • CCX12 • CX01) (ε) KB0012.proved) Eq.refl Eq.refl

  p16 : X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ CX01 • CX10 • CCX12 • CX01
  p16 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (refl))))))))))))))))

  p17 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p17 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0481.proved) Eq.refl Eq.refl

  p18 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p18 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0215.proved) Eq.refl Eq.refl

  p19 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p19 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0118.proved) Eq.refl Eq.refl

  p20 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p20 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p21 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p21 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0029.proved) Eq.refl Eq.refl

  p22 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p22 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p23 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p23 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0366.proved) Eq.refl Eq.refl

  p24 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p24 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p25 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p25 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p26 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p26 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0963.proved) Eq.refl Eq.refl

  p27 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p27 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p28 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p28 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2 • CX10) (CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0045.proved) Eq.refl Eq.refl

  p29 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p29 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p30 : X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p30 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CX10 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p31 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CCX01 • CX10 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p31 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0147.proved) Eq.refl Eq.refl

  p32 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CCX01 • CX10 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CCX01 • X0 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p32 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2 • CCX01) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p33 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CCX01 • X0 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p33 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0481.proved) Eq.refl Eq.refl

  p34 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CX12 • CCX01 • CCX02 • X2 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p34 = by-assoc-and (under (X2 • CX10 • CX12) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB1209.proved) Eq.refl Eq.refl

  p35 : X2 • CX10 • CX12 • CX12 • CCX01 • CCX02 • X2 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p35 = by-assoc-and (under (X2 • CX10) (CCX01 • CCX02 • X2 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0006.proved) Eq.refl Eq.refl

  p36 : X2 • CX10 • CCX01 • CCX02 • X2 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • X0 • CX10 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p36 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X2) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p37 : X2 • CX10 • CCX01 • CCX02 • X2 • X0 • CX10 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p37 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CX10 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0018.proved) Eq.refl Eq.refl

  p38 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X2 • CX10 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p38 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0021.proved) Eq.refl Eq.refl

  p39 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X2 • CX10 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p39 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CX10 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0004.proved) Eq.refl Eq.refl

  p40 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CCX01 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p40 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0366.proved) Eq.refl Eq.refl

  p41 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CCX01 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CCX01 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p41 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0012.proved) Eq.refl Eq.refl

  p42 : X2 • CX10 • CCX01 • CCX02 • CCX01 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX12 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p42 = by-assoc-and (under (X2 • CX10) (CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0214.proved) Eq.refl Eq.refl

  p43 : X2 • CX10 • CX12 • CCX02 • CX12 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX10 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p43 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0026.proved) Eq.refl Eq.refl

  p44 : X2 • CX10 • CX12 • CCX02 • CX10 • CX12 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CCX12 • CX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  p44 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CCX02 • CCX12 • X0 • CCX01 • X2 • X0) KB0180.proved) Eq.refl Eq.refl

  p45 : X2 • CX10 • CX12 • CCX02 • CCX12 • CX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0
  p45 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (X0 • CCX01 • X2 • X0) KB1363.proved) Eq.refl Eq.refl

  p46 : X2 • CX10 • CX12 • CCX02 • CX12 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX02 • CCX01 • CX10 • X0 • CCX01 • X2 • X0
  p46 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • CCX01 • X2 • X0) KB0331.proved) Eq.refl Eq.refl

  p47 : X2 • CX10 • CCX02 • CCX01 • CX10 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX02 • CCX01 • X0 • CX10 • CCX01 • X2 • X0
  p47 = by-assoc-and (under (X2 • CX10 • CCX02 • CCX01) (CCX01 • X2 • X0) KB0047.proved) Eq.refl Eq.refl

  p48 : X2 • CX10 • CCX02 • CCX01 • X0 • CX10 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX02 • X0 • CX10 • CCX01 • CCX01 • X2 • X0
  p48 = by-assoc-and (under (X2 • CX10 • CCX02) (CCX01 • X2 • X0) KB0280.proved) Eq.refl Eq.refl

  p49 : X2 • CX10 • CCX02 • X0 • CX10 • CCX01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CX01 • X0 • CCX01 • CCX01 • X2 • X0
  p49 = by-assoc-and (under (X2) (CCX01 • CCX01 • X2 • X0) KB0973.proved) Eq.refl Eq.refl

  p50 : X2 • CX01 • CCX12 • CX01 • X0 • CCX01 • CCX01 • X2 • X0 ≈ X2 • CX01 • CCX12 • CX01 • X0 • X2 • X0
  p50 = by-assoc-and (under (X2 • CX01 • CCX12 • CX01 • X0) (X2 • X0) KB0011.proved) Eq.refl Eq.refl

  p51 : X2 • CX01 • CCX12 • CX01 • X0 • X2 • X0 ≈ X2 • CX01 • CCX12 • X2 • CX01 • X0 • X0
  p51 = by-assoc-and (under (X2 • CX01 • CCX12) (X0) KB0221.proved) Eq.refl Eq.refl

  p52 : X2 • CX01 • CCX12 • X2 • CX01 • X0 • X0 ≈ CX01 • CX10 • CCX12 • CX01 • X0 • X0
  p52 = by-assoc-and (under (ε) (CX01 • X0 • X0) KB0519.proved) Eq.refl Eq.refl

  p53 : CX01 • CX10 • CCX12 • CX01 • X0 • X0 ≈ CX01 • CX10 • CCX12 • CX01
  p53 = by-assoc-and (under (CX01 • CX10 • CCX12 • CX01) (ε) KB0012.proved) Eq.refl Eq.refl

  p54 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ CX01 • CX10 • CCX12 • CX01
  p54 = trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (trans p31 (trans p32 (trans p33 (trans p34 (trans p35 (trans p36 (trans p37 (trans p38 (trans p39 (trans p40 (trans p41 (trans p42 (trans p43 (trans p44 (trans p45 (trans p46 (trans p47 (trans p48 (trans p49 (trans p50 (trans p51 (trans p52 (trans p53 (refl)))))))))))))))))))))))))))))))))))))

  proved : X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 ≈ X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
  proved = trans p16 (sym p54)
