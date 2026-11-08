{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.B002 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r014 ; r026 ; r028 ; r044 ; refl ; sym ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B000 using (module KB0003 ; module KB0010 ; module KB0011 ; module KB0012 ; module KB0013 ; module KB0023 ; module KB0028 ; module KB0033 ; module KB0035 ; module KB0120 ; module KB0125 ; module KB0127 ; module KB0186 ; module KB0191 ; module KB0192 ; module KB0216 ; module KB0307 ; module KB0477 ; module KB0516 ; module KB0780 ; module KB0795 ; module KB0817 ; module KB1397)
open import Examples.Groups.CCX+HH-3qubit.PermProofs.B001 using (module KB0022 ; module KB0038 ; module KB0119 ; module KB0122 ; module KB0123 ; module KB0137 ; module KB0709 ; module KB1569 ; module KB2158 ; module KB2277 ; module KB3195 ; module KB3819)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B000 using (module drel161 ; module elim_CX10 ; module elim_SWAP01 ; module symmetry_CX_e)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B001 using (module elim_X2)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B002 using (module bifunct_X_SWAP_b ; module bifunct_X_b ; module bifunct_X_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B003 using (module symmetry_CCX_c)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B004 using (module cadd5)
open import Examples.Groups.CCX+HH-3qubit.Tietze.B007 using (module drel56)

module KB4157 where

  p0 : CX12 • CX01 • CX02 • CCX12 • CX01 • CCX01 ≈ CX12 • CX01 • CCX01 • CCX12 • CX01
  p0 = by-assoc-and (under (CX12 • CX01) (ε) KB0709.proved) Eq.refl Eq.refl

  p1 : CX12 • CX01 • CX02 • CCX12 • CX01 • CCX01 ≈ CX01 • CX12 • CCX12 • CX01 • CCX01
  p1 = by-assoc-and (under (ε) (CCX12 • CX01 • CCX01) KB0127.proved) Eq.refl Eq.refl

  p2 : CX12 • CX01 • CCX01 • CCX12 • CX01 ≈ CX01 • CX12 • CCX12 • CX01 • CCX01
  p2 = trans (sym p0) p1

  p3 : CX12 • CX01 • CCX01 • CCX12 • CX01 ≈ CX12 • CX01 • CCX01 • CCX12 • CX01
  p3 = refl

  p4 : CX01 • CX12 • CCX12 • CX01 • CCX01 ≈ CX01 • CX12 • CCX12 • CX01 • CCX01
  p4 = refl

  p5 : CX12 • CX01 • CCX01 • CCX12 • CX01 ≈ CX01 • CX12 • CCX12 • CX01 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX12 • CX01 • CCX01 • CCX12 • CX01 ≈ CX01 • CX12 • CCX12 • CX01 • CCX01
  proved = p5

module decodeCCX12 where

  p0 : CCX12 ≈ CCX12
  p0 = refl

  p1 : CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • X1 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p2 = by-assoc-and (under (CCX02) (X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0186.proved) Eq.refl Eq.refl

  p3 : CCX02 • X1 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X1 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p3 = by-assoc-and (under (ε) (CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p4 : X1 • CCX02 • CX02 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X1 • CCX02 • X1 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p4 = by-assoc-and (under (X1 • CCX02) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0023.proved) Eq.refl Eq.refl

  p5 : X1 • CCX02 • X1 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X1 • X1 • CCX02 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p5 = by-assoc-and (under (X1) (CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p6 : X1 • X1 • CCX02 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p6 = by-assoc-and (under (ε) (CCX02 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0003.proved) Eq.refl Eq.refl

  p7 : CCX02 • CX02 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p7 = by-assoc-and (under (CCX02) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0191.proved) Eq.refl Eq.refl

  p8 : CCX02 • X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p8 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB3819.proved) Eq.refl Eq.refl

  p9 : X0 • CX02 • CCX01 • X0 • CCX02 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CX01 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p9 = by-assoc-and (under (X0 • CX02 • CCX01 • X0) (CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0216.proved) Eq.refl Eq.refl

  p10 : X0 • CX02 • CCX01 • X0 • CX01 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • X0 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p10 = by-assoc-and (under (X0) (CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0780.proved) Eq.refl Eq.refl

  p11 : X0 • X1 • CCX01 • CX01 • X0 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X2 • CX12 • CX01 • CCX01 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p11 = by-assoc-and (under (ε) (CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB2158.proved) Eq.refl Eq.refl

  p12 : X2 • CX12 • CX01 • CCX01 • CCX12 • CX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X2 • CX01 • CX12 • CCX12 • CX01 • CCX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p12 = by-assoc-and (under (X2) (CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB4157.proved) Eq.refl Eq.refl

  p13 : X2 • CX01 • CX12 • CCX12 • CX01 • CCX01 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X2 • CX01 • CX12 • CX01 • CCX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p13 = by-assoc-and (under (X2 • CX01 • CX12) (X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB1397.proved) Eq.refl Eq.refl

  p14 : X2 • CX01 • CX12 • CX01 • CCX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X2 • CX02 • CX12 • CCX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p14 = by-assoc-and (under (X2) (CCX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0192.proved) Eq.refl Eq.refl

  p15 : X2 • CX02 • CX12 • CCX01 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X1 • CX12 • CCX01 • X1 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p15 = by-assoc-and (under (ε) (CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0795.proved) Eq.refl Eq.refl

  p16 : X1 • CX12 • CCX01 • X1 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p16 = by-assoc-and (under (ε) (CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0817.proved) Eq.refl Eq.refl

  p17 : X0 • CX02 • CCX01 • X0 • CCX12 • CCX02 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CX02 • CCX01 • CCX12 • CX21 • CCX02 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p17 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0516.proved) Eq.refl Eq.refl

  p18 : X0 • CX02 • CCX01 • CCX12 • CX21 • CCX02 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CX02 • CX20 • CCX01 • CCX02 • CX20 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p18 = by-assoc-and (under (X0 • CX02) (X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB3195.proved) Eq.refl Eq.refl

  p19 : X0 • CX02 • CX20 • CCX01 • CCX02 • CX20 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ X0 • CCX12 • CX02 • CX21 • CCX02 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p19 = by-assoc-and (under (X0) (X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB1569.proved) Eq.refl Eq.refl

  p20 : X0 • CCX12 • CX02 • CX21 • CCX02 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • X0 • CX02 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p20 = by-assoc-and (under (ε) (X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB2277.proved) Eq.refl Eq.refl

  p21 : CCX12 • CCX02 • X0 • CX02 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • X0 • X2 • CX02 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p21 = by-assoc-and (under (CCX12 • CCX02 • X0) (X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0033.proved) Eq.refl Eq.refl

  p22 : CCX12 • CCX02 • X0 • X2 • CX02 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • CX02 • X0 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p22 = by-assoc-and (under (CCX12 • CCX02) (X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0125.proved) Eq.refl Eq.refl

  p23 : CCX12 • CCX02 • CX02 • X0 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • CX02 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p23 = by-assoc-and (under (CCX12 • CCX02 • CX02) (X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0012.proved) Eq.refl Eq.refl

  p24 : CCX12 • CCX02 • CX02 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • X1 • CX02 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p24 = by-assoc-and (under (CCX12 • CCX02) (CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0023.proved) Eq.refl Eq.refl

  p25 : CCX12 • CCX02 • X1 • CX02 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • X1 • CCX02 • CX02 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p25 = by-assoc-and (under (CCX12) (CX02 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p26 : CCX12 • X1 • CCX02 • CX02 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • CCX01 • X1 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  p26 = by-assoc-and (under (CCX12) (X1 • CCX01 • CCX02 • CCX01 • CCX01) KB0477.proved) Eq.refl Eq.refl

  p27 : CCX12 • CCX02 • CCX01 • X1 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01
  p27 = by-assoc-and (under (CCX12 • CCX02 • CCX01) (CCX01 • CCX02 • CCX01 • CCX01) KB0003.proved) Eq.refl Eq.refl

  p28 : CCX12 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX02 • CCX02 • CCX01 • CCX01
  p28 = by-assoc-and (under (CCX12 • CCX02) (CCX02 • CCX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p29 : CCX12 • CCX02 • CCX02 • CCX01 • CCX01 ≈ CCX12 • CCX01 • CCX01
  p29 = by-assoc-and (under (CCX12) (CCX01 • CCX01) KB0010.proved) Eq.refl Eq.refl

  p30 : CCX12 • CCX01 • CCX01 ≈ CCX12
  p30 = by-assoc-and (under (CCX12) (ε) KB0011.proved) Eq.refl Eq.refl

  p31 : CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX12
  p31 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (trans p30 (refl))))))))))))))))))))))))))))))

  proved : CCX12 ≈ CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • CCX01
  proved = trans p0 (sym p31)

module KB0150 where

  p0 : CX02 • CCX01 • X1 • X1 ≈ X1 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0120.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • X1 • X1 ≈ CX02 • CCX01
  p1 = by-assoc-and (under (CX02 • CCX01) (ε) KB0003.proved) Eq.refl Eq.refl

  p2 : X1 • CCX01 • X1 ≈ CX02 • CCX01
  p2 = trans (sym p0) p1

  p3 : X1 • CCX01 • X1 ≈ X1 • CCX01 • X1
  p3 = refl

  p4 : CX02 • CCX01 ≈ CX02 • CCX01
  p4 = refl

  p5 : X1 • CCX01 • X1 ≈ CX02 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : X1 • CCX01 • X1 ≈ CX02 • CCX01
  proved = p5

module KB0214 where

  p0 : CX12 • CCX02 • CX12 ≈ CCX01 • CCX02 • CCX01
  p0 = cadd5.proved

  p1 : CX12 • CCX02 • CX12 ≈ CX12 • CCX02 • CX12
  p1 = refl

  p2 : CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01
  p2 = refl

  p3 : CX12 • CCX02 • CX12 ≈ CCX01 • CCX02 • CCX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
  p4 = sym p3

  proved : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
  proved = p4

module KB0149 where

  p0 : CX01 • CX01 • CCX02 • CX02 ≈ CX01 • CX02 • CCX02
  p0 = by-assoc-and (under (CX01) (ε) KB0119.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CCX02 • CX02 ≈ CCX02 • CX02
  p1 = by-assoc-and (under (ε) (CCX02 • CX02) KB0013.proved) Eq.refl Eq.refl

  p2 : CX01 • CX02 • CCX02 ≈ CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CX02 • CCX02 ≈ CX01 • CX02 • CCX02
  p3 = refl

  p4 : CCX02 • CX02 ≈ CCX02 • CX02
  p4 = refl

  p5 : CX01 • CX02 • CCX02 ≈ CCX02 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • CX02 • CCX02 ≈ CCX02 • CX02
  proved = p5

module KB0156 where

  p0 : CX01 • CX02 • CCX01 • CCX01 ≈ CCX01 • CX01 • CCX01
  p0 = by-assoc-and (under (ε) (CCX01) KB0123.proved) Eq.refl Eq.refl

  p1 : CX01 • CX02 • CCX01 • CCX01 ≈ CX01 • CX02
  p1 = by-assoc-and (under (CX01 • CX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CCX01 ≈ CCX01 • CX01 • CCX01
  p3 = refl

  p4 : CX01 • CX02 ≈ CX01 • CX02
  p4 = refl

  p5 : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
  proved = p5

module KB0189 where

  p0 : CCX01 • CCX01 • CX01 • CCX01 ≈ CCX01 • CX01 • CX02
  p0 = by-assoc-and (under (CCX01) (ε) KB0156.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX01 • CX01 • CCX01 ≈ CX01 • CCX01
  p1 = by-assoc-and (under (ε) (CX01 • CCX01) KB0011.proved) Eq.refl Eq.refl

  p2 : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
  p2 = trans (sym p0) p1

  p3 : CCX01 • CX01 • CX02 ≈ CCX01 • CX01 • CX02
  p3 = refl

  p4 : CX01 • CCX01 ≈ CX01 • CCX01
  p4 = refl

  p5 : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX01 • CX01 • CX02 ≈ CX01 • CCX01
  proved = p5

module KB0292 where

  p0 : CCX01 • CX01 • CX02 • CCX02 ≈ CX01 • CCX01 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0189.proved) Eq.refl Eq.refl

  p1 : CCX01 • CX01 • CX02 • CCX02 ≈ CCX01 • CCX02 • CX02
  p1 = by-assoc-and (under (CCX01) (ε) KB0149.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CCX02 ≈ CX01 • CCX01 • CCX02
  p3 = refl

  p4 : CCX01 • CCX02 • CX02 ≈ CCX01 • CCX02 • CX02
  p4 = refl

  p5 : CX01 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CCX01 • CCX02 • CX02 ≈ CX01 • CCX01 • CCX02
  p6 = sym p5

  proved : CCX01 • CCX02 • CX02 ≈ CX01 • CCX01 • CCX02
  proved = p6

module KB0435 where

  p0 : CX02 • CCX01 • CX01 • X1 ≈ CX01 • CCX01 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0137.proved) Eq.refl Eq.refl

  p1 : CX02 • CCX01 • CX01 • X1 ≈ CX02 • CCX01 • X1 • CX01
  p1 = by-assoc-and (under (CX02 • CCX01) (ε) KB0035.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • X1 ≈ CX02 • CCX01 • X1 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • X1 ≈ CX01 • CCX01 • X1
  p3 = refl

  p4 : CX02 • CCX01 • X1 • CX01 ≈ X1 • CCX01 • CX01
  p4 = by-assoc-and (under (ε) (CX01) KB0120.proved) Eq.refl Eq.refl

  p5 : CX02 • CCX01 • X1 • CX01 ≈ X1 • CCX01 • CX01
  p5 = trans p4 (refl)

  p6 : CX01 • CCX01 • X1 ≈ X1 • CCX01 • CX01
  p6 = trans (sym p3) (trans p2 p5)

  proved : CX01 • CCX01 • X1 ≈ X1 • CCX01 • CX01
  proved = p6

module KB1182 where

  p0 : CCX01 • CCX02 • CX02 • X1 ≈ CX01 • CCX01 • CCX02 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0292.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CX02 • X1 ≈ CCX01 • CCX02 • X1 • CX02
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0023.proved) Eq.refl Eq.refl

  p2 : CX01 • CCX01 • CCX02 • X1 ≈ CCX01 • CCX02 • X1 • CX02
  p2 = trans (sym p0) p1

  p3 : CX01 • CCX01 • CCX02 • X1 ≈ CX01 • CCX01 • X1 • CCX02
  p3 = by-assoc-and (under (CX01 • CCX01) (ε) KB0028.proved) Eq.refl Eq.refl

  p4 : CX01 • CCX01 • X1 • CCX02 ≈ X1 • CCX01 • CX01 • CCX02
  p4 = by-assoc-and (under (ε) (CCX02) KB0435.proved) Eq.refl Eq.refl

  p5 : CX01 • CCX01 • CCX02 • X1 ≈ X1 • CCX01 • CX01 • CCX02
  p5 = trans p3 (trans p4 (refl))

  p6 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
  p6 = by-assoc-and (under (CCX01) (CX02) KB0028.proved) Eq.refl Eq.refl

  p7 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
  p7 = trans p6 (refl)

  p8 : X1 • CCX01 • CX01 • CCX02 ≈ CCX01 • X1 • CCX02 • CX02
  p8 = trans (sym p5) (trans p2 p7)

  p9 : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
  p9 = sym p8

  proved : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
  proved = p9

module KB1438 where

  p0 : CCX01 • CCX02 • CCX01 • X1 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01
  p0 = by-assoc-and (under (ε) (X1 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p1 : CCX01 • CCX02 • CCX01 • X1 • CCX01 ≈ CCX01 • CCX02 • X1 • CX02
  p1 = by-assoc-and (under (CCX01 • CCX02) (ε) KB0186.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ CCX01 • CCX02 • X1 • CX02
  p2 = trans (sym p0) p1

  p3 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01
  p3 = refl

  p4 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
  p4 = by-assoc-and (under (CCX01) (CX02) KB0028.proved) Eq.refl Eq.refl

  p5 : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
  p5 = by-assoc-and (under (ε) (ε) KB1182.proved) Eq.refl Eq.refl

  p6 : CCX01 • CCX02 • X1 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
  p6 = trans p4 (trans p5 (refl))

  p7 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02
  p7 = trans (sym p3) (trans p2 p6)

  proved : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02
  proved = p7

module decodeCX01 where

  p0 : CX01 ≈ CX01
  p0 = refl

  p1 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p1 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p2 : CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  p2 = by-assoc-and (under (ε) (X1 • CCX01 • CCX01 • CCX02 • CCX01) KB1438.proved) Eq.refl Eq.refl

  p3 : X1 • CCX01 • CX01 • CCX02 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • CX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p3 = by-assoc-and (under (X1 • CCX01 • CX01) (CCX01 • CCX01 • CCX02 • CCX01) KB0028.proved) Eq.refl Eq.refl

  p4 : X1 • CCX01 • CX01 • X1 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ X1 • CCX01 • X1 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p4 = by-assoc-and (under (X1 • CCX01) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) KB0035.proved) Eq.refl Eq.refl

  p5 : X1 • CCX01 • X1 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX02 • CCX01 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p5 = by-assoc-and (under (ε) (CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01) KB0150.proved) Eq.refl Eq.refl

  p6 : CX02 • CCX01 • CX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01
  p6 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • CCX02 • CCX01) KB0137.proved) Eq.refl Eq.refl

  p7 : CX01 • CCX01 • CCX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01
  p7 = by-assoc-and (under (CX01) (CCX01 • CCX02 • CCX01) KB0214.proved) Eq.refl Eq.refl

  p8 : CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX02 • CCX01
  p8 = by-assoc-and (under (CX01) (CCX02 • CCX01) KB0307.proved) Eq.refl Eq.refl

  p9 : CX01 • CCX01 • CCX02 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX01
  p9 = by-assoc-and (under (CX01 • CCX01) (CCX01) KB0010.proved) Eq.refl Eq.refl

  p10 : CX01 • CCX01 • CCX01 ≈ CX01
  p10 = by-assoc-and (under (CX01) (ε) KB0011.proved) Eq.refl Eq.refl

  p11 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01
  p11 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))))))

  proved : CX01 ≈ CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX01 • CCX02 • CCX01
  proved = trans p0 (sym p11)

module decodeCX02 where

  p0 : CX02 ≈ CX02
  p0 = refl

  p1 : X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX01 • CCX01
  p1 = by-assoc-and (under (ε) (CCX01) KB0150.proved) Eq.refl Eq.refl

  p2 : CX02 • CCX01 • CCX01 ≈ CX02
  p2 = by-assoc-and (under (CX02) (ε) KB0011.proved) Eq.refl Eq.refl

  p3 : X1 • CCX01 • X1 • CCX01 ≈ CX02
  p3 = trans p1 (trans p2 (refl))

  proved : CX02 ≈ X1 • CCX01 • X1 • CCX01
  proved = trans p0 (sym p3)

module KB0004 where

  p0 : X2 • X2 ≈ ε
  p0 = elim_X2.proved

  p1 : X2 • X2 ≈ X2 • X2
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : X2 • X2 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : X2 • X2 ≈ ε
  proved = p3

module KB0016 where

  p0 : X2 • SWAP01 ≈ SWAP01 • X2
  p0 = bifunct_X_SWAP_b.proved

  p1 : X2 • SWAP01 ≈ X2 • SWAP01
  p1 = refl

  p2 : SWAP01 • X2 ≈ SWAP01 • X2
  p2 = refl

  p3 : X2 • SWAP01 ≈ SWAP01 • X2
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • X2 ≈ X2 • SWAP01
  p4 = sym p3

  proved : SWAP01 • X2 ≈ X2 • SWAP01
  proved = p4

module KB0019 where

  p0 : X1 • X2 ≈ X2 • X1
  p0 = bifunct_X_c.proved

  p1 : X1 • X2 ≈ X1 • X2
  p1 = refl

  p2 : X2 • X1 ≈ X2 • X1
  p2 = refl

  p3 : X1 • X2 ≈ X2 • X1
  p3 = trans (sym p1) (trans p0 p2)

  p4 : X2 • X1 ≈ X1 • X2
  p4 = sym p3

  proved : X2 • X1 ≈ X1 • X2
  proved = p4

module KB0045 where

  p0 : CX12 • X0 ≈ X0 • CX12
  p0 = by-assoc-and (axiom r026) Eq.refl Eq.refl

  p1 : CX12 • X0 ≈ CX12 • X0
  p1 = refl

  p2 : X0 • CX12 ≈ X0 • CX12
  p2 = refl

  p3 : CX12 • X0 ≈ X0 • CX12
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX12 • X0 ≈ X0 • CX12
  proved = p3

module KB0000 where

  p0 : SWAP01 • SWAP01 ≈ ε
  p0 = elim_SWAP01.proved

  p1 : SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : SWAP01 • SWAP01 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : SWAP01 • SWAP01 ≈ ε
  proved = p3

module KB0073 where

  p0 : CCX01 ≈ SWAP01 • CCX01 • SWAP01
  p0 = symmetry_CCX_c.proved

  p1 : CCX01 ≈ CCX01
  p1 = refl

  p2 : SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01
  p2 = refl

  p3 : CCX01 ≈ SWAP01 • CCX01 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • CCX01 • SWAP01 ≈ CCX01
  p4 = sym p3

  proved : SWAP01 • CCX01 • SWAP01 ≈ CCX01
  proved = p4

module KB0074 where

  p0 : SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01
  p0 = by-assoc-and (under (SWAP01) (ε) KB0073.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ CCX01 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX01 • SWAP01) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CCX01 ≈ CCX01 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CCX01 ≈ SWAP01 • CCX01
  p3 = refl

  p4 : CCX01 • SWAP01 ≈ CCX01 • SWAP01
  p4 = refl

  p5 : SWAP01 • CCX01 ≈ CCX01 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CCX01 ≈ CCX01 • SWAP01
  proved = p5

module KB0089 where

  p0 : CCX02 ≈ SWAP01 • CCX12 • SWAP01
  p0 = by-assoc-and (axiom r014) Eq.refl Eq.refl

  p1 : CCX02 ≈ CCX02
  p1 = refl

  p2 : SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01
  p2 = refl

  p3 : CCX02 ≈ SWAP01 • CCX12 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • CCX12 • SWAP01 ≈ CCX02
  p4 = sym p3

  proved : SWAP01 • CCX12 • SWAP01 ≈ CCX02
  proved = p4

module KB0090 where

  p0 : SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX02
  p0 = by-assoc-and (under (SWAP01) (ε) KB0089.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ CCX12 • SWAP01
  p1 = by-assoc-and (under (ε) (CCX12 • SWAP01) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CCX02 ≈ CCX12 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CCX02 ≈ SWAP01 • CCX02
  p3 = refl

  p4 : CCX12 • SWAP01 ≈ CCX12 • SWAP01
  p4 = refl

  p5 : SWAP01 • CCX02 ≈ CCX12 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CCX02 ≈ CCX12 • SWAP01
  proved = p5

module KB0091 where

  p0 : SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ CCX02 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0089.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12
  p1 = by-assoc-and (under (SWAP01 • CCX12) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : CCX02 • SWAP01 ≈ SWAP01 • CCX12
  p2 = trans (sym p0) p1

  p3 : CCX02 • SWAP01 ≈ CCX02 • SWAP01
  p3 = refl

  p4 : SWAP01 • CCX12 ≈ SWAP01 • CCX12
  p4 = refl

  p5 : CCX02 • SWAP01 ≈ SWAP01 • CCX12
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP01 • CCX12 ≈ CCX02 • SWAP01
  p6 = sym p5

  proved : SWAP01 • CCX12 ≈ CCX02 • SWAP01
  proved = p6

module KB0095 where

  p0 : X1 ≈ SWAP01 • X0 • SWAP01
  p0 = by-assoc-and (axiom r028) Eq.refl Eq.refl

  p1 : X1 ≈ X1
  p1 = refl

  p2 : SWAP01 • X0 • SWAP01 ≈ SWAP01 • X0 • SWAP01
  p2 = refl

  p3 : X1 ≈ SWAP01 • X0 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • X0 • SWAP01 ≈ X1
  p4 = sym p3

  proved : SWAP01 • X0 • SWAP01 ≈ X1
  proved = p4

module KB0096 where

  p0 : SWAP01 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • X1
  p0 = by-assoc-and (under (SWAP01) (ε) KB0095.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • X0 • SWAP01 ≈ X0 • SWAP01
  p1 = by-assoc-and (under (ε) (X0 • SWAP01) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • X1 ≈ X0 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • X1 ≈ SWAP01 • X1
  p3 = refl

  p4 : X0 • SWAP01 ≈ X0 • SWAP01
  p4 = refl

  p5 : SWAP01 • X1 ≈ X0 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • X1 ≈ X0 • SWAP01
  proved = p5

module KB0097 where

  p0 : SWAP01 • X0 • SWAP01 • SWAP01 ≈ X1 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0095.proved) Eq.refl Eq.refl

  p1 : SWAP01 • X0 • SWAP01 • SWAP01 ≈ SWAP01 • X0
  p1 = by-assoc-and (under (SWAP01 • X0) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : X1 • SWAP01 ≈ SWAP01 • X0
  p2 = trans (sym p0) p1

  p3 : X1 • SWAP01 ≈ X1 • SWAP01
  p3 = refl

  p4 : SWAP01 • X0 ≈ SWAP01 • X0
  p4 = refl

  p5 : X1 • SWAP01 ≈ SWAP01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : SWAP01 • X0 ≈ X1 • SWAP01
  p6 = sym p5

  proved : SWAP01 • X0 ≈ X1 • SWAP01
  proved = p6

module KB0155 where

  p0 : X2 • CX01 • CCX02 • CCX02 ≈ CCX02 • X2 • CCX02
  p0 = by-assoc-and (under (ε) (CCX02) KB0122.proved) Eq.refl Eq.refl

  p1 : X2 • CX01 • CCX02 • CCX02 ≈ X2 • CX01
  p1 = by-assoc-and (under (X2 • CX01) (ε) KB0010.proved) Eq.refl Eq.refl

  p2 : CCX02 • X2 • CCX02 ≈ X2 • CX01
  p2 = trans (sym p0) p1

  p3 : CCX02 • X2 • CCX02 ≈ CCX02 • X2 • CCX02
  p3 = refl

  p4 : X2 • CX01 ≈ X2 • CX01
  p4 = refl

  p5 : CCX02 • X2 • CCX02 ≈ X2 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX02 • X2 • CCX02 ≈ X2 • CX01
  proved = p5

module KB0161 where

  p0 : X0 • X0 • X2 • CX02 ≈ X0 • CX02 • X0
  p0 = by-assoc-and (under (X0) (ε) KB0125.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • X2 • CX02 ≈ X2 • CX02
  p1 = by-assoc-and (under (ε) (X2 • CX02) KB0012.proved) Eq.refl Eq.refl

  p2 : X0 • CX02 • X0 ≈ X2 • CX02
  p2 = trans (sym p0) p1

  p3 : X0 • CX02 • X0 ≈ X0 • CX02 • X0
  p3 = refl

  p4 : X2 • CX02 ≈ X2 • CX02
  p4 = refl

  p5 : X0 • CX02 • X0 ≈ X2 • CX02
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CX02 • X0 ≈ X2 • CX02
  proved = p5

module KB0204 where

  p0 : CX01 • CX12 • CX01 • CX01 ≈ CX02 • CX12 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0192.proved) Eq.refl Eq.refl

  p1 : CX01 • CX12 • CX01 • CX01 ≈ CX01 • CX12
  p1 = by-assoc-and (under (CX01 • CX12) (ε) KB0013.proved) Eq.refl Eq.refl

  p2 : CX02 • CX12 • CX01 ≈ CX01 • CX12
  p2 = trans (sym p0) p1

  p3 : CX02 • CX12 • CX01 ≈ CX02 • CX12 • CX01
  p3 = refl

  p4 : CX01 • CX12 ≈ CX01 • CX12
  p4 = refl

  p5 : CX02 • CX12 • CX01 ≈ CX01 • CX12
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX02 • CX12 • CX01 ≈ CX01 • CX12
  proved = p5

module KB0018 where

  p0 : X0 • X2 ≈ X2 • X0
  p0 = bifunct_X_b.proved

  p1 : X0 • X2 ≈ X0 • X2
  p1 = refl

  p2 : X2 • X0 ≈ X2 • X0
  p2 = refl

  p3 : X0 • X2 ≈ X2 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : X2 • X0 ≈ X0 • X2
  p4 = sym p3

  proved : X2 • X0 ≈ X0 • X2
  proved = p4

module KB0221 where

  p0 : CX01 • X2 • X0 ≈ X2 • CX01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0022.proved) Eq.refl Eq.refl

  p1 : CX01 • X2 • X0 ≈ CX01 • X0 • X2
  p1 = by-assoc-and (under (CX01) (ε) KB0018.proved) Eq.refl Eq.refl

  p2 : X2 • CX01 • X0 ≈ CX01 • X0 • X2
  p2 = trans (sym p0) p1

  p3 : X2 • CX01 • X0 ≈ X2 • CX01 • X0
  p3 = refl

  p4 : CX01 • X0 • X2 ≈ CX01 • X0 • X2
  p4 = refl

  p5 : X2 • CX01 • X0 ≈ CX01 • X0 • X2
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • X0 • X2 ≈ X2 • CX01 • X0
  p6 = sym p5

  proved : CX01 • X0 • X2 ≈ X2 • CX01 • X0
  proved = p6

module KB0042 where

  p0 : CX01 • CX10 ≈ CX10 • SWAP01
  p0 = drel161.proved

  p1 : CX01 • CX10 ≈ CX01 • CX10
  p1 = refl

  p2 : CX10 • SWAP01 ≈ CX10 • SWAP01
  p2 = refl

  p3 : CX01 • CX10 ≈ CX10 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX10 • SWAP01 ≈ CX01 • CX10
  p4 = sym p3

  proved : CX10 • SWAP01 ≈ CX01 • CX10
  proved = p4

module KB0062 where

  p0 : CX01 ≈ SWAP01 • CX10 • SWAP01
  p0 = symmetry_CX_e.proved

  p1 : CX01 ≈ CX01
  p1 = refl

  p2 : SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CX01 • CX10
  p2 = by-assoc-and (under (SWAP01) (ε) KB0042.proved) Eq.refl Eq.refl

  p3 : SWAP01 • CX10 • SWAP01 ≈ SWAP01 • CX01 • CX10
  p3 = trans p2 (refl)

  p4 : CX01 ≈ SWAP01 • CX01 • CX10
  p4 = trans (sym p1) (trans p0 p3)

  p5 : SWAP01 • CX01 • CX10 ≈ CX01
  p5 = sym p4

  proved : SWAP01 • CX01 • CX10 ≈ CX01
  proved = p5

module KB0063 where

  p0 : SWAP01 • SWAP01 • CX01 • CX10 ≈ SWAP01 • CX01
  p0 = by-assoc-and (under (SWAP01) (ε) KB0062.proved) Eq.refl Eq.refl

  p1 : SWAP01 • SWAP01 • CX01 • CX10 ≈ CX01 • CX10
  p1 = by-assoc-and (under (ε) (CX01 • CX10) KB0000.proved) Eq.refl Eq.refl

  p2 : SWAP01 • CX01 ≈ CX01 • CX10
  p2 = trans (sym p0) p1

  p3 : SWAP01 • CX01 ≈ SWAP01 • CX01
  p3 = refl

  p4 : CX01 • CX10 ≈ CX01 • CX10
  p4 = refl

  p5 : SWAP01 • CX01 ≈ CX01 • CX10
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • CX01 ≈ CX01 • CX10
  proved = p5

module KB0032 where

  p0 : CCX12 • CX10 ≈ CX10 • CCX12
  p0 = drel56.proved

  p1 : CCX12 • CX10 ≈ CCX12 • CX10
  p1 = refl

  p2 : CX10 • CCX12 ≈ CX10 • CCX12
  p2 = refl

  p3 : CCX12 • CX10 ≈ CX10 • CCX12
  p3 = trans (sym p1) (trans p0 p2)

  proved : CCX12 • CX10 ≈ CX10 • CCX12
  proved = p3

module KB0228 where

  p0 : CCX12 • CX10 • SWAP01 ≈ CCX12 • CX01 • CX10
  p0 = by-assoc-and (under (CCX12) (ε) KB0042.proved) Eq.refl Eq.refl

  p1 : CCX12 • CX10 • SWAP01 ≈ CX10 • CCX12 • SWAP01
  p1 = by-assoc-and (under (ε) (SWAP01) KB0032.proved) Eq.refl Eq.refl

  p2 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CCX12 • CX01 • CX10 ≈ CCX12 • CX01 • CX10
  p3 = refl

  p4 : CX10 • CCX12 • SWAP01 ≈ CX10 • CCX12 • SWAP01
  p4 = refl

  p5 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
  proved = p5

module KB0264 where

  p0 : SWAP01 • CCX02 • CX01 ≈ CCX12 • SWAP01 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0090.proved) Eq.refl Eq.refl

  p1 : SWAP01 • CCX02 • CX01 ≈ SWAP01 • CX01 • CCX02
  p1 = by-assoc-and (under (SWAP01) (ε) KB0038.proved) Eq.refl Eq.refl

  p2 : CCX12 • SWAP01 • CX01 ≈ SWAP01 • CX01 • CCX02
  p2 = trans (sym p0) p1

  p3 : CCX12 • SWAP01 • CX01 ≈ CCX12 • CX01 • CX10
  p3 = by-assoc-and (under (CCX12) (ε) KB0063.proved) Eq.refl Eq.refl

  p4 : CCX12 • CX01 • CX10 ≈ CX10 • CCX12 • SWAP01
  p4 = by-assoc-and (under (ε) (ε) KB0228.proved) Eq.refl Eq.refl

  p5 : CCX12 • SWAP01 • CX01 ≈ CX10 • CCX12 • SWAP01
  p5 = trans p3 (trans p4 (refl))

  p6 : SWAP01 • CX01 • CCX02 ≈ CX01 • CX10 • CCX02
  p6 = by-assoc-and (under (ε) (CCX02) KB0063.proved) Eq.refl Eq.refl

  p7 : SWAP01 • CX01 • CCX02 ≈ CX01 • CX10 • CCX02
  p7 = trans p6 (refl)

  p8 : CX10 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX02
  p8 = trans (sym p5) (trans p2 p7)

  proved : CX10 • CCX12 • SWAP01 ≈ CX01 • CX10 • CCX02
  proved = p8

module KB0005 where

  p0 : CX10 • CX10 ≈ ε
  p0 = elim_CX10.proved

  p1 : CX10 • CX10 ≈ CX10 • CX10
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX10 • CX10 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX10 • CX10 ≈ ε
  proved = p3

module KB0141 where

  p0 : CX12 • CCX12 ≈ CCX12 • CX10 • CX12
  p0 = by-assoc-and (axiom r044) Eq.refl Eq.refl

  p1 : CX12 • CCX12 ≈ CX12 • CCX12
  p1 = refl

  p2 : CCX12 • CX10 • CX12 ≈ CX10 • CCX12 • CX12
  p2 = by-assoc-and (under (ε) (CX12) KB0032.proved) Eq.refl Eq.refl

  p3 : CCX12 • CX10 • CX12 ≈ CX10 • CCX12 • CX12
  p3 = trans p2 (refl)

  p4 : CX12 • CCX12 ≈ CX10 • CCX12 • CX12
  p4 = trans (sym p1) (trans p0 p3)

  p5 : CX10 • CCX12 • CX12 ≈ CX12 • CCX12
  p5 = sym p4

  proved : CX10 • CCX12 • CX12 ≈ CX12 • CCX12
  proved = p5
