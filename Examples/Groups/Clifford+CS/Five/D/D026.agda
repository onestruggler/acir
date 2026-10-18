{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D026 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0220 ; wl0263 ; wl0341 ; wl0391 ; wl0392 ; wl0393 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1233 ; wl1249 ; wl1251 ; wp0167 ; wp0261 ; wp0272 ; wp0301 ; wp0743 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1041 ; wp1042 ; wp1111 ; wp1123 ; wp1124 ; wp1125)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F0-at01143043 ; lem-box-cP-at03243240 ; lem-box2-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-S2-SBOX⟨3·1·42·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-CKc-box-at0312203441 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-box-perm-3421-at03243240 ; lem-box-perm-4312-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-nf-rel-268at0)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ134-CX02 ; lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)
-- F1-rel-268@0: 484 steps
lem-F1-rel-268at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (run b60))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 3 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 8 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 10 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 11 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸ done

  b1 : Chain (Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 2 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 8 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 10 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 12 1 (CS01 ∷ []) (refl) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b2 = at 14 1 (CS01⁻ ∷ []) (refl) ▸
       at 10 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 13 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 13 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 12 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 13 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ Toff302 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b3 = at 16 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 17 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 18 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 12 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 13 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 13 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 15 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ Toff302 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b4 = at 14 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 15 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 17 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 18 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 14 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 11 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ134 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b5 = at 10 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 11 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 16 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 10 7 (Toff024 ∷ []) (wp1026 c4) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ134 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b6 = at 11 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 12 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 12 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 15 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 14 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 13 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 12 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 13 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b7 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b7 = at 13 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 16 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 16 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 15 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 16 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 17 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 18 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 19 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b8 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b8 = at 20 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 21 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 15 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 16 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 14 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 16 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 18 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 17 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b9 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b9 = at 18 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 19 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 20 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 21 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 17 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 14 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 14 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 13 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b10 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b10 = at 14 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 15 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 17 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 18 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 19 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 13 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸ done

  b11 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-2041 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ [])
  b11 = at 15 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 15 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 18 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 17 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 16 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 15 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 16 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 16 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸ done

  b12 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-2041 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CK41 ∷ S4 ∷ [])
  b12 = at 16 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 19 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 19 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 23 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 22 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 23 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 24 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 25 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b13 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ [])
  b13 = at 26 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 22 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 21 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 21 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 20 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 21 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 22 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 23 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b14 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ [])
  b14 = at 24 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 20 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 19 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 20 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 20 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸
       at 20 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 23 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 23 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b15 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b15 = at 26 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 25 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 24 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 23 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 24 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 0 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸ done

  b16 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b16 = at 2 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 4 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 6 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 7 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 8 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 2 7 (Toff024 ∷ []) (wp1026 c4) ▸ done

  b17 : Chain (CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff302 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b17 = at 3 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 3 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 5 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 7 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b18 : Chain (CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff302 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b18 = at 8 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 1 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 1 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 0 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 1 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 2 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 3 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸ done

  b19 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b19 = at 4 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 5 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 6 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 0 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 2 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 5 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸ done

  b20 : Chain (Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b20 = at 4 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 3 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 2 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 3 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 6 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 5 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b21 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b21 = at 6 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 11 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸ done

  b22 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b22 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 6 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 8 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 10 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 11 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸ done

  b23 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b23 = at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 4 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 3 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 4 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b24 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b24 = at 8 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 9 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 5 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 8 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 7 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸ done

  b25 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b25 = at 6 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 5 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 6 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 6 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸
       at 6 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 9 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 9 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 13 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸ done

  b26 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b26 = at 12 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 13 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 14 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 15 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 16 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 12 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 11 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 11 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸ done

  b27 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ Bx3-1420 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b27 = at 10 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 11 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 12 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 13 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 14 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 10 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 9 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 10 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b28 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ Bx3-1420 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b28 = at 10 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸
       at 10 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 13 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 13 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 16 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 15 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 14 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 13 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸ done

  b29 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b29 = at 14 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 14 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 18 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 17 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 18 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 19 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 20 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 21 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸ done

  b30 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b30 = at 17 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 16 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 16 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 15 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 16 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 17 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 18 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 19 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸ done

  b31 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b31 = at 15 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 15 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 15 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 18 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 18 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 17 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 18 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸ done

  b32 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b32 = at 19 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 20 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 21 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 22 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 23 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 17 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 18 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 16 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸ done

  b33 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b33 = at 18 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 20 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 19 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 20 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 22 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 23 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 19 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b34 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b34 = at 16 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 16 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 15 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 16 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 17 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 18 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 19 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 20 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸ done

  b35 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b35 = at 21 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 15 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 16 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 17 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 17 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 21 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 20 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 21 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b36 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b36 = at 22 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 23 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 24 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 20 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 19 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 19 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 18 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 19 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b37 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b37 = at 20 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 21 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 22 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 18 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 17 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 18 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 18 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 21 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸ done

  b38 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b38 = at 20 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 19 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 18 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 19 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 19 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 22 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 22 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 21 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b39 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b39 = at 22 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 23 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 24 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 25 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 26 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 27 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 21 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸ done

  b40 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b40 = at 20 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 22 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 24 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 23 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 24 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 25 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 26 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 27 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸ done

  b41 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b41 = at 23 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 20 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 20 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 19 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 20 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 21 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 22 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 23 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b42 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b42 = at 24 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 25 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 19 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 20 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 21 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 21 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 25 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 24 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b43 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b43 = at 25 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 26 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 27 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 28 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 24 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 23 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 23 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 22 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b44 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b44 = at 23 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 24 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 25 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 26 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 22 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 21 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 22 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 22 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b45 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b45 = at 25 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 24 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 23 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 22 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 23 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 23 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 26 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 26 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸ done

  b46 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b46 = at 25 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 26 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 27 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 28 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 29 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 25 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 24 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 24 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸ done

  b47 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ Bx3-2041 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b47 = at 23 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 24 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 25 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 26 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 27 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 23 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 24 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 24 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸ done

  b48 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ Bx3-2041 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b48 = at 24 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 27 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 27 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 30 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 30 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 29 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 30 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 31 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸ done

  b49 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b49 = at 32 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 33 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 28 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 28 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 27 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 28 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 29 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸ done

  b50 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b50 = at 30 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 31 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 27 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 28 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 28 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 32 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 31 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 32 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b51 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b51 = at 33 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 34 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 35 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 31 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 30 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 30 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 29 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 30 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b52 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b52 = at 31 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 32 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 33 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 29 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 28 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 29 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 29 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 32 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸ done

  b53 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b53 = at 32 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 31 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 32 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 33 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 34 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 35 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 31 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 30 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸ done

  b54 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ Bx3-1420 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b54 = at 30 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 29 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 30 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 31 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 32 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 33 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 30 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b55 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ Bx3-1420 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ CCZ134 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ S4 ∷ Bx3-1420 ∷ [])
  b55 = at 30 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸
       at 30 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 33 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 33 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 36 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 36 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 35 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 36 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b56 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ CCZ134 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CCZ134 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ Bx3-1420 ∷ [])
  b56 = at 37 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 38 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 39 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 35 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 34 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 34 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 33 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 34 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b57 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CCZ134 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ Bx3-1420 ∷ [])
  b57 = at 35 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 36 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 37 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 33 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 34 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 34 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 37 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 36 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸ done

  b58 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ Bx3-1420 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  b58 = at 35 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 34 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 35 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 35 2 [] (lem-box2-at03243240 c4) ▸
       at 1 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 4 26 (CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) (wp1123 c4) ▸
       at 29 2 [] (wl0341 (lit c4)) ▸ done

  b59 : Chain (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
  b59 = at 5 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 6 2 [] (wl0341 (lit c4)) ▸
       at 7 11 (S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ []) (wp1124 c4) ▸
       at 17 2 [] (wl0341 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 9 2 [] (wl0263 (lit c4)) ▸
       at 9 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 11 2 [] (wl0263 (lit c4)) ▸ done

  b60 : Chain (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b60 = at 15 2 [] (wl0341 (lit c4)) ▸
       at 16 2 [] (wl0341 (lit c4)) ▸
       at 0 19 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (wp1125 c4) ▸
       at 0 19 (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (sym (lem-nf-rel-268at0 c4)) ▸ done

