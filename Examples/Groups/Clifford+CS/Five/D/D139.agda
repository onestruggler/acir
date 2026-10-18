{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D139 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0289 ; wl0415 ; wl0461 ; wl0477 ; wl0929 ; wl1270 ; wl1501 ; wl1502 ; wl1509 ; wl1517 ; wl1538 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1588 ; wl1695 ; wl1708 ; wl1709 ; wl1710 ; wp0021 ; wp0032 ; wp0038 ; wp0039 ; wp0053 ; wp0060 ; wp0061 ; wp0065 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0109 ; wp0142 ; wp0155 ; wp0156 ; wp0157 ; wp0167 ; wp0279 ; wp0311 ; wp0394 ; wp0669 ; wp0765 ; wp1210 ; wp1211 ; wp1288 ; wp1318 ; wp1328 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1347 ; wp1348 ; wp1355 ; wp1356 ; wp1357 ; wp1358 ; wp1370 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1379 ; wp1381 ; wp1398 ; wp1460 ; wp1461 ; wp1462 ; wp1463 ; wp1464 ; wp1465 ; wp1466 ; wp1467 ; wp1468 ; wp1469)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-perm-1324-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-L-CX01-1-at0440 ; lem-L-CX01-2-at0440 ; lem-L-CX10-2-at0440 ; lem-S2-SBOX⟨0·2·43·1⟩-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CSd02 ; lem-comm-TOFF413-CX20)
-- L-CCZ-1 @0440 part0: 500 steps
lem-L-CCZ-1-at0440-part0 : Ws → ⟪ (Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Sb4-2-03-1 ∷ Toff201 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Sb4-1-02-3 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b0 = at 1 5 (Toff201 ∷ []) (lem-L-CX01-1-at0440 c4) ▸
       at 5 5 (Toff201 ∷ []) (lem-L-CX01-1-at0440 c4) ▸
       at 6 5 (Toff302 ∷ []) (lem-L-CX01-2-at0440 c4) ▸
       at 7 5 (Toff203 ∷ []) (lem-L-CX10-2-at0440 c4) ▸
       at 8 5 (Toff302 ∷ []) (lem-L-CX01-2-at0440 c4) ▸
       at 10 5 (Toff302 ∷ []) (lem-L-CX01-2-at0440 c4) ▸
       at 11 5 (Toff203 ∷ []) (lem-L-CX10-2-at0440 c4) ▸
       at 12 5 (Toff302 ∷ []) (lem-L-CX01-2-at0440 c4) ▸ done

  b1 : Chain (Sb4-2-03-1 ∷ Toff201 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Sb4-1-02-3 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b1 = at 2 2 (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4) ▸
       at 0 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 11 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b2 = at 18 1 (CS13 ∷ []) (refl) ▸
       at 20 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 19 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 18 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 21 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 20 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 21 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸ done

  b3 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b3 = at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 24 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 25 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 26 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 20 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 17 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 19 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b4 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b4 = at 18 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 19 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 20 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 21 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 22 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 18 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 19 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 17 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸ done

  b5 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ014 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b5 = at 16 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 18 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 17 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 18 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 19 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 20 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 21 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 22 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸ done

  b6 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b6 = at 23 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 17 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 18 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 18 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 21 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 20 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 19 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 18 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b7 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b7 = at 19 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 19 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 22 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 21 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 24 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 23 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 24 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 25 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b8 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff402 ∷ CS02 ∷ Toff423 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b8 = at 26 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 27 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 28 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 29 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 23 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 20 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 22 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 21 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸ done

  b9 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff402 ∷ CS02 ∷ Toff423 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b9 = at 22 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 23 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 24 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 25 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 21 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 22 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 20 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 19 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸ done

  b10 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b10 = at 21 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 20 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 21 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 24 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 25 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 26 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b11 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ [])
  b11 = at 20 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 21 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 21 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 24 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 23 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 22 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 21 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 22 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b12 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ [])
  b12 = at 22 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 25 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 24 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 27 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 26 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 27 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 28 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 29 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸ done

  b13 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ014 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ Toff423 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ [])
  b13 = at 30 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 31 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 32 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 26 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 23 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 25 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 24 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 25 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b14 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ014 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ Toff423 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ [])
  b14 = at 26 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 27 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 28 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 24 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 25 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 23 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 22 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 24 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b15 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ [])
  b15 = at 23 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 24 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 25 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 26 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 27 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 28 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 29 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 23 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff203 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff403 ∷ CCZ013 ∷ K2 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ Toff423 ∷ Toff302 ∷ [])
  b16 = at 24 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 24 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 27 2 (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) (sym (wp1460 c4)) ▸
       at 26 2 (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp1461 c4) ▸
       at 29 1 (K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1708 (lit c4))) ▸
       at 28 2 (K2 ∷ CCZ014 ∷ []) (wp1210 c4) ▸
       at 29 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 30 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff403 ∷ CCZ013 ∷ K2 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ Toff423 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff403 ∷ CS03 ∷ Toff423 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff203 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ [])
  b17 = at 31 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 32 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 33 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 34 2 (K2⁻ ∷ CCZ014 ∷ []) (wp1211 c4) ▸
       at 28 7 (Toff203 ∷ []) (wl1708 (lit c4)) ▸
       at 25 2 (Toff403 ∷ Toff423 ∷ []) (sym (wp1462 c4)) ▸
       at 27 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 26 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸ done

  b18 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff403 ∷ CS03 ∷ Toff423 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff203 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ CCZ014 ∷ Toff203 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ [])
  b18 = at 27 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 28 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 29 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 30 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 26 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸
       at 27 2 (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) (sym (wp1460 c4)) ▸
       at 25 3 (CCZ013 ∷ []) (sym (wp1463 c4)) ▸
       at 24 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸ done

  b19 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ CCZ014 ∷ Toff203 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ [])
  b19 = at 26 1 (K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1708 (lit c4))) ▸
       at 25 2 (K2 ∷ CCZ014 ∷ []) (wp1210 c4) ▸
       at 26 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 27 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 28 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 29 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 30 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 31 2 (K2⁻ ∷ CCZ014 ∷ []) (wp1211 c4) ▸ done

  b20 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ [])
  b20 = at 25 7 (Toff203 ∷ []) (wl1708 (lit c4)) ▸
       at 26 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 26 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 29 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 28 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 31 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 30 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 31 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸ done

  b21 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ [])
  b21 = at 32 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 33 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 34 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 35 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 36 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 30 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 27 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 29 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b22 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b22 = at 28 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 29 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 30 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 31 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 32 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 28 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 29 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 27 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸ done

  b23 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ014 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b23 = at 26 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 28 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 27 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 28 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 29 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 30 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 31 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 32 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸ done

  b24 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b24 = at 33 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 27 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 28 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 7 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 10 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 9 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 12 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b25 = at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 8 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b26 = at 10 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 9 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 10 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 11 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 12 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 13 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 10 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b27 = at 8 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 7 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 9 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 9 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b28 = at 13 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 9 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 9 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 12 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 11 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 10 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b29 = at 9 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 10 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 10 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 13 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 12 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 15 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 14 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 15 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b30 = at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 18 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 19 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 20 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 14 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 11 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 13 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸ done

  b31 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ CCZ023 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b31 = at 12 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 13 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 15 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 12 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 13 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 11 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸ done

  b32 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ CCZ023 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b32 = at 10 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 12 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b33 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b33 = at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 12 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 12 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 15 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 14 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 13 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 12 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b34 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff413 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b34 = at 13 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 13 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 17 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 16 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 17 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 18 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 19 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 20 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b35 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff413 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b35 = at 21 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 22 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 16 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 15 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 15 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 14 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 15 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 16 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b36 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b36 = at 17 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 18 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 19 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 20 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 14 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 15 2 (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1464 c4)) ▸
       at 13 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 15 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸ done

  b37 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b37 = at 17 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 16 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 19 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 20 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 16 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 13 3 (Toff201 ∷ []) (wp1465 c4) ▸ done

  b38 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b38 = at 15 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 15 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 15 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 19 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 18 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 19 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 20 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 21 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b39 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b39 = at 22 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 23 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 24 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 18 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 17 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 17 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 16 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 17 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸ done

  b40 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ024 ∷ CCZ012 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b40 = at 18 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 19 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 20 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 21 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 22 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 16 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 17 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 15 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸ done

  b41 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ024 ∷ CCZ012 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b41 = at 17 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 19 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 18 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 19 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 20 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 21 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 22 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 18 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b42 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff203 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b42 = at 15 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 17 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 17 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 17 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 21 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 20 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 21 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 22 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b43 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b43 = at 23 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 24 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 25 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 26 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 20 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 19 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 19 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 18 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸ done

  b44 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b44 = at 19 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 20 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 21 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 22 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 23 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 24 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 18 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 19 2 (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1468 c4)) ▸ done

  b45 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b45 = at 17 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 19 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 21 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 20 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 21 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 22 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 23 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 24 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b46 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b46 = at 20 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 17 3 (Toff203 ∷ []) (wp1469 c4) ▸
       at 19 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 19 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 19 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 23 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 22 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 23 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸ done

  b47 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b47 = at 24 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 25 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 26 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 27 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 28 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 22 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 21 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 21 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b48 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b48 = at 20 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 21 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 22 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 23 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 24 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 25 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 26 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 20 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b49 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CCZ234 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b49 = at 21 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 19 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 21 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 23 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 22 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 23 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 24 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 25 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b50 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CCZ234 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b50 = at 26 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 22 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 19 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 21 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 21 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 21 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 25 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 24 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b51 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b51 = at 25 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 26 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 27 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 28 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 24 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 23 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 23 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 22 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b52 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b52 = at 23 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 24 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 25 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 26 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 22 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 21 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 22 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 22 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸ done

  b53 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b53 = at 22 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 26 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 25 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 26 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 27 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 28 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 29 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 30 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b54 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b54 = at 31 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 25 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 24 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 24 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 23 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 24 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 25 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 26 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b55 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b55 = at 27 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 28 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 29 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 23 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 24 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 22 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 24 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 26 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b56 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b56 = at 25 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 26 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 27 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 28 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 29 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 25 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 22 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 24 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b57 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b57 = at 24 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 24 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 27 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸
       at 26 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 25 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸
       at 24 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 25 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 25 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b58 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b58 = at 29 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 28 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 29 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 30 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 31 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 32 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 28 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 27 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b59 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b59 = at 27 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 26 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 27 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 28 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 29 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 30 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 26 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 25 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b60 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b60 = at 26 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 26 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 26 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 30 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 29 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 30 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 31 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 32 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b61 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b61 = at 33 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 34 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 35 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 29 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 28 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 28 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 27 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 28 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸ done

  b62 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b62 = at 29 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 30 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 31 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 32 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

