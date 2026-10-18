{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D140 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0289 ; wl0415 ; wl0929 ; wl1270 ; wl1500 ; wl1501 ; wl1538 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1588 ; wl1695 ; wl1709 ; wl1710 ; wp0021 ; wp0032 ; wp0038 ; wp0039 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0109 ; wp0142 ; wp0279 ; wp0669 ; wp0765 ; wp1288 ; wp1328 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1370 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1379 ; wp1381 ; wp1398 ; wp1412 ; wp1464 ; wp1465 ; wp1466 ; wp1467 ; wp1468 ; wp1469)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-perm-1324-at04122041 ; lem-box-perm-4213-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-box2-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ024-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CSd02 ; lem-comm-TOFF413-CX20)
-- L-CCZ-1 @0440 part1: 500 steps
lem-L-CCZ-1-at0440-part1 : Ws → ⟪ (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b0 = at 33 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 27 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 28 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 26 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 28 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 30 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 29 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 30 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b1 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b1 = at 31 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 32 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 33 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 26 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 28 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 28 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 28 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b2 = at 31 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 30 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 29 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 28 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 29 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 29 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 33 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 32 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b3 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b3 = at 33 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 34 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 35 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 36 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 32 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 31 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 31 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 30 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b4 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b4 = at 31 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 32 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 33 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 34 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 30 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 29 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 30 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 30 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸ done

  b5 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b5 = at 30 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 34 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 33 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 34 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 35 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 36 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 37 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 38 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b6 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b6 = at 39 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 33 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 32 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 32 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 31 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 32 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 33 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 34 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b7 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b7 = at 35 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 36 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 37 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 31 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 32 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 30 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 32 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 34 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b8 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b8 = at 33 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 34 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 35 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 36 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 37 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 33 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 30 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 32 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b9 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b9 = at 32 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 32 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 35 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 35 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 34 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 35 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 36 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 37 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b10 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b10 = at 38 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 34 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 33 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 33 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 32 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 33 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 34 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 35 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b11 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b11 = at 36 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 32 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 33 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 33 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 37 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 36 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 37 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 38 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b12 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b12 = at 39 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 40 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 41 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 42 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 36 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 35 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 35 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 34 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸ done

  b13 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b13 = at 35 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 36 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 37 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 38 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 39 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 40 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 34 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 35 2 (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1468 c4)) ▸ done

  b14 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b14 = at 33 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 35 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 37 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 36 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 37 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 38 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 39 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 40 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b15 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b15 = at 36 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 33 3 (Toff203 ∷ []) (wp1469 c4) ▸
       at 35 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 35 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 39 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 38 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 39 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 40 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Bx4-1023 ∷ [])
  b16 = at 41 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 42 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 38 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 37 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 37 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 36 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 37 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 38 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Bx4-1023 ∷ [])
  b17 = at 39 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 40 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 36 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 35 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 36 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 36 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 36 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 40 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b18 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ Bx4-1023 ∷ [])
  b18 = at 39 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 40 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 41 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 42 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 43 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 44 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 45 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 39 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b19 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Bx4-1023 ∷ [])
  b19 = at 38 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 38 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 37 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 38 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 39 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 40 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 41 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 42 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b20 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Bx4-1023 ∷ [])
  b20 = at 43 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 37 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 38 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 36 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 38 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 40 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 39 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 40 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b21 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Bx4-1023 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-1023 ∷ Bx4-1023 ∷ [])
  b21 = at 41 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 42 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 43 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 39 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 36 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 38 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 38 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 38 1 (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4) ▸ done

  b22 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-1023 ∷ Bx4-1023 ∷ []) (CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b22 = at 38 2 [] (lem-box2-at04203243 c4) ▸
       at 0 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 2 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b23 : Chain (CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ024 ∷ Toff403 ∷ CS03 ∷ Toff413 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b23 = at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 1 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 3 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 2 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸ done

  b24 : Chain (CCZ024 ∷ Toff403 ∷ CS03 ∷ Toff413 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b24 = at 3 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 5 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 2 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 0 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸ done

  b25 : Chain (CCZ023 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b25 = at 2 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b26 : Chain (CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ Bx4-2031 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b26 = at 1 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

  b27 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ Bx4-2031 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b27 = at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 6 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 5 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 8 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b28 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b28 = at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 6 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 5 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 6 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b29 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b29 = at 7 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 8 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 6 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 4 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 3 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b30 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b30 = at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b31 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b31 = at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b32 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b32 = at 10 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 9 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 10 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 12 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 14 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 15 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸ done

  b33 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff413 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b33 = at 9 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 8 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 8 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 7 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 8 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 10 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b34 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff413 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b34 = at 12 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 13 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 7 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1464 c4)) ▸
       at 6 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 8 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 10 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 9 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b35 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b35 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 6 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 8 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 8 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b36 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b36 = at 12 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 11 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 12 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 13 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 14 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 15 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 11 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 10 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸ done

  b37 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b37 = at 10 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 9 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 10 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 11 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 12 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 13 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸ done

  b38 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b38 = at 9 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 9 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 13 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 12 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 13 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 15 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸ done

  b39 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b39 = at 12 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 11 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 11 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 10 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 11 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 13 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 14 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸ done

  b40 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b40 = at 10 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 9 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 10 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 10 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 13 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 12 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 15 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 14 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b41 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b41 = at 15 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 18 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 19 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 20 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 14 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 11 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸ done

  b42 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b42 = at 13 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 12 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 13 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 15 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 16 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 12 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 13 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸ done

  b43 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b43 = at 11 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 10 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 12 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b44 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b44 = at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 12 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 12 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 15 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 14 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸ done

  b45 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b45 = at 12 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 13 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 17 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 16 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 17 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 18 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 19 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b46 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b46 = at 20 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 16 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 15 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 15 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 14 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 15 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 16 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 17 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b47 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b47 = at 18 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 14 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 13 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 14 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 14 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 17 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 16 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 19 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b48 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b48 = at 18 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 19 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 21 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 24 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 18 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b49 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b49 = at 15 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 17 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 16 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 17 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 18 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 19 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 20 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 16 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done

  b50 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b50 = at 17 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 15 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 14 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 16 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 15 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 16 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 17 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 18 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b51 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b51 = at 19 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 20 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 21 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 15 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 16 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 19 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 18 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b52 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b52 = at 17 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 16 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 17 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 17 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 21 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 20 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 21 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 22 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b53 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b53 = at 23 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 24 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 25 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 26 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 20 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 19 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 19 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 18 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸ done

  b54 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b54 = at 19 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 20 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 21 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 22 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 23 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 24 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 18 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 19 2 (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1464 c4)) ▸ done

  b55 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b55 = at 17 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 19 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 21 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 20 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 21 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 22 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 23 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 24 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b56 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b56 = at 20 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 17 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 19 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 19 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 22 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 22 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 21 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b57 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b57 = at 23 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 24 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 25 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 21 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 20 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 20 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 19 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 20 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b58 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b58 = at 21 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 22 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 23 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 19 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 20 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 20 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 20 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 24 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b59 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b59 = at 23 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 24 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 25 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 26 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 27 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 28 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 29 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 23 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b60 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b60 = at 22 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 22 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 21 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 22 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 23 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 24 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 25 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 26 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b61 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b61 = at 27 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 21 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 22 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 20 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 22 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 24 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 23 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 24 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b62 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b62 = at 25 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 26 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 27 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 23 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

