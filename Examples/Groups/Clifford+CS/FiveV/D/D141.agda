{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D141 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0155 ; wl0204 ; wl0230 ; wl0289 ; wl0311 ; wl0341 ; wl0415 ; wl0532 ; wl0533 ; wl0929 ; wl1131 ; wl1251 ; wl1500 ; wl1501 ; wl1502 ; wl1538 ; wl1546 ; wl1549 ; wl1588 ; wl1709 ; wl1710 ; wl1711 ; wl1712 ; wp0021 ; wp0032 ; wp0039 ; wp0090 ; wp0109 ; wp0142 ; wp0279 ; wp0765 ; wp1328 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1370 ; wp1375 ; wp1376 ; wp1398 ; wp1412 ; wp1466 ; wp1467 ; wp1468 ; wp1469)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D133 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-perm-1324-at04122041)
open import Examples.Groups.Clifford+CS.FiveV.D.D135 using (lem-box-perm-4132-at04122041 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.FiveV.D.D139 using (lem-L-CCZ-1-at0440-part0)
open import Examples.Groups.Clifford+CS.FiveV.D.D140 using (lem-L-CCZ-1-at0440-part1)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CZ12-TOFF403)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CSd02 ; lem-comm-TOFF413-CX20)
-- L-CCZ-1 @0440 part2: 500 steps
lem-L-CCZ-1-at0440-part2 : Ws → ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b0 = at 20 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 22 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 22 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 22 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 26 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 25 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 26 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 27 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b1 = at 28 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 29 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 25 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 24 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 24 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 23 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 24 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 25 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b2 = at 26 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 27 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 23 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 22 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 23 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 23 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 27 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 26 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸ done

  b3 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b3 = at 27 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 28 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 29 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 30 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 31 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 32 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 26 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 25 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸ done

  b4 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ Toff413 ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b4 = at 25 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 24 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 25 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 26 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 27 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 28 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 29 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 30 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸ done

  b5 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ Toff413 ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b5 = at 24 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 25 2 (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1468 c4)) ▸
       at 23 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 25 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 27 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 26 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 27 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 28 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸ done

  b6 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b6 = at 29 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 30 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 26 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 23 3 (Toff203 ∷ []) (wp1469 c4) ▸
       at 25 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 25 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 28 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 28 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸ done

  b7 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b7 = at 27 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 28 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 29 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 30 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 31 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 27 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 26 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 26 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸ done

  b8 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b8 = at 25 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 26 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 27 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 28 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 29 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 25 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 26 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 26 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸ done

  b9 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b9 = at 26 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 30 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 29 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 30 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 31 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 32 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 33 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 34 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b10 = at 35 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 29 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 28 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 28 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 27 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 28 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 29 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 30 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b11 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b11 = at 31 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 32 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 33 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 27 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 28 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 26 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 28 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 30 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b12 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b12 = at 29 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 30 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 31 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 32 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 33 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 29 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 26 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 28 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b13 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b13 = at 28 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 28 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 32 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 31 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 32 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 33 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 34 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 35 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b14 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b14 = at 31 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 30 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 30 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 29 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 30 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 31 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 32 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 33 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b15 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b15 = at 29 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 28 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 29 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 29 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 33 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 32 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 33 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 34 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b16 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b16 = at 35 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 36 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 32 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 31 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 31 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 30 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 31 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 32 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b17 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b17 = at 33 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 34 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 30 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 29 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 30 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 30 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 30 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 34 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b18 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b18 = at 33 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 34 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 35 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 36 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 37 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 38 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 39 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 33 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b19 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b19 = at 32 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 32 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 31 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 32 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 33 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 34 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 35 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 36 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b20 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b20 = at 37 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 31 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 32 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 30 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 32 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 34 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 33 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 34 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b21 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b21 = at 35 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 36 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 37 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 33 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 30 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 32 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 32 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 32 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b22 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b22 = at 36 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 35 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 37 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 39 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 35 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 34 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b23 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b23 = at 34 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 33 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 34 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 35 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 37 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 33 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 32 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b24 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b24 = at 33 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 33 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 36 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸
       at 35 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 34 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸
       at 33 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 34 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 34 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b25 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b25 = at 38 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 37 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 39 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 40 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 41 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 37 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 36 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b26 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b26 = at 36 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 35 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 36 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 37 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 38 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 39 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 35 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 34 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b27 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b27 = at 35 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 35 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 35 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 39 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 38 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 39 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 40 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 41 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b28 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b28 = at 42 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 43 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 44 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 38 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 37 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 37 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 36 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 37 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸ done

  b29 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ024 ∷ CCZ012 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b29 = at 38 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 39 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 40 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 41 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 42 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 36 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 37 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 35 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸ done

  b30 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ024 ∷ CCZ012 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b30 = at 37 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 39 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 38 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 39 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 40 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 41 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 42 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 38 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b31 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b31 = at 35 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 37 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 37 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 37 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 41 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 40 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 41 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 42 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b32 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b32 = at 43 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 44 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 40 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 39 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 39 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 38 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 39 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 40 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b33 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b33 = at 41 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 42 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 38 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 37 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 38 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 38 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 41 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 40 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸ done

  b34 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b34 = at 39 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 38 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 39 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 39 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 43 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 42 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 43 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 44 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b35 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b35 = at 45 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 46 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 42 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 41 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 41 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 40 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 41 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 42 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b36 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b36 = at 43 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 44 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 40 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 39 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 40 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 40 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 40 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 44 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b37 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b37 = at 43 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 44 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 45 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 46 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 47 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 48 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 49 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 43 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b38 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b38 = at 42 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 42 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 41 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 42 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 43 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 44 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 45 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 46 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b39 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b39 = at 47 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 41 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 42 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 40 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 42 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 44 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 43 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 44 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸ done

  b40 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CS02 ∷ CX10 ∷ CCZ234 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b40 = at 45 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 46 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 47 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 43 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 40 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 42 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 42 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 42 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b41 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b41 = at 46 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 45 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 46 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 47 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 48 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 49 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 45 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 44 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b42 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b42 = at 44 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 43 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 44 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 45 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 46 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 47 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 43 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 42 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸ done

  b43 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b43 = at 43 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 43 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 46 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 46 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 45 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 46 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 47 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 48 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b44 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b44 = at 49 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 45 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 44 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 44 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 43 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 44 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 45 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 46 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b45 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b45 = at 47 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 43 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 44 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 44 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 48 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 47 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 48 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 49 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b46 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CS03 ∷ CX20 ∷ Toff413 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b46 = at 50 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 51 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 52 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 53 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 47 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 46 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 46 1 (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl1710 (lit c4))) ▸
       at 45 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸ done

  b47 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ K2 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ CCZ034 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b47 = at 46 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 47 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 48 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 49 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 50 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 51 2 (K2⁻ ∷ Toff413 ∷ []) (sym (wl1709 (lit c4))) ▸
       at 45 7 (Toff203 ∷ []) (wl1710 (lit c4)) ▸
       at 46 2 (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (sym (wp1468 c4)) ▸ done

  b48 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ CCZ024 ∷ Toff203 ∷ CCZ034 ∷ CCZ013 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b48 = at 44 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 46 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 48 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 47 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 48 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 49 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 50 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 51 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b49 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ034 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b49 = at 47 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 44 3 (Toff203 ∷ []) (wp1469 c4) ▸
       at 46 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 46 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 49 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 49 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 48 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 49 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b50 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  b50 = at 50 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 51 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 52 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 48 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 47 2 (CCZ013 ∷ Toff413 ∷ []) (sym (wp1412 c4)) ▸
       at 47 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 46 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 47 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b51 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ [])
  b51 = at 48 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 49 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 50 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 46 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 47 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 47 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 51 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 50 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b52 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ [])
  b52 = at 51 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 52 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 53 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 54 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 50 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 49 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 49 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 48 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸ done

  b53 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ024 ∷ CS02 ∷ Toff413 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ Toff413 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ [])
  b53 = at 49 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 50 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 51 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 52 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 48 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 47 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 48 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 48 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸ done

  b54 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ [])
  b54 = at 48 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 52 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 51 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 52 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 53 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 54 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 55 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 56 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b55 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ [])
  b55 = at 57 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 51 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 50 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 50 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 49 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 50 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 51 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 52 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸ done

  b56 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ [])
  b56 = at 53 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 54 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 55 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 49 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 50 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 48 2 (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4) ▸
       at 50 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 52 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸ done

  b57 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ234 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ012 ∷ [])
  b57 = at 51 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 52 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 53 2 (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4) ▸
       at 54 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 55 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 51 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 48 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 50 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b58 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ Bx4-2301 ∷ CCZ012 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ [])
  b58 = at 50 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 50 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 54 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 53 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 54 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 55 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 56 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 57 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b59 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ [])
  b59 = at 53 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 52 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 52 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 51 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 52 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 53 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 54 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 55 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b60 : Chain (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ [])
  b60 = at 51 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 50 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 51 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 0 3 (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4)) ▸
       at 2 2 [] (wl0204 (lit c4)) ▸
       at 5 11 (CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ []) (wl1711 (lit c4)) ▸
       at 15 2 [] (wl0230 (lit c4)) ▸
       at 5 2 [] (wl0204 (lit c4)) ▸ done

  b61 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ [])
  b61 = at 5 3 (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4)) ▸
       at 7 2 [] (wl0204 (lit c4)) ▸
       at 13 2 [] (wl0341 (lit c4)) ▸
       at 14 2 [] (wl0230 (lit c4)) ▸
       at 15 2 [] (wl0341 (lit c4)) ▸
       at 15 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 16 2 [] (wl0341 (lit c4)) ▸
       at 16 2 (CS13 ∷ CCZ012 ∷ []) (wl0311 (lit c4)) ▸ done

  b62 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ [])
  b62 = at 17 2 [] (wl0341 (lit c4)) ▸
       at 18 2 [] (wl0341 (lit c4)) ▸
       at 19 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 20 2 [] (wl0341 (lit c4)) ▸ done


-- L-CCZ-1 @0440 part3: 6 steps
lem-L-CCZ-1-at0440-part3 : Ws → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part3 c4 = run b0
  where
  b0 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 21 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 22 2 [] (wl0230 (lit c4)) ▸
       at 23 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 24 2 [] (wl0341 (lit c4)) ▸
       at 0 25 [] (wl1712 (lit c4)) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-box-perm-4132-at04122041 c4) ▸ done


-- L-CCZ-1 @0440: 4 steps
lem-L-CCZ-1-at0440 : Ws → ⟪ (Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440 c4 = run b0
  where
  b0 : Chain (Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 45 (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (lem-L-CCZ-1-at0440-part0 c4) ▸
       at 0 46 (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (lem-L-CCZ-1-at0440-part1 c4) ▸
       at 0 50 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) (lem-L-CCZ-1-at0440-part2 c4) ▸
       at 0 30 (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440-part3 c4) ▸ done


-- t-cP @0440: 5 steps
lem-t-cP-at0440 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-t-cP-at0440 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (sym (wl0532 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸
       at 2 3 (CCZ124 ∷ Toff412 ∷ []) (sym (wl0533 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸ done

