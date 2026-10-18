{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D138 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0167 ; wl0204 ; wl0207 ; wl0228 ; wl0263 ; wl0270 ; wl0271 ; wl0278 ; wl0287 ; wl0305 ; wl0307 ; wl0318 ; wl0321 ; wl0334 ; wl0341 ; wl0453 ; wl0454 ; wl0455 ; wl0456 ; wl0457 ; wl0461 ; wl0465 ; wl0466 ; wl0470 ; wl0516 ; wl0618 ; wl0675 ; wl0679 ; wl0861 ; wl0871 ; wl0879 ; wl0929 ; wl1151 ; wl1152 ; wl1190 ; wl1226 ; wl1241 ; wl1251 ; wl1270 ; wl1358 ; wl1430 ; wl1431 ; wl1501 ; wl1509 ; wl1517 ; wl1519 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1549 ; wl1596 ; wl1609 ; wl1611 ; wl1661 ; wl1665 ; wl1666 ; wl1667 ; wl1669 ; wl1671 ; wl1673 ; wl1674 ; wl1675 ; wl1676 ; wl1677 ; wl1678 ; wl1679 ; wl1680 ; wl1681 ; wl1682 ; wl1683 ; wl1684 ; wl1685 ; wl1686 ; wl1687 ; wl1688 ; wl1689 ; wl1690 ; wl1691 ; wl1692 ; wl1693 ; wl1694 ; wl1695 ; wl1696 ; wl1697 ; wl1698 ; wl1699 ; wl1700 ; wl1701 ; wl1702 ; wl1703 ; wl1704 ; wl1705 ; wl1706 ; wl1707 ; wp0001 ; wp0002 ; wp0003 ; wp0021 ; wp0032 ; wp0039 ; wp0053 ; wp0054 ; wp0060 ; wp0061 ; wp0062 ; wp0064 ; wp0065 ; wp0066 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0103 ; wp0106 ; wp0108 ; wp0120 ; wp0121 ; wp0123 ; wp0124 ; wp0125 ; wp0127 ; wp0155 ; wp0156 ; wp0157 ; wp0161 ; wp0213 ; wp0261 ; wp0269 ; wp0303 ; wp0304 ; wp0306 ; wp0311 ; wp0317 ; wp0357 ; wp0374 ; wp0375 ; wp0496 ; wp0575 ; wp0722 ; wp0732 ; wp0733 ; wp1003 ; wp1005 ; wp1006 ; wp1134 ; wp1202 ; wp1278 ; wp1279 ; wp1318 ; wp1323 ; wp1335 ; wp1338 ; wp1339 ; wp1340 ; wp1354 ; wp1355 ; wp1356 ; wp1373 ; wp1374 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1399 ; wp1400 ; wp1436 ; wp1437 ; wp1438 ; wp1439 ; wp1440 ; wp1441 ; wp1442 ; wp1443 ; wp1444 ; wp1445 ; wp1446 ; wp1447 ; wp1448 ; wp1449 ; wp1450 ; wp1451 ; wp1452 ; wp1453 ; wp1454 ; wp1455 ; wp1456 ; wp1457 ; wp1458 ; wp1459)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at04203243 ; lem-box-cP-at043043 ; lem-box-tQ-at043043 ; lem-tP-at04203243 ; lem-tP-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at0314203142 ; lem-box-tQ-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-cP-at0214213043 ; lem-sym-bc-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-cP-at0314213240 ; lem-sym-ab-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at033440 ; lem-sym-bc-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-tQ-at04122041 ; lem-tP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-box-perm-1324-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-pairs-at0413203142 ; lem-pairs-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-CSdu-box-3-at0314203142 ; lem-CSu-box-3-at0314203142 ; lem-F0-at0410213243 ; lem-P-box-at0410233142 ; lem-VPQ-at0410233142 ; lem-box-perm-1342-at0314203142 ; lem-box-perm-1342-at04203243 ; lem-box-tQ-at0410233142 ; lem-box-tQ-at0412233140 ; lem-cQ-at0412233140 ; lem-sym-ab-at0413203142 ; lem-tP-at0410233142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS03-TOFF412 ; lem-comm-CS12-CCZ034 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-TOFF401 ; lem-comm-CX40-TOFF312 ; lem-comm-CZ03-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CK03-CCZ124 ; lem-comm-CX20-TOFF413 ; lem-comm-CX41-TOFF302 ; lem-comm-CZ02-TOFF413 ; lem-comm-SWAP13-BOX⟨4·20⟩ ; lem-comm-TOFF403-CX12)
-- QVQ @0410233142: 3 steps
lem-QVQ-at0410233142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0410233142 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0410233142: 12 steps
lem-box-cP-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0312 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0410233142 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233142 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done


-- pairs @0410233142: 4 steps
lem-pairs-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-pairs-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) (sym (lem-P-box-at0410233142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0410233142 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done


-- box-perm-1243 @0440: 3 steps
lem-box-perm-1243-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-1243-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-3012 ∷ []) (lem-pairs-at0440 c4) ▸
       at 0 1 (Bx4-0312 ∷ []) (lem-sym-ab-at0413203142 c4) ▸
       at 0 1 (Bx4-1203 ∷ []) (lem-pairs-at0410233142 c4) ▸ done


-- P-box @043043: 8 steps
lem-P-box-at043043 : Ws → ⟪ (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-P-box-at043043 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 0 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at043043 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (sym (wp1399 c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at043043 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ03 ∷ []) (sym (wp1400 c4)) ▸
       at 2 2 (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0375 c4)) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done


-- pairs @043043: 4 steps
lem-pairs-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-pairs-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 0 1 (Toff403 ∷ Bx4-1203 ∷ Toff403 ∷ []) (sym (lem-P-box-at043043 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 2 [] (wp0317 c4) ▸
       at 0 4 (Bx4-0312 ∷ []) (sym (lem-box-tQ-at0410233142 c4)) ▸ done


-- sym-ab @0410233142: 18 steps
lem-sym-ab-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-ab-at0410233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0312 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (wl1596 (lit c4)) ▸
       at 4 1 (Bx4-32 ∷ []) (refl) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ [])
  b1 = at 2 6 (Bx3-412 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (wl1596 (lit c4)) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸
       at 10 1 (Bx4-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (Bx4-3012 ∷ [])
  b2 = at 5 6 (Bx3-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- box-perm-1243 @043043: 3 steps
lem-box-perm-1243-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1243-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Bx4-0312 ∷ []) (lem-pairs-at043043 c4) ▸
       at 0 1 (Bx4-3012 ∷ []) (lem-sym-ab-at0410233142 c4) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-pairs-at0413203142 c4) ▸ done


-- box-box-3 @0440: 105 steps
lem-box-box-3-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-3-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx4-1230 ∷ Bx3-4120 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CCZ134 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ [])
  b0 = at 0 1 (Bx4-1203 ∷ []) (lem-box-perm-1243-at0440 c4) ▸
       at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 3 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 4 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 6 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 5 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 9 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CCZ134 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 6 3 (Toff302 ∷ CCZ034 ∷ []) (wp1134 c4) ▸
       at 3 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ Toff302 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 4 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸
       at 3 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 9 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸ done

  b3 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ Toff302 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 3 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 6 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 9 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b4 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 5 3 (Toff412 ∷ []) (wl1676 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 5 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 11 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸ done

  b5 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ Bx3-4120 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 9 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 5 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 6 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 2 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸ done

  b6 : Chain (Toff412 ∷ CCZ034 ∷ Bx3-4120 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CCZ134 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 2 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 3 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 7 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸ done

  b7 : Chain (Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CCZ134 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff412 ∷ Toff302 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 4 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 4 3 (Toff302 ∷ CCZ034 ∷ []) (wp1134 c4) ▸
       at 1 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 0 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸ done

  b8 : Chain (CCZ134 ∷ Toff412 ∷ Toff302 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 7 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 6 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 1 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸ done

  b9 : Chain (CCZ134 ∷ Toff302 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b10 : Chain (CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ Toff302 ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 3 3 (Toff412 ∷ []) (wl1676 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 3 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 9 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸ done

  b11 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ Toff302 ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx3-4120 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 3 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 2 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸ done

  b12 : Chain (Bx3-4120 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx3-4120 ∷ Bx4-1203 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff412 ∷ CCZ012 ∷ []) (wp0374 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 1 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done

  b13 : Chain (Bx3-4120 ∷ Bx4-1203 ∷ []) (Bx3-4120 ∷ Bx4-1230 ∷ [])
  b13 = at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1243-at043043 c4) ▸ done


-- box-perm-1423 @0314213240: 3 steps
lem-box-perm-1423-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1423-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸
       at 0 1 (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-pairs-at033440 c4) ▸ done


-- sym-ab @0440: 18 steps
lem-sym-ab-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-ab-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1230 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 4 1 (Bx4-20 ∷ []) (refl) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ [])
  b1 = at 2 6 (Bx2-430 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (wp0732 c4) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸
       at 10 1 (Bx4-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (Bx4-2130 ∷ [])
  b2 = at 5 6 (Bx2-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- cQ @04122140: 7 steps
lem-cQ-at04122140 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at04122140 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸ done


-- box-tQ @04122140: 13 steps
lem-box-tQ-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at04122140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2130 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at04122140 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done


-- CXbc-box @04122140: 17 steps
lem-CXbc-box-at04122140 : Ws → ⟪ (CX13 ∷ Bx4-2130 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx4-2130 ∷ CX13 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX13 ∷ CCZ014 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at04122140 c4) ▸
       at 0 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (sym (wp0121 c4)) ▸
       at 3 2 (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1439 c4) ▸
       at 2 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX13 ∷ CCZ014 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX13 ∷ []) (Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 3 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (sym (wp0121 c4)) ▸
       at 4 3 (CX13 ∷ []) (wp0125 c4) ▸
       at 0 4 (Bx4-2130 ∷ []) (sym (lem-box-tQ-at04122140 c4)) ▸ done

  b2 : Chain (Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CX13 ∷ []) (Bx4-2130 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1665 (lit c4))) ▸ done


-- CXcb-box @04122140: 18 steps
lem-CXcb-box-at04122140 : Ws → ⟪ (CX31 ∷ Bx4-2130 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx4-2130 ∷ CX31 ∷ []) (Toff412 ∷ CCZ034 ∷ CX31 ∷ Toff423 ∷ CS03 ∷ CX23 ∷ Toff412 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ034 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at04122140 c4) ▸
       at 0 2 (Toff412 ∷ CX31 ∷ Toff423 ∷ []) (wl1677 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) (sym (wp1440 c4)) ▸
       at 1 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 4 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 8 2 (Toff412 ∷ CS02 ∷ []) (wp1441 c4) ▸
       at 7 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 6 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ CX31 ∷ Toff423 ∷ CS03 ∷ CX23 ∷ Toff412 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ034 ∷ CX31 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX31 ∷ CCZ023 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 4 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 3 2 (Toff412 ∷ Toff423 ∷ []) (sym (wl0516 (lit c4))) ▸
       at 2 2 (Toff412 ∷ CX31 ∷ Toff423 ∷ []) (wl1677 (lit c4)) ▸
       at 3 3 (CX31 ∷ []) (wl1678 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 3 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX31 ∷ CCZ023 ∷ CX31 ∷ []) (Bx4-2130 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-2130 ∷ []) (sym (lem-box-tQ-at04122140 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1661 (lit c4))) ▸ done


-- SWbc-box @04122140: 11 steps
lem-SWbc-box-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-SWbc-box-at04122140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (CX13 ∷ Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx4-2130 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122140 c4) ▸
       at 3 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸
       at 1 3 (Bx4-2130 ∷ CCZ023 ∷ []) (lem-CXcb-box-at04122140 c4) ▸
       at 4 2 (CX13 ∷ CCZ012 ∷ []) (wl0167 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) (Bx4-2130 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1679 (lit c4)) ▸
       at 0 3 (Bx4-2130 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122140 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @04122140: 23 steps
lem-nat-SWbc-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ Sw13 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw13 ∷ []) (wl1680 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 4 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 5 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ Sw13 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ Sw13 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Sw13 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 7 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw13 ∷ []) (wl1680 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 11 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 12 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Sw13 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Sw13 ∷ []) (Bx4-2310 ∷ [])
  b2 = at 13 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 15 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-410 ∷ []) (refl) ▸
       at 5 6 (Bx2-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-2310 ∷ []) (refl) ▸ done


-- sym-bc @04122140: 2 steps
lem-sym-bc-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-bc-at04122140 c4 = run b0
  where
  b0 : Chain (Bx4-2130 ∷ []) (Bx4-2310 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at04122140 c4)) ▸
       at 0 3 (Bx4-2310 ∷ []) (lem-nat-SWbc-at04122140 c4) ▸ done


-- tP @0412233140: 7 steps
lem-tP-at0412233140 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233140 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff401 ∷ []) (wp0303 c4) ▸
       at 1 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸ done


-- P-box @0412233140: 8 steps
lem-P-box-at0412233140 : Ws → ⟪ (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-P-box-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) (Bx4-2310 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233140 c4) ▸
       at 0 2 (Toff423 ∷ Toff401 ∷ []) (sym (lem-tP-at0412233140 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) (sym (wp1338 c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (sym (lem-tP-at0412233140 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ01 ∷ []) (sym (wp1339 c4)) ▸
       at 2 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp1340 c4)) ▸
       at 0 4 (Bx4-2310 ∷ []) (sym (lem-box-tQ-at0412233140 c4)) ▸ done


-- VPQ @0412233140: 14 steps
lem-VPQ-at0412233140 : Ws → ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0412233140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (CS01⁻ ∷ CS23⁻ ∷ S4 ∷ Toff401 ∷ Toff423 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (sym (wl0455 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (sym (wp0304 c4)) ▸
       at 3 2 (CS01⁻ ∷ S4⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 1 2 (CS01⁻ ∷ S4 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑ ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (c₂ (CS • CS • CS) (CS • CS • CS))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS23⁻ ∷ S4 ∷ Toff401 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S)) ▸
       at 2 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff401 ∷ CCZ014 ∷ []) (wp0304 c4) ▸
       at 2 4 (Toff423 ∷ CCZ234 ∷ []) (wl0455 (lit c4)) ▸ done


-- QVQ @0412233140: 3 steps
lem-QVQ-at0412233140 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233140 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 1 4 (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at0412233140 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done


-- box-cP @0412233140: 12 steps
lem-box-cP-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-box-cP-at0412233140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2310 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 2 4 (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-QVQ-at0412233140 c4) ▸
       at 1 2 (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233140 c4) ▸
       at 2 2 [] (wl0457 (lit c4)) ▸ done


-- pairs @0412233140: 4 steps
lem-pairs-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-pairs-at0412233140 c4 = run b0
  where
  b0 : Chain (Bx4-2310 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Toff401 ∷ Bx4-2310 ∷ Toff401 ∷ []) (sym (lem-P-box-at0412233140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233140 c4) ▸
       at 4 2 [] (wp0306 c4) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done


-- box-perm-1423 @0440: 3 steps
lem-box-perm-1423-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1423-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-2130 ∷ []) (lem-sym-ab-at0440 c4) ▸
       at 0 1 (Bx4-2310 ∷ []) (lem-sym-bc-at04122140 c4) ▸
       at 0 1 (Bx4-1023 ∷ []) (lem-pairs-at0412233140 c4) ▸ done


-- CSu-box-3 @04203243: 17 steps
lem-CSu-box-3-at04203243 : Ws → ⟪ (CS24 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-3-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24 ∷ Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CS24 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 2 (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) (wl1682 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CS24 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24 ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 5 2 (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1683 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS23 ∷ []) (wl1684 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) (wl1682 (lit c4)) ▸
       at 4 6 (CS24 ∷ []) (wl1685 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24 ∷ []) (Bx4-1023 ∷ CS24 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done


-- CSdu-box-3 @04203243: 17 steps
lem-CSdu-box-3-at04203243 : Ws → ⟪ (CS24⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24⁻ ∷ Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 1 2 (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) (wl1686 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 5 2 (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1683 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS23⁻ ∷ []) (wl1687 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) (wl1686 (lit c4)) ▸
       at 4 6 (CS24⁻ ∷ []) (wl1688 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ []) (Bx4-1023 ∷ CS24⁻ ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done


-- F4-CS1-CS0 @0440: 214 steps
lem-F4-CS1-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (run b26))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b0 = at 3 1 (Sb3-4-01-2 ∷ []) (lem-F0-at0410213243 c4) ▸
       at 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24 ∷ []) (refl) ▸
       at 7 1 (CS24⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 4 2 (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) (wl1689 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CCZ034 ∷ CZ34 ∷ CCZ124 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b1 = at 6 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 9 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CZ34 ∷ []) (sym (wp1443 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CCZ034 ∷ CZ34 ∷ CCZ124 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Bx3-4012 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b2 = at 4 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 5 3 (X0 ∷ []) (wl1690 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 5 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 2 (Bx3-4012 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at0314203142 c4) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Bx3-4012 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b3 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 6 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 10 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b4 = at 7 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 5 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ Toff302 ∷ []) (sym (wp1438 c4)) ▸
       at 7 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 3 2 (Bx3-4012 ∷ CS13 ∷ []) (lem-CSu-box-3-at0314203142 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b5 = at 2 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 4 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 8 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Bx4-1230 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b6 = at 3 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 4 3 (CCZ034 ∷ Toff302 ∷ []) (sym (wp1438 c4)) ▸
       at 5 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1342-at04203243 c4) ▸
       at 2 1 (Bx3-4120 ∷ []) (lem-box-perm-1342-at0314203142 c4) ▸
       at 1 2 (Bx3-4120 ∷ Bx4-1230 ∷ []) (lem-box-box-3-at0440 c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-1423-at0314213240 c4) ▸ done

  b7 : Chain (X0 ∷ Bx3-4012 ∷ Bx4-1230 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ Toff312 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b7 = at 2 1 (Bx4-1023 ∷ []) (lem-box-perm-1423-at0440 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 2 2 (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) (wl1689 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b8 : Chain (CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ Toff312 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X0 ∷ Toff312 ∷ CCZ124 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b8 = at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ34 ∷ []) (sym (wp1443 c4)) ▸
       at 2 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1690 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X0 ∷ Toff312 ∷ CCZ124 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ124 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b9 = at 3 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 2 (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1691 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b10 : Chain (Bx3-4012 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ124 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b10 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 5 3 (Toff423 ∷ CCZ124 ∷ []) (wl1692 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸ done

  b11 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b11 = at 7 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 6 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸ done

  b12 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b12 = at 9 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 8 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 7 2 (X0 ∷ CCZ124 ∷ []) (wp1444 c4) ▸ done

  b13 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b13 = at 8 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX12 ∷ Toff201 ∷ X0 ∷ []) (sym (wl1693 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 6 1 (CS13⁻ ∷ []) (refl) ▸ done

  b14 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff403 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b14 = at 3 6 (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1694 (lit c4))) ▸
       at 2 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 2 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 5 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 7 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸ done

  b15 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff403 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b15 = at 9 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 11 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 4 3 (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp1450 c4) ▸
       at 3 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸ done

  b16 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b16 = at 4 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 5 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 6 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 10 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸ done

  b17 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b17 = at 5 2 (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1451 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1452 c4)) ▸
       at 5 4 (CZ14 ∷ CCZ014 ∷ []) (wp1453 c4) ▸
       at 2 5 (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) (wp1454 c4) ▸
       at 4 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b18 : Chain (Bx3-4012 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b18 = at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff201 ∷ X0 ∷ []) (sym (wl1696 (lit c4))) ▸
       at 4 2 (CS24 ∷ X0 ∷ []) (sym (wl1697 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 7 2 (CS24 ∷ CS13⁻ ∷ []) (wl1698 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b19 : Chain (Bx3-4012 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ Sb4-1-02-3 ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ [])
  b19 = at 5 2 (CS24 ∷ CS13 ∷ []) (wl1699 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 3 2 (CS24 ∷ Bx4-1023 ∷ []) (sym (lem-CSu-box-3-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ X0 ∷ []) (sym (wl1697 (lit c4))) ▸
       at 5 2 (CX12 ∷ Toff201 ∷ X0 ∷ []) (sym (wl1693 (lit c4))) ▸ done

  b20 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ Sb4-1-02-3 ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b20 = at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1694 (lit c4))) ▸
       at 4 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 7 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸ done

  b21 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b21 = at 8 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 9 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 11 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 12 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 13 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 14 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 8 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸ done

  b22 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b22 = at 6 3 (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp1450 c4) ▸
       at 5 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 7 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸ done

  b23 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b23 = at 11 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 7 2 (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1451 c4)) ▸
       at 9 2 (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1452 c4)) ▸
       at 7 4 (CZ14 ∷ CCZ014 ∷ []) (wp1453 c4) ▸
       at 4 5 (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) (wp1454 c4) ▸
       at 6 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done

  b24 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS24⁻ ∷ X0 ∷ [])
  b24 = at 6 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff201 ∷ X0 ∷ []) (sym (wl1696 (lit c4))) ▸
       at 6 2 (CS24⁻ ∷ X0 ∷ []) (sym (wl1700 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS24⁻ ∷ X0 ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ [])
  b25 = at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 7 2 (CS24⁻ ∷ CS13 ∷ []) (wl1701 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 5 2 (CS24⁻ ∷ Bx4-1023 ∷ []) (sym (lem-CSdu-box-3-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b26 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b26 = at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ X0 ∷ []) (sym (wl1700 (lit c4))) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-4-01-3 ∷ []) (sym (lem-F0-at0410213243 c4)) ▸ done


-- F4-I-CS0 @0440: 15 steps
lem-F4-I-CS0-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS0-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 1 4 (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1430 (lit c4))) ▸
       at 2 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 3 4 (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1430 (lit c4))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1279 c4)) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4)) ▸
       at 1 2 (X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1431 (lit c4))) ▸ done


-- box-perm-1324 @0214203143: 1 steps
lem-box-perm-1324-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-1324-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸ done


-- F4-K3-CS0 @0440: 19 steps
lem-F4-K3-CS0-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS0-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-box-perm-1324-at0214203143 c4) ▸
       at 3 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 1 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸ done

  b1 : Chain (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1702 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 4 (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1702 (lit c4))) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-cP-at0214213043 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1324-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1455 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- t-cP @04203243: 5 steps
lem-t-cP-at04203243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-t-cP-at04203243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (sym (wp1456 c4)) ▸
       at 2 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸
       at 2 3 (CCZ014 ∷ Toff401 ∷ []) (sym (wp1457 c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸ done


-- box2 @04203243: 11 steps
lem-box2-at04203243 : Ws → ⟪ (Bx4-1023 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ []) (lem-t-cP-at04203243 c4) ▸
       at 5 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 4 2 [] (wp0306 c4) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) []
  b1 = at 2 2 [] (wp0306 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wp0306 c4) ▸ done


-- S2-SBOX(0;1;42;3) @0440: 86 steps
lem-S2-SBOX⟨0·1·42·3⟩-at0440 : Ws → ⟪ (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b1 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 3 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 8 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 4 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b3 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 12 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 11 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 10 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 6 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 7 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b4 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 5 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 8 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 7 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 11 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 9 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 8 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b5 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 8 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 6 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 3 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 5 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 1 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 6 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸ done

  b7 : Chain (Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CCZ014 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 2 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 2 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b8 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff423 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 6 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸ done

  b9 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff423 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 5 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 6 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 5 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 4 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸ done

  b10 : Chain (Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ012 ∷ [])
  b10 = at 5 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 1 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 0 2 [] (lem-box2-at04203243 c4) ▸
       at 0 3 (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) (wl1519 (lit c4)) ▸
       at 2 2 [] (wl0341 (lit c4)) ▸
       at 0 8 (CCZ012 ∷ []) (sym (wl1703 (lit c4))) ▸ done


-- L-CX01-1 @0440: 2 steps
lem-L-CX01-1-at0440 : Ws → ⟪ (CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-L-CX01-1-at0440 c4 = run b0
  where
  b0 : Chain (CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ []) (Toff201 ∷ [])
  b0 = at 1 2 (CCZ012 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4) ▸
       at 0 4 (Toff201 ∷ []) (wl1704 (lit c4)) ▸ done


-- t-cP @04122041: 5 steps
lem-t-cP-at04122041 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-t-cP-at04122041 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) (sym (wp1458 c4)) ▸
       at 2 2 (Toff413 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF413 (lit c4)) ▸
       at 1 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04122041 c4) ▸
       at 2 3 (CCZ024 ∷ Toff402 ∷ []) (sym (wp1459 c4)) ▸
       at 3 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04122041 c4) ▸ done


-- box2 @04122041: 11 steps
lem-box2-at04122041 : Ws → ⟪ (Bx4-2031 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2031 ∷ Bx4-2031 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff402 ∷ []) (lem-t-cP-at04122041 c4) ▸
       at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 4 2 [] (wp1323 c4) ▸
       at 3 2 [] (wl0321 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) []
  b1 = at 2 2 [] (wp1323 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸
       at 0 2 [] (wp1323 c4) ▸ done


-- S2-SBOX(0;2;43;1) @0440: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0440 : Ws → ⟪ (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸ done

  b1 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 7 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 4 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b3 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b4 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 8 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 7 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 11 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 10 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 8 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸ done

  b5 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 8 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 6 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 7 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b6 : Chain (Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 5 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 1 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b7 : Chain (Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 2 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 2 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b8 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 6 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸ done

  b9 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff413 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 5 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 6 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 5 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 4 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸ done

  b10 : Chain (Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ023 ∷ [])
  b10 = at 5 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 1 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 0 2 [] (lem-box2-at04122041 c4) ▸
       at 0 3 (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4)) ▸
       at 2 2 [] (wl0204 (lit c4)) ▸
       at 0 8 (CCZ023 ∷ []) (sym (wl1705 (lit c4))) ▸ done


-- L-CX01-2 @0440: 2 steps
lem-L-CX01-2-at0440 : Ws → ⟪ (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-L-CX01-2-at0440 c4 = run b0
  where
  b0 : Chain (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ [])
  b0 = at 1 2 (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4) ▸
       at 0 4 (Toff302 ∷ []) (wl1706 (lit c4)) ▸ done


-- L-CX10-2 @0440: 2 steps
lem-L-CX10-2-at0440 : Ws → ⟪ (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-L-CX10-2-at0440 c4 = run b0
  where
  b0 : Chain (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ [])
  b0 = at 1 2 (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4) ▸
       at 0 4 (Toff203 ∷ []) (wl1707 (lit c4)) ▸ done

