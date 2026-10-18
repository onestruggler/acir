{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D215 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0006 ; wl0037 ; wl0038 ; wl0044 ; wl0084 ; wl0155 ; wl0172 ; wl0173 ; wl0181 ; wl0193 ; wl0195 ; wl0207 ; wl0228 ; wl0230 ; wl0280 ; wl0289 ; wl0321 ; wl0323 ; wl0341 ; wl0343 ; wl0448 ; wl0463 ; wl0503 ; wl0617 ; wl0677 ; wl0679 ; wl0746 ; wl0748 ; wl0807 ; wl0808 ; wl0861 ; wl0869 ; wl0879 ; wl0880 ; wl0882 ; wl0889 ; wl0921 ; wl0954 ; wl1021 ; wl1222 ; wl1226 ; wl1358 ; wl1368 ; wl1421 ; wl1422 ; wl1432 ; wl1433 ; wl1434 ; wl1435 ; wl1436 ; wl1437 ; wl1438 ; wl1446 ; wl1447 ; wl1448 ; wl1477 ; wl1478 ; wl1479 ; wl1480 ; wl1481 ; wl1516 ; wl1520 ; wl1525 ; wl1526 ; wl1528 ; wl1574 ; wl1576 ; wl1577 ; wl1586 ; wl1588 ; wl1625 ; wl1695 ; wl1698 ; wl1699 ; wl1701 ; wl1720 ; wl1727 ; wl1730 ; wl1731 ; wl1732 ; wl1733 ; wl1734 ; wl1735 ; wl1736 ; wl1737 ; wl1738 ; wl1739 ; wp0001 ; wp0002 ; wp0003 ; wp0021 ; wp0032 ; wp0033 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0053 ; wp0054 ; wp0066 ; wp0103 ; wp0104 ; wp0109 ; wp0110 ; wp0161 ; wp0179 ; wp0261 ; wp0285 ; wp0312 ; wp0313 ; wp0314 ; wp0496 ; wp0653 ; wp0655 ; wp0669 ; wp0706 ; wp0744 ; wp0747 ; wp0749 ; wp0760 ; wp0919 ; wp1143 ; wp1202 ; wp1250 ; wp1275 ; wp1276 ; wp1280 ; wp1281 ; wp1282 ; wp1283 ; wp1284 ; wp1285 ; wp1286 ; wp1287 ; wp1288 ; wp1289 ; wp1290 ; wp1291 ; wp1300 ; wp1301 ; wp1302 ; wp1316 ; wp1351 ; wp1352 ; wp1353 ; wp1376 ; wp1385 ; wp1436 ; wp1438 ; wp1445 ; wp1446 ; wp1447 ; wp1448 ; wp1449 ; wp1465 ; wp1483 ; wp1503 ; wp1506 ; wp1507 ; wp1508 ; wp1509 ; wp1510 ; wp1511 ; wp1512 ; wp1513 ; wp1514 ; wp1515 ; wp1516 ; wp1517 ; wp1518 ; wp1519)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at04203243 ; lem-box-cP-at043043 ; lem-box-tQ-at0330)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-cP-at0214213043)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D135 using (lem-box-perm-1324-at04203243 ; lem-box-tQ-at0413213240)
open import Examples.Groups.Clifford+CS.FiveV.D.D136 using (lem-box-cP-at0413213240)
open import Examples.Groups.Clifford+CS.FiveV.D.D137 using (lem-CSdu-box-3-at0314203142 ; lem-CSu-box-3-at0314203142 ; lem-F0-at0410213243 ; lem-box-perm-1342-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D138 using (lem-CSdu-box-3-at04203243 ; lem-CSu-box-3-at04203243 ; lem-box-perm-1324-at0214203143 ; lem-box-perm-1423-at0314213240 ; lem-pairs-at0412233140)
open import Examples.Groups.Clifford+CS.FiveV.D.D214 using (lem-box-perm-2341-at0314213240 ; lem-box-perm-4123-at0330 ; lem-box-perm-4132-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CS23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CS04-TOFF213 ; lem-comm-CSd03-CCZ124 ; lem-comm-CX31-CCZ024 ; lem-comm-CX40-TOFF312)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-CCZ013-CS24)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-CX40-TOFF213 ; lem-comm-TOFF213-CX40)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-CCZ124-CK03 ; lem-comm-CS02-TOFF413 ; lem-comm-CSd02-TOFF413 ; lem-comm-CX12-TOFF403 ; lem-comm-CX31-TOFF402 ; lem-comm-SWAP12-BOX⟨4·30⟩ ; lem-comm-TOFF312-CX40)
-- box-box-1 @0314213240: 105 steps
lem-box-box-1-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ Bx3-4120 ∷ []) ⟫ʷ
lem-box-box-1-at0314213240 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-4120 ∷ Bx4-3120 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CCZ134 ∷ CX32 ∷ CS03 ∷ Toff402 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-box-perm-2341-at0314213240 c4) ▸
       at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 4 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4) ▸
       at 3 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 4 2 (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp1506 c4) ▸
       at 6 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 10 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 9 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CCZ134 ∷ CX32 ∷ CS03 ∷ Toff402 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 7 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 6 3 (Toff402 ∷ CCZ034 ∷ []) (wp1507 c4) ▸
       at 3 4 (Bx4-3120 ∷ []) (sym (lem-box-cP-at0413213240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ Toff402 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 4 2 (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1385 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff402 ∷ K3⁻ ∷ []) (wp1508 c4) ▸
       at 8 2 (Toff402 ∷ CS23 ∷ []) (wp1509 c4) ▸
       at 7 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 6 2 (Toff402 ∷ CS12⁻ ∷ []) (wp1510 c4) ▸
       at 5 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸ done

  b3 : Chain (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ Toff402 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ Toff402 ∷ Toff312 ∷ CCZ124 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff402 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff402 ∷ CS12 ∷ []) (wp1316 c4) ▸
       at 3 2 (Toff402 ∷ K3 ∷ []) (wp1511 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 6 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 9 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b4 : Chain (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ Toff402 ∷ Toff312 ∷ CCZ124 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff402 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff402 ∷ K3⁻ ∷ CCZ012 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 5 3 (Toff312 ∷ []) (wl1730 (lit c4)) ▸
       at 6 2 (Toff402 ∷ CCZ012 ∷ []) (wp1512 c4) ▸
       at 5 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 11 2 (Toff402 ∷ K3⁻ ∷ []) (wp1508 c4) ▸ done

  b5 : Chain (Toff312 ∷ CCZ034 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff402 ∷ K3⁻ ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ Bx4-3120 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff402 ∷ CS23 ∷ []) (wp1509 c4) ▸
       at 9 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 8 2 (Toff402 ∷ CS12⁻ ∷ []) (wp1510 c4) ▸
       at 7 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 6 2 (Toff402 ∷ CS12 ∷ []) (wp1316 c4) ▸
       at 5 2 (Toff402 ∷ K3 ∷ []) (wp1511 c4) ▸
       at 6 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 2 4 (Bx4-3120 ∷ []) (sym (lem-box-cP-at0413213240 c4)) ▸ done

  b6 : Chain (Toff312 ∷ CCZ034 ∷ Bx4-3120 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ CS02 ∷ CCZ134 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ Toff402 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 2 2 (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp1506 c4) ▸
       at 4 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 7 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸ done

  b7 : Chain (Toff312 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ CS02 ∷ CCZ134 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ Toff402 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff312 ∷ Toff402 ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 4 3 (Toff402 ∷ CCZ034 ∷ []) (wp1507 c4) ▸
       at 1 4 (Bx4-3120 ∷ []) (sym (lem-box-cP-at0413213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4) ▸
       at 0 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 2 2 (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1385 c4) ▸ done

  b8 : Chain (CCZ134 ∷ Toff312 ∷ Toff402 ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff402 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 7 2 (Toff402 ∷ K3⁻ ∷ []) (wp1508 c4) ▸
       at 6 2 (Toff402 ∷ CS23 ∷ []) (wp1509 c4) ▸
       at 5 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 4 2 (Toff402 ∷ CS12⁻ ∷ []) (wp1510 c4) ▸
       at 3 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 2 2 (Toff402 ∷ CS12 ∷ []) (wp1316 c4) ▸
       at 1 2 (Toff402 ∷ K3 ∷ []) (wp1511 c4) ▸ done

  b9 : Chain (CCZ134 ∷ Toff402 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ012 ∷ CCZ134 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff402 ∷ Toff312 ∷ CCZ124 ∷ CCZ134 ∷ CCZ012 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b10 : Chain (CCZ134 ∷ Toff402 ∷ Toff312 ∷ CCZ124 ∷ CCZ134 ∷ CCZ012 ∷ Toff402 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff402 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 3 3 (Toff312 ∷ []) (wl1730 (lit c4)) ▸
       at 4 2 (Toff402 ∷ CCZ012 ∷ []) (wp1512 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff402 ∷ K3⁻ ∷ []) (wp1508 c4) ▸
       at 8 2 (Toff402 ∷ CS23 ∷ []) (wp1509 c4) ▸
       at 7 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸ done

  b11 : Chain (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff402 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-3120 ∷ Toff312 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff402 ∷ CS12⁻ ∷ []) (wp1510 c4) ▸
       at 5 2 (Toff402 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF402 (lit c4)) ▸
       at 4 2 (Toff402 ∷ CS12 ∷ []) (wp1316 c4) ▸
       at 3 2 (Toff402 ∷ K3 ∷ []) (wp1511 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 0 4 (Bx4-3120 ∷ []) (sym (lem-box-cP-at0413213240 c4)) ▸
       at 2 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸ done

  b12 : Chain (Bx4-3120 ∷ Toff312 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-3120 ∷ Bx3-1204 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 1 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done

  b13 : Chain (Bx4-3120 ∷ Bx3-1204 ∷ []) (Bx4-3120 ∷ Bx3-4120 ∷ [])
  b13 = at 1 1 (Bx3-4120 ∷ []) (lem-box-perm-4123-at0330 c4) ▸ done


-- CXbc-box @0413213240: 17 steps
lem-CXbc-box-at0413213240 : Ws → ⟪ (CX12 ∷ Bx4-3120 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx4-3120 ∷ CX12 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX12 ∷ CCZ014 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213240 c4) ▸
       at 0 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (sym (wp0744 c4)) ▸
       at 3 2 (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1513 c4) ▸
       at 2 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX12 ∷ CCZ014 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX12 ∷ []) (Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (sym (wp0744 c4)) ▸
       at 4 3 (CX12 ∷ []) (wp0747 c4) ▸
       at 0 4 (Bx4-3120 ∷ []) (sym (lem-box-tQ-at0413213240 c4)) ▸ done

  b2 : Chain (Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ []) (Bx4-3120 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl1477 (lit c4))) ▸ done


-- CXcb-box @0413213240: 18 steps
lem-CXcb-box-at0413213240 : Ws → ⟪ (CX21 ∷ Bx4-3120 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx4-3120 ∷ CX21 ∷ []) (Toff413 ∷ CCZ024 ∷ CX21 ∷ Toff423 ∷ CS02 ∷ CX32 ∷ Toff413 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ CCZ024 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213240 c4) ▸
       at 0 2 (Toff413 ∷ CX21 ∷ Toff423 ∷ []) (wl1731 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) (sym (wp1514 c4)) ▸
       at 1 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 4 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸
       at 7 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ CX21 ∷ Toff423 ∷ CS02 ∷ CX32 ∷ Toff413 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ CCZ024 ∷ CX21 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Toff423 ∷ []) (sym (wl1727 (lit c4))) ▸
       at 2 2 (Toff413 ∷ CX21 ∷ Toff423 ∷ []) (wl1731 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl1732 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ []) (Bx4-3120 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-3120 ∷ []) (sym (lem-box-tQ-at0413213240 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1478 (lit c4))) ▸ done


-- SWbc-box @0413213240: 11 steps
lem-SWbc-box-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (CX12 ∷ Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx4-3120 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0413213240 c4) ▸
       at 3 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸
       at 1 3 (Bx4-3120 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213240 c4) ▸
       at 4 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (Bx4-3120 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl1481 (lit c4)) ▸
       at 0 3 (Bx4-3120 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0413213240 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @0413213240: 23 steps
lem-nat-SWbc-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ Sw12 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 4 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 5 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ Sw12 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Sw12 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 7 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 12 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Sw12 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Sw12 ∷ []) (Bx4-3210 ∷ [])
  b2 = at 13 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 15 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-410 ∷ []) (refl) ▸
       at 5 6 (Bx3-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-3210 ∷ []) (refl) ▸ done


-- sym-bc @0413213240: 2 steps
lem-sym-bc-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-bc-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-3210 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0413213240 c4)) ▸
       at 0 3 (Bx4-3210 ∷ []) (lem-nat-SWbc-at0413213240 c4) ▸ done


-- sym-ab @04133140: 18 steps
lem-sym-ab-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-ab-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3210 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (wp1436 c4) ▸
       at 4 1 (Bx4-20 ∷ []) (refl) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ [])
  b1 = at 2 6 (Bx2-410 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (wp1436 c4) ▸
       at 7 1 (Bx4-20 ∷ []) (refl) ▸
       at 10 1 (Bx4-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (Bx4-2310 ∷ [])
  b2 = at 5 6 (Bx2-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-2310 ∷ []) (refl) ▸ done


-- box-perm-2431 @0413213240: 3 steps
lem-box-perm-2431-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-2431-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-3210 ∷ []) (lem-sym-bc-at0413213240 c4) ▸
       at 0 1 (Bx4-2310 ∷ []) (lem-sym-ab-at04133140 c4) ▸
       at 0 1 (Bx4-1023 ∷ []) (lem-pairs-at0412233140 c4) ▸ done


-- CXu-box-4 @0314203142: 15 steps
lem-CXu-box-4-at0314203142 : Ws → ⟪ (CX23 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Bx3-4012 ∷ []) (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 2 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 6 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-4012 ∷ CX23 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 1 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 2 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 3 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸ done


-- F4-CS0-CS1 @0440: 232 steps
lem-F4-CS0-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS1-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (run b28))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Sb3-4-01-2 ∷ []) (lem-F0-at0410213243 c4) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 4 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸ done

  b1 : Chain (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ014 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ014 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Bx4-1023 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 4 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 5 3 (X0 ∷ []) (wp1353 c4) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸
       at 5 2 (Bx4-1023 ∷ CS24⁻ ∷ []) (lem-CSdu-box-3-at04203243 c4) ▸ done

  b3 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Bx4-1023 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff403 ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 5 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 5 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 6 2 (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1515 c4) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 11 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 10 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸ done

  b4 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff403 ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ124 ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 5 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 12 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 11 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ124 ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff201 ∷ Toff403 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 10 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 7 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 7 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 8 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸ done

  b6 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff201 ∷ Toff403 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 13 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 12 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 11 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 10 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 7 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸ done

  b7 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff201 ∷ CCZ014 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 8 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 4 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 3 2 (Bx4-1023 ∷ CS24 ∷ []) (lem-CSu-box-3-at04203243 c4) ▸
       at 3 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 2 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸ done

  b8 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff201 ∷ CCZ014 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ K2 ∷ Toff403 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1515 c4) ▸
       at 3 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 9 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 8 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 5 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 4 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸ done

  b9 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ K2 ∷ Toff403 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CCZ124 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 3 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 4 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CCZ124 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b10 = at 7 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 4 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 5 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 6 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 11 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 10 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸ done

  b11 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Bx4-1023 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b11 = at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 5 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 2 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 2 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸ done

  b12 : Chain (X0 ∷ Bx3-4012 ∷ Bx4-1023 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ X0 ∷ Toff423 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b12 = at 1 1 (Bx3-4120 ∷ []) (lem-box-perm-1342-at0314203142 c4) ▸
       at 2 1 (Bx4-3120 ∷ []) (lem-box-perm-4132-at04203243 c4) ▸
       at 1 2 (Bx4-3120 ∷ Bx3-4120 ∷ []) (lem-box-box-1-at0314213240 c4) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-box-perm-2431-at0413213240 c4) ▸
       at 2 1 (Bx3-4012 ∷ []) (lem-box-perm-1423-at0314213240 c4) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 2 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ X0 ∷ Toff423 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ014 ∷ CCZ123 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b13 = at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b14 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ014 ∷ CCZ123 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b14 = at 3 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 3 3 (X0 ∷ []) (wp1353 c4) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b15 : Chain (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b15 = at 6 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b16 : Chain (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b16 = at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 5 3 (Toff312 ∷ CCZ123 ∷ []) (wl0889 (lit c4)) ▸ done

  b17 : Chain (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b17 = at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 3 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1733 (lit c4)) ▸
       at 6 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 5 2 (CS24 ∷ CCZ123 ∷ []) (wl0173 (lit c4)) ▸
       at 6 4 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1734 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ123 ∷ []) (wl0172 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ123 ∷ []) (wl1720 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b18 = at 4 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CCZ013 ∷ []) (wl1735 (lit c4)) ▸
       at 6 2 [] (wl0230 (lit c4)) ▸
       at 4 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 2 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 2 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸ done

  b19 : Chain (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff302 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b19 = at 4 1 (CS24 ∷ []) (refl) ▸
       at 6 1 (CS24⁻ ∷ []) (refl) ▸
       at 6 3 (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) (wp1516 c4) ▸
       at 5 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 4 3 (CX23 ∷ Toff302 ∷ CS24 ∷ []) (wp1517 c4) ▸
       at 3 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 2 2 (CX23 ∷ Bx3-4012 ∷ []) (sym (lem-CXu-box-4-at0314203142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b20 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff302 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b20 = at 6 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 5 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 4 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 6 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 6 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 7 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 8 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸ done

  b21 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b21 = at 9 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 3 3 (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 6 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 1 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸ done

  b22 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx3-4012 ∷ CS13 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b22 = at 4 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24 ∷ []) (refl) ▸
       at 7 1 (CS24⁻ ∷ []) (refl) ▸
       at 7 2 (CS13 ∷ CS24⁻ ∷ []) (sym (wl1701 (lit c4))) ▸
       at 6 2 (CS13 ∷ Toff201 ∷ []) (sym (wl1737 (lit c4))) ▸
       at 5 2 (CS13 ∷ CS24 ∷ []) (sym (wl1699 (lit c4))) ▸
       at 4 2 (CS13 ∷ Toff201 ∷ []) (sym (wl1737 (lit c4))) ▸ done

  b23 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx3-4012 ∷ CS13 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (CS13 ∷ Bx3-4012 ∷ []) (sym (lem-CSu-box-3-at0314203142 c4)) ▸
       at 6 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 4 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 1 (CS24 ∷ []) (refl) ▸ done

  b24 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b24 = at 8 1 (CS24⁻ ∷ []) (refl) ▸
       at 8 3 (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) (wp1516 c4) ▸
       at 7 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 6 3 (CX23 ∷ Toff302 ∷ CS24 ∷ []) (wp1517 c4) ▸
       at 5 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 4 2 (CX23 ∷ Bx3-4012 ∷ []) (sym (lem-CXu-box-4-at0314203142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 8 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸ done

  b25 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b25 = at 7 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 6 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 8 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 7 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 8 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 9 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 10 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b26 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ CS13⁻ ∷ X0 ∷ [])
  b26 = at 7 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 5 3 (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4) ▸
       at 6 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 8 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 3 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸ done

  b27 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ CS13⁻ ∷ X0 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ [])
  b27 = at 5 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 7 1 (CS24 ∷ []) (refl) ▸
       at 9 1 (CS24⁻ ∷ []) (refl) ▸
       at 9 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ Toff201 ∷ []) (sym (wl1738 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CS24 ∷ []) (sym (wl1698 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ Toff201 ∷ []) (sym (wl1738 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ Bx3-4012 ∷ []) (sym (lem-CSdu-box-3-at0314203142 c4)) ▸ done

  b28 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b28 = at 8 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 1 (Sb2-4-01-3 ∷ []) (sym (lem-F0-at0410213243 c4)) ▸ done


-- F4-S0-I @0440: 1 steps
lem-F4-S0-I-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1300 c4)) ▸ done


-- F4-CS0-I @0440: 15 steps
lem-F4-CS0-I-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-I-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (X0 ∷ CCZ024 ∷ Toff213 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp1301 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 3 (ι ∷ S0⁻ ∷ Toff213 ∷ []) (wl1447 (lit c4)) ▸
       at 3 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff213 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b1 = at 2 3 (ι ∷ S0⁻ ∷ Toff213 ∷ []) (wl1447 (lit c4)) ▸
       at 1 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 3 (S0 ∷ X0 ∷ []) (sym (wl1448 (lit c4))) ▸ done


-- F4-S0-K3 @0440: 1 steps
lem-F4-S0-K3-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1518 c4)) ▸ done


-- F4-CS0-K3 @0440: 21 steps
lem-F4-CS0-K3-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K3-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ []) (X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (sym (wl1574 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1519 c4)) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-box-perm-1324-at0214203143 c4) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 4 4 (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (sym (wl1739 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx2-4103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 4 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 2 4 (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (sym (wl1739 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 2 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 4 4 (Bx2-4103 ∷ []) (sym (lem-box-cP-at0214213043 c4)) ▸ done

  b2 : Chain (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx2-4103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1324-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK03 ∷ X0 ∷ []) (sym (wl1577 (lit c4))) ▸ done


-- F4-S0-CS0 @0440: 18 steps
lem-F4-S0-CS0-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS0-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1280 c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ S4 ∷ CS04⁻ ∷ [])
  b1 = at 2 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 2 3 (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (sym (wp1282 c4)) ▸
       at 4 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (Toff213 ∷ S4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 6 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) (wp1283 c4) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ S4 ∷ CS04⁻ ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b2 = at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done


-- F4-CS0-CS0 @0440: 286 steps
lem-F4-CS0-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 6 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 8 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 5 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 9 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 8 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 12 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸ done

  b7 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b7 = at 9 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 7 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 8 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b11 = at 7 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b12 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b12 = at 5 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b15 : Chain (Bx2-4013 ∷ X0 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b16 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ024 ∷ CX41 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 8 (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) (sym (wp1286 c4)) ▸
       at 10 2 [] (wl0321 (lit c4)) ▸ done

  b17 : Chain (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b17 = at 3 3 (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) (wp1276 c4) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 4 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (CS34 ∷ []) (refl) ▸ done

  b18 : Chain (Bx2-4013 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b18 = at 6 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1287 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸ done

  b19 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸ done

  b20 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b20 = at 9 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 4 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 5 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 6 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 8 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸ done

  b21 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff213 ∷ CS14 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b21 = at 4 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 7 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 9 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b22 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff213 ∷ CS14 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b22 = at 12 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 8 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 3 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b23 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b24 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b24 = at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 4 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸ done

  b25 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b25 = at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 4 5 (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1290 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 6 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b26 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ [])
  b26 = at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 2 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 5 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (CS34 ∷ []) (refl) ▸
       at 8 1 (CS34⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1287 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 6 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b28 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b29 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX12 ∷ CCZ014 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b29 = at 5 2 (CX12 ∷ Toff213 ∷ []) (sym (wl0748 (lit c4))) ▸
       at 7 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 8 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b30 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ Toff213 ∷ CX13 ∷ Toff201 ∷ CCZ014 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b30 = at 7 2 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (sym (wl0746 (lit c4))) ▸
       at 9 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 11 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS01⁻ ∷ Toff213 ∷ []) (sym (wl1422 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸ done

  b31 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ CX13 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff213 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b31 = at 10 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 11 2 (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (sym (wl1435 (lit c4))) ▸
       at 5 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 5 4 (CX13 ∷ Toff301 ∷ []) (wp1289 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b33 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 6 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (CS34 ∷ []) (refl) ▸
       at 9 1 (CS34⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ X0 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b34 = at 6 5 (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1291 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 8 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b35 = at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 4 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

