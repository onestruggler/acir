{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D137 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0003 ; wl0011 ; wl0012 ; wl0155 ; wl0171 ; wl0191 ; wl0196 ; wl0204 ; wl0258 ; wl0270 ; wl0274 ; wl0287 ; wl0293 ; wl0297 ; wl0305 ; wl0307 ; wl0321 ; wl0324 ; wl0335 ; wl0392 ; wl0393 ; wl0406 ; wl0433 ; wl0443 ; wl0452 ; wl0454 ; wl0456 ; wl0457 ; wl0467 ; wl0468 ; wl0469 ; wl0471 ; wl0499 ; wl0500 ; wl0501 ; wl0508 ; wl0516 ; wl0525 ; wl0617 ; wl0662 ; wl0663 ; wl0763 ; wl0765 ; wl0806 ; wl0808 ; wl0809 ; wl0844 ; wl0881 ; wl0882 ; wl0883 ; wl0884 ; wl0885 ; wl0886 ; wl0887 ; wl0954 ; wl1192 ; wl1204 ; wl1321 ; wl1329 ; wl1338 ; wl1343 ; wl1353 ; wl1370 ; wl1386 ; wl1399 ; wl1432 ; wl1433 ; wl1434 ; wl1436 ; wl1437 ; wl1438 ; wl1491 ; wl1492 ; wl1493 ; wl1494 ; wl1495 ; wl1507 ; wl1545 ; wl1569 ; wl1570 ; wl1571 ; wl1588 ; wl1596 ; wl1616 ; wl1620 ; wl1621 ; wl1622 ; wl1623 ; wl1624 ; wl1625 ; wl1626 ; wl1627 ; wl1628 ; wl1629 ; wl1630 ; wl1631 ; wl1632 ; wl1633 ; wl1634 ; wl1635 ; wl1636 ; wl1637 ; wl1638 ; wl1639 ; wl1640 ; wl1641 ; wl1642 ; wl1643 ; wl1644 ; wl1645 ; wl1646 ; wl1647 ; wl1648 ; wl1649 ; wl1650 ; wl1651 ; wl1652 ; wl1653 ; wl1654 ; wl1655 ; wl1656 ; wl1657 ; wl1658 ; wl1659 ; wl1660 ; wl1661 ; wl1662 ; wl1663 ; wl1664 ; wl1665 ; wl1666 ; wl1667 ; wl1668 ; wl1669 ; wl1670 ; wl1671 ; wl1672 ; wp0003 ; wp0007 ; wp0021 ; wp0028 ; wp0032 ; wp0033 ; wp0036 ; wp0037 ; wp0039 ; wp0062 ; wp0063 ; wp0064 ; wp0075 ; wp0088 ; wp0089 ; wp0090 ; wp0109 ; wp0124 ; wp0127 ; wp0155 ; wp0156 ; wp0157 ; wp0161 ; wp0167 ; wp0184 ; wp0185 ; wp0221 ; wp0231 ; wp0285 ; wp0311 ; wp0312 ; wp0314 ; wp0315 ; wp0316 ; wp0320 ; wp0376 ; wp0384 ; wp0388 ; wp0454 ; wp0523 ; wp0536 ; wp0537 ; wp0594 ; wp0685 ; wp0687 ; wp0700 ; wp0701 ; wp0717 ; wp0718 ; wp0719 ; wp0728 ; wp0729 ; wp0732 ; wp0733 ; wp0734 ; wp0776 ; wp0792 ; wp0794 ; wp0795 ; wp1071 ; wp1143 ; wp1171 ; wp1173 ; wp1185 ; wp1186 ; wp1187 ; wp1189 ; wp1192 ; wp1284 ; wp1285 ; wp1288 ; wp1365 ; wp1391 ; wp1392 ; wp1398 ; wp1419 ; wp1420 ; wp1421 ; wp1422 ; wp1423 ; wp1424 ; wp1425 ; wp1426 ; wp1427 ; wp1428 ; wp1429 ; wp1430 ; wp1431 ; wp1432 ; wp1433 ; wp1434 ; wp1435 ; wp1436 ; wp1437)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at04203243 ; lem-sym-ab-at0310243142 ; lem-tP-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0310243142 ; lem-box-cP-at0314203142 ; lem-box-tQ-at04203243 ; lem-sym-ab-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at0214203143 ; lem-sym-ab-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-sym-bc-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-sym-ab-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-box-tQ-at0210213443)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D019 using (lem-sym-ab-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-pairs-at0314203142 ; lem-sym-bc-at033440)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-box-tQ-at0310213442 ; lem-sym-bc-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-box-perm-1324-at0310213442 ; lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-pairs-at0210213443 ; lem-pairs-at0214233041 ; lem-sym-ab-at0213243041 ; lem-sym-ab-at0214233041 ; lem-sym-bc-at0210213443)
open import Examples.Groups.Clifford+CS.FiveV.D.D035 using (lem-box-cP-at0213243041 ; lem-box-cP-at0310213442 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D133 using (lem-box-cP-at04122041)
open import Examples.Groups.Clifford+CS.FiveV.D.D135 using (lem-CSdu-box-3-at0214203143 ; lem-CSu-box-3-at0214203143 ; lem-box-perm-1342-at0214203143 ; lem-box-perm-4132-at04122041)
open import Examples.Groups.Clifford+CS.FiveV.D.D136 using (lem-CSdu-box-3-at04122041 ; lem-CSu-box-3-at04122041 ; lem-box-box-2-at0440 ; lem-box-perm-1423-at02142140 ; lem-box-perm-2431-at0440)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX40-CCZ123 ; lem-comm-CX40-TOFF312 ; lem-comm-CZ12-TOFF403)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS04-CCZ123 ; lem-comm-CX03-CCZ124 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ034-CS12)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-CX40-TOFF213)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-CZ23-TOFF401 ; lem-comm-SWAP13-BOX⟨4·20⟩ ; lem-comm-TOFF403-CSd12 ; lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CSd02)
-- F4-CS2-CS0 @0440: 284 steps
lem-F4-CS2-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ134 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 2 (Bx2-4013 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0214203143 c4) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸ done

  b3 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b5 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CCZ024 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 9 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 13 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Bx2-4013 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b6 = at 10 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 8 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 7 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 8 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b7 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Bx2-4013 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b7 = at 3 2 (Bx2-4013 ∷ CS12 ∷ []) (lem-CSu-box-3-at0214203143 c4) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b9 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 7 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 11 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff103 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b10 = at 10 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 6 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl1620 (lit c4)) ▸
       at 6 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b11 = at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-4132-at04122041 c4) ▸
       at 2 1 (Bx2-4130 ∷ []) (lem-box-perm-1342-at0214203143 c4) ▸
       at 1 2 (Bx2-4130 ∷ Bx4-1230 ∷ []) (lem-box-box-2-at0440 c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-box-perm-1423-at02142140 c4) ▸
       at 2 1 (Bx4-2031 ∷ []) (lem-box-perm-2431-at0440 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b12 = at 2 2 (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff213 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b13 = at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b14 : Chain (Bx2-4013 ∷ X0 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CZ13 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b14 = at 2 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1616 (lit c4)) ▸ done

  b15 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CZ13 ∷ CCZ134 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CZ13 ∷ CCZ134 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b15 = at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CZ13 ∷ CCZ134 ∷ Toff413 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b16 = at 5 3 (Toff413 ∷ CCZ134 ∷ []) (wl1622 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 3 (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp1419 c4) ▸
       at 6 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 6 4 (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp1420 c4) ▸
       at 8 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ134 ∷ []) (wp1421 c4) ▸ done

  b17 : Chain (Bx2-4013 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ034 ∷ CS12 ∷ Toff103 ∷ CCZ034 ∷ CS12⁻ ∷ X0 ∷ CCZ134 ∷ CCZ134 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ Sb4-2-03-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b17 = at 10 2 [] (wl0321 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (Toff103 ∷ CCZ034 ∷ []) (wp1422 c4) ▸
       at 6 2 [] (wp0007 c4) ▸
       at 4 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸ done

  b18 : Chain (Bx2-4013 ∷ X0 ∷ Sb4-2-03-1 ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CX13 ∷ Toff401 ∷ Toff301 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b18 = at 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1623 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 7 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸ done

  b19 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CX13 ∷ Toff401 ∷ Toff301 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b19 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp1424 c4) ▸
       at 10 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b20 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b20 = at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 9 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (CX14 ∷ Toff413 ∷ []) (sym (wl1626 (lit c4))) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 5 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 6 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸ done

  b21 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 8 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 7 2 (Toff401 ∷ Toff413 ∷ []) (sym (wp1425 c4)) ▸
       at 9 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸ done

  b22 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX13 ∷ Toff301 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b22 = at 10 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 12 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 8 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 3 4 (CX13 ∷ Toff301 ∷ []) (wl1627 (lit c4)) ▸ done

  b23 : Chain (Bx2-4013 ∷ X0 ∷ CCZ024 ∷ CX13 ∷ Toff301 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ X0 ∷ CX13 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b23 = at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b24 : Chain (Bx2-4013 ∷ X0 ∷ CX13 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Sb4-2-03-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b24 = at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 4 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸ done

  b25 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ Sb4-2-03-1 ∷ CS34 ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b25 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 2 (CS34 ∷ CS12⁻ ∷ []) (wl1628 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff103 ∷ []) (sym (wp1427 c4)) ▸
       at 5 2 (CS34 ∷ CS12 ∷ []) (wl1629 (lit c4)) ▸
       at 4 2 (CS34 ∷ Toff103 ∷ []) (sym (wp1427 c4)) ▸
       at 3 2 (CS34 ∷ Bx4-2031 ∷ []) (sym (lem-CSu-box-3-at04122041 c4)) ▸ done

  b26 : Chain (Bx2-4013 ∷ Toff301 ∷ X0 ∷ CS34 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ [])
  b26 = at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 2 2 (CS34 ∷ X0 ∷ []) (sym (wl1437 (lit c4))) ▸
       at 5 2 (CX13 ∷ Toff301 ∷ X0 ∷ []) (sym (wl1434 (lit c4))) ▸
       at 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1623 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 7 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 6 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp1424 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸ done

  b28 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸ done

  b29 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX14 ∷ CCZ012 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ Toff413 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b29 = at 5 2 (CX14 ∷ Toff413 ∷ []) (sym (wl1626 (lit c4))) ▸
       at 7 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 6 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 7 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 8 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 10 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b30 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ Toff413 ∷ CX13 ∷ Toff401 ∷ CCZ012 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b30 = at 7 2 (CX14 ∷ CX13 ∷ Toff413 ∷ []) (sym (wl1624 (lit c4))) ▸
       at 9 2 (Toff401 ∷ Toff413 ∷ []) (sym (wp1425 c4)) ▸
       at 11 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 12 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff413 ∷ []) (sym (wl1588 (lit c4))) ▸
       at 14 2 (CS01 ∷ Toff413 ∷ []) (sym (wp1398 c4)) ▸ done

  b31 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CCZ024 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ CX13 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b31 = at 10 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 11 2 (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (sym (wp1423 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 5 4 (CX13 ∷ Toff301 ∷ []) (wl1627 (lit c4)) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

  b33 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ X0 ∷ CX13 ∷ Toff301 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS34⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 3 (Toff301 ∷ X0 ∷ []) (sym (wl1436 (lit c4))) ▸
       at 6 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS34⁻ ∷ X0 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b34 = at 9 2 (CS34⁻ ∷ CS12⁻ ∷ []) (wl1630 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff103 ∷ []) (sym (wp1428 c4)) ▸
       at 7 2 (CS34⁻ ∷ CS12 ∷ []) (wl1631 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff103 ∷ []) (sym (wp1428 c4)) ▸
       at 5 2 (CS34⁻ ∷ Bx4-2031 ∷ []) (sym (lem-CSdu-box-3-at04122041 c4)) ▸
       at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ X0 ∷ CS34⁻ ∷ Sb4-2-03-1 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b35 = at 4 2 (CS34⁻ ∷ X0 ∷ []) (sym (wl1438 (lit c4))) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- CSu-box-2 @0214203143: 17 steps
lem-CSu-box-2-at0214203143 : Ws → ⟪ (CS02 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-2-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Bx2-4013 ∷ []) (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) (wp1429 c4) ▸
       at 3 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 7 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS02 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (wp0454 c4) ▸
       at 2 2 (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ []) (wp1429 c4) ▸
       at 3 6 (CS02 ∷ []) (wp1430 c4) ▸
       at 3 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS02 ∷ []) (Bx2-4013 ∷ CS02 ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done


-- Ku-box @0214203143: 6 steps
lem-Ku-box-at0214203143 : Ws → ⟪ (K2 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ K2 ∷ []) ⟫ʷ
lem-Ku-box-at0214203143 c4 = run b0
  where
  b0 : Chain (K2 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ K2 ∷ []) (sym (wp0536 c4)) ▸
       at 1 2 (Toff213 ∷ K2 ∷ []) (wl0662 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K2 ∷ []) (sym (wp0536 c4)) ▸
       at 3 2 (Toff213 ∷ K2 ∷ []) (wl0662 (lit c4)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done


-- Kdu-box @0214203143: 6 steps
lem-Kdu-box-at0214203143 : Ws → ⟪ (K2⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ K2⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at0214203143 c4 = run b0
  where
  b0 : Chain (K2⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2⁻ ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ K2⁻ ∷ []) (sym (wp0537 c4)) ▸
       at 1 2 (Toff213 ∷ K2⁻ ∷ []) (wl0663 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K2⁻ ∷ []) (sym (wp0537 c4)) ▸
       at 3 2 (Toff213 ∷ K2⁻ ∷ []) (wl0663 (lit c4)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done


-- CKdu-box-2 @0214203143: 7 steps
lem-CKdu-box-2-at0214203143 : Ws → ⟪ (CK02⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CK02⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0214203143 c4 = run b0
  where
  b0 : Chain (CK02⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02⁻ ∷ [])
  b0 = at 0 1 (CS02 ∷ K2⁻ ∷ CS02 ∷ K2 ∷ CS02 ∷ []) (wl1632 (lit c4)) ▸
       at 4 2 (Bx2-4013 ∷ CS02 ∷ []) (lem-CSu-box-2-at0214203143 c4) ▸
       at 3 2 (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4) ▸
       at 2 2 (Bx2-4013 ∷ CS02 ∷ []) (lem-CSu-box-2-at0214203143 c4) ▸
       at 1 2 (Bx2-4013 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ CS02 ∷ []) (lem-CSu-box-2-at0214203143 c4) ▸
       at 1 5 (CK02⁻ ∷ []) (sym (wl1632 (lit c4))) ▸ done


-- XCKX-box-2 @0214203143: 4 steps
lem-XCKX-box-2-at0214203143 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0214203143 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 3 (K2 ∷ CK02⁻ ∷ []) (sym (wl1633 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ CK02⁻ ∷ []) (lem-CKdu-box-2-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4) ▸
       at 1 2 (X0 ∷ CK02 ∷ X0 ∷ []) (wl1633 (lit c4)) ▸ done


-- F4-K2-CS0 @0440: 11 steps
lem-F4-K2-CS0-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS0-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-XCKX-box-2-at0214203143 c4) ▸
       at 1 4 (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1634 (lit c4))) ▸
       at 2 4 (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1431 c4)) ▸
       at 3 4 (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1634 (lit c4))) ▸
       at 4 4 (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1432 c4)) ▸ done

  b1 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- box-perm-2314 @0214203143: 2 steps
lem-box-perm-2314-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-2314-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸ done


-- box-perm-3124 @0310213442: 2 steps
lem-box-perm-3124-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-3124-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done


-- box-perm-4312 @0210213443: 2 steps
lem-box-perm-4312-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-4312-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸ done


-- box-box-4 @0314203142: 103 steps
lem-box-box-4-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-box-box-4-at0314203142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-4012 ∷ Bx2-3401 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 4 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1635 (lit c4)) ▸
       at 6 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 6 3 (Toff201 ∷ CCZ123 ∷ []) (wl1636 (lit c4)) ▸
       at 3 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ Toff201 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b2 = at 4 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ Toff201 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ [])
  b3 = at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 6 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 7 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ Toff201 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 6 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 11 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 10 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ Toff201 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 9 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 8 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 5 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 6 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 2 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1635 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 7 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b7 : Chain (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 4 3 (Toff201 ∷ CCZ123 ∷ []) (wl1636 (lit c4)) ▸
       at 1 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸ done

  b8 : Chain (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ234 ∷ CCZ014 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 7 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ234 ∷ CCZ014 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ Toff201 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 4 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸ done

  b11 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ Toff201 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b12 : Chain (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ [])
  b12 = at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done


-- box-perm-3421 @0213243041: 2 steps
lem-box-perm-3421-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4) ▸ done


-- box-perm-2314 @0314203142: 2 steps
lem-box-perm-2314-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-2314-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸ done


-- F0-B @0410213243: 62 steps
lem-F0-B-at0410213243 : Ws → ⟪ (CX23 ∷ Bx2-0143 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Bx3-0142 ∷ []) ⟫ʷ
lem-F0-B-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX23 ∷ Bx2-0143 ∷ CX23 ∷ []) (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CZ24 ∷ CCZ014 ∷ CCZ234 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ Toff301 ∷ CX23 ∷ []) (wl1637 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ24 ∷ CX23 ∷ []) (sym (wl1638 (lit c4))) ▸
       at 4 2 (Toff201 ∷ Toff301 ∷ CX23 ∷ []) (wl1637 (lit c4)) ▸
       at 6 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl1639 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) (wp1433 c4) ▸
       at 5 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CZ24 ∷ CCZ014 ∷ CCZ234 ∷ CZ24 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CZ24 ∷ []) (sym (wp1434 c4)) ▸
       at 6 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff201 ∷ []) (wl1386 (lit c4)) ▸
       at 4 0 (CCZ234 ∷ CCZ234 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 1 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1640 (lit c4))) ▸ done

  b2 : Chain (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff201 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 5 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 1 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 1 7 (Toff201 ∷ []) (wl1640 (lit c4)) ▸ done

  b3 : Chain (CCZ034 ∷ Toff201 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ Toff301 ∷ CCZ014 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b3 = at 1 2 (Toff312 ∷ Toff201 ∷ Toff301 ∷ []) (wl1641 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1640 (lit c4))) ▸
       at 8 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b4 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ Toff301 ∷ CCZ014 ∷ Toff312 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff201 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 3 7 (Toff201 ∷ []) (wl1640 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸ done

  b5 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff201 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-0142 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 5 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff201 ∷ Toff301 ∷ []) (wl1641 (lit c4)) ▸
       at 4 3 (Toff201 ∷ []) (wl1642 (lit c4)) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 0 1 (Bx3-0142 ∷ []) (sym (lem-box-perm-1324-at0310213442 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸ done

  b6 : Chain (Bx3-0142 ∷ Toff201 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-0142 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b6 = at 6 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 3 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 4 2 [] (wp0161 c4) ▸ done

  b7 : Chain (Bx3-0142 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ [])
  b7 = at 1 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-box-perm-3124-at0310213442 c4) ▸
       at 1 1 (Bx2-3401 ∷ []) (lem-box-perm-4312-at0210213443 c4) ▸
       at 0 2 (Bx2-3401 ∷ Bx3-4012 ∷ []) (lem-box-box-4-at0314203142 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-box-perm-3421-at0213243041 c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-box-perm-2314-at0314203142 c4) ▸ done


-- CSdu-box-3 @0310213442: 17 steps
lem-CSdu-box-3-at0310213442 : Ws → ⟪ (CS34⁻ ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34⁻ ∷ Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 0 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) (wl1643 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 7 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 5 2 (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) (wl1204 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS24⁻ ∷ []) (wl1644 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) (wl1643 (lit c4)) ▸
       at 4 6 (CS34⁻ ∷ []) (wl1645 (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ []) (Bx3-0142 ∷ CS34⁻ ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸ done


-- F0-R @0410213243: 11 steps
lem-F0-R-at0410213243 : Ws → ⟪ (CX23 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS34⁻ ∷ CCZ234 ∷ CX23 ∷ [])
  b0 = at 0 2 (Toff301 ∷ CX23 ∷ []) (wl1646 (lit c4)) ▸
       at 1 2 (CS34 ∷ CS24 ∷ CCZ234 ∷ CX23 ∷ []) (sym (wl1647 (lit c4))) ▸
       at 4 2 (Toff301 ∷ CX23 ∷ []) (wl1646 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CX23 ∷ []) (sym (wl1648 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ CS24 ∷ []) (sym (wl1649 (lit c4))) ▸
       at 3 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 4 3 (CS34⁻ ∷ []) (wl1650 (lit c4)) ▸
       at 2 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸ done

  b1 : Chain (Toff301 ∷ CS34 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS34⁻ ∷ CCZ234 ∷ CX23 ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ CS34⁻ ∷ []) (sym (wl1651 (lit c4))) ▸
       at 3 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸
       at 3 2 (CS34⁻ ∷ Bx3-0142 ∷ []) (sym (lem-CSdu-box-3-at0310213442 c4)) ▸ done


-- CSu-box-3 @0310213442: 17 steps
lem-CSu-box-3-at0310213442 : Ws → ⟪ (CS34 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34 ∷ Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 2 (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) (wl1652 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 7 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff324 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34 ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 5 2 (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) (wl1204 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS24 ∷ []) (wl1653 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) (wl1652 (lit c4)) ▸
       at 4 6 (CS34 ∷ []) (wl1654 (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34 ∷ []) (Bx3-0142 ∷ CS34 ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸ done


-- t-cP @0310213442: 5 steps
lem-t-cP-at0310213442 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at0310213442 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 2 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (sym (wl1370 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸
       at 2 3 (CCZ013 ∷ Toff301 ∷ []) (sym (wl1192 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸ done


-- box2 @0310213442: 11 steps
lem-box2-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0142 ∷ Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at0310213442 c4) ▸
       at 5 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done


-- box-perm-3124 @0210213443: 2 steps
lem-box-perm-3124-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-3124-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-bc-at0210213443 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸ done


-- CXuA-S @0410213243: 44 steps
lem-CXuA-S-at0410213243 : Ws → ⟪ (CX23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX23 ∷ Sb2-4-01-3 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Bx3-0142 ∷ CS34⁻ ∷ CX23 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-2314-at0214203143 c4) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 0 3 (Bx2-0143 ∷ Bx3-0142 ∷ []) (lem-F0-B-at0410213243 c4) ▸
       at 2 5 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ []) (lem-F0-R-at0410213243 c4) ▸
       at 5 2 (Bx3-0142 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at0310213442 c4) ▸ done

  b1 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Bx3-0142 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34⁻ ∷ CX23 ∷ [])
  b1 = at 5 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸ done

  b2 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ Bx3-0142 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b2 = at 6 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ Toff301 ∷ []) (sym (wp1435 c4)) ▸
       at 7 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 4 1 (Bx3-0142 ∷ []) (sym (lem-box-perm-1324-at0310213442 c4)) ▸
       at 3 2 (Bx3-0142 ∷ CS34 ∷ []) (lem-CSu-box-3-at0310213442 c4) ▸ done

  b3 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ Bx3-0142 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b3 = at 3 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸ done

  b4 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b4 = at 4 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 4 3 (CCZ034 ∷ Toff301 ∷ []) (sym (wp1435 c4)) ▸
       at 5 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (Bx3-0142 ∷ []) (sym (lem-box-perm-1324-at0310213442 c4)) ▸
       at 1 2 [] (lem-box2-at0310213442 c4) ▸ done

  b5 : Chain (Bx2-0143 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Sb2-4-01-3 ∷ CX23 ∷ [])
  b5 = at 0 1 (Bx2-4013 ∷ []) (lem-box-perm-3124-at0210213443 c4) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- CXu-box-4 @0214203143: 15 steps
lem-CXu-box-4-at0214203143 : Ws → ⟪ (CX32 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Bx2-4013 ∷ []) (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 2 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 6 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ []) (Bx2-4013 ∷ CX32 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 1 2 (Toff213 ∷ CX32 ∷ []) (wl0809 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 2 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 3 3 (CX32 ∷ []) (wp0718 c4) ▸
       at 3 2 (Toff213 ∷ CX32 ∷ []) (wl0809 (lit c4)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done


-- CXAu-S @0410213243: 12 steps
lem-CXAu-S-at0410213243 : Ws → ⟪ (CX32 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Sb2-4-01-3 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CX32 ∷ CS34⁻ ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-4013 ∷ CX32 ∷ []) (lem-CXu-box-4-at0214203143 c4) ▸
       at 1 2 (Toff301 ∷ CX32 ∷ Toff201 ∷ []) (wl1655 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS)) ▸
       at 2 2 (CS34 ∷ CX32 ∷ []) (sym (wl1656 (lit c4))) ▸
       at 3 3 (Toff301 ∷ CX32 ∷ []) (wl1657 (lit c4)) ▸ done

  b1 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CX32 ∷ CS34⁻ ∷ []) (Sb2-4-01-3 ∷ CX32 ∷ [])
  b1 = at 4 2 (CS34⁻ ∷ CX32 ∷ []) (sym (wl1658 (lit c4))) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- SW-S @0410213243: 5 steps
lem-SW-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at0410213243 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 2 (Sb2-4-01-3 ∷ CX23 ∷ []) (lem-CXuA-S-at0410213243 c4) ▸
       at 1 2 (Sb2-4-01-3 ∷ CX32 ∷ []) (lem-CXAu-S-at0410213243 c4) ▸
       at 0 2 (Sb2-4-01-3 ∷ CX23 ∷ []) (lem-CXuA-S-at0410213243 c4) ▸
       at 1 3 (Sw23 ∷ []) (wl0258 (lit c4)) ▸ done


-- nat-S @0410213243: 31 steps
lem-nat-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ []) ⟫ʷ
lem-nat-S-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Sb2-4-01-3 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b1 = at 8 1 (CZ34 ∷ []) (refl) ▸
       at 2 7 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (sym (wl1659 (lit c4))) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (wp0719 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 6 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Toff201 ∷ CS24 ∷ Sw23 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ [])
  b2 = at 8 1 (CZ34 ∷ []) (refl) ▸
       at 11 1 (CZ34 ∷ []) (refl) ▸
       at 5 7 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (sym (wl1659 (lit c4))) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸
       at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 6 2 (Toff201 ∷ Sw23 ∷ []) (wl1660 (lit c4)) ▸
       at 7 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸ done

  b3 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Toff201 ∷ CS24 ∷ Sw23 ∷ Toff301 ∷ CS34⁻ ∷ Sw23 ∷ []) (Sb3-4-01-2 ∷ [])
  b3 = at 8 2 (Toff201 ∷ Sw23 ∷ []) (wl1660 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 (lit c4))) ▸
       at 10 2 [] (wl0003 (lit c4)) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done


-- F0 @0410213243: 3 steps
lem-F0-at0410213243 : Ws → ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ []) ⟫ʷ
lem-F0-at0410213243 c4 = run b0
  where
  b0 : Chain (Sb2-4-01-3 ∷ []) (Sb3-4-01-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Sb2-4-01-3 ∷ Sw23 ∷ []) (lem-SW-S-at0410213243 c4) ▸
       at 0 3 (Sb3-4-01-2 ∷ []) (lem-nat-S-at0410213243 c4) ▸ done


-- CSdu-box-3 @0314203142: 17 steps
lem-CSdu-box-3-at0314203142 : Ws → ⟪ (CS13⁻ ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13⁻ ∷ Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl0885 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS12⁻ ∷ []) (wl0886 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl0885 (lit c4)) ▸
       at 4 6 (CS13⁻ ∷ []) (wl0887 (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ []) (Bx3-4012 ∷ CS13⁻ ∷ [])
  b2 = at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸ done


-- CSu-box-3 @0314203142: 17 steps
lem-CSu-box-3-at0314203142 : Ws → ⟪ (CS13 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS12 ∷ []) (wl0883 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 6 (CS13 ∷ []) (wl0884 (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ []) (Bx3-4012 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸ done


-- P-box @04203243: 8 steps
lem-P-box-at04203243 : Ws → ⟪ (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-P-box-at04203243 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at04203243 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (sym (wl1491 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at04203243 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1492 (lit c4))) ▸
       at 2 2 (Toff401 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF401 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl1493 (lit c4))) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done


-- cQ @0412233140: 7 steps
lem-cQ-at0412233140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done


-- box-tQ @0412233140: 13 steps
lem-box-tQ-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at0412233140 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 0 2 (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl1494 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233140 c4) ▸
       at 2 4 (Toff423 ∷ []) (wl1495 (lit c4)) ▸ done


-- pairs @04203243: 4 steps
lem-pairs-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-pairs-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-2310 ∷ [])
  b0 = at 0 1 (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) (sym (lem-P-box-at04203243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 [] (wl0457 (lit c4)) ▸
       at 0 4 (Bx4-2310 ∷ []) (sym (lem-box-tQ-at0412233140 c4)) ▸ done


-- CXbc-box @0412233140: 17 steps
lem-CXbc-box-at0412233140 : Ws → ⟪ (CX31 ∷ Bx4-2310 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx4-2310 ∷ CX31 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX31 ∷ CCZ034 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233140 c4) ▸
       at 0 2 (Toff423 ∷ CX31 ∷ []) (wl1507 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 3 2 (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp1365 c4) ▸
       at 2 2 (Toff423 ∷ CX31 ∷ []) (wl1507 (lit c4)) ▸
       at 5 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX31 ∷ CCZ034 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ CX31 ∷ []) (Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 3 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 4 3 (CX31 ∷ []) (wp0794 c4) ▸
       at 0 4 (Bx4-2310 ∷ []) (sym (lem-box-tQ-at0412233140 c4)) ▸ done

  b2 : Chain (Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CX31 ∷ []) (Bx4-2310 ∷ CCZ023 ∷ [])
  b2 = at 1 3 (CCZ023 ∷ []) (sym (wl1661 (lit c4))) ▸ done


-- CXcb-box @0412233140: 18 steps
lem-CXcb-box-at0412233140 : Ws → ⟪ (CX13 ∷ Bx4-2310 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx4-2310 ∷ CX13 ∷ []) (Toff423 ∷ CCZ014 ∷ CX13 ∷ Toff412 ∷ CS01 ∷ CX21 ∷ Toff423 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ014 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233140 c4) ▸
       at 0 2 (Toff423 ∷ CX13 ∷ Toff412 ∷ []) (wl1662 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 1 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 4 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX21 ∷ []) (wl1663 (lit c4)) ▸
       at 6 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ CX13 ∷ Toff412 ∷ CS01 ∷ CX21 ∷ Toff423 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ014 ∷ CX13 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX13 ∷ CCZ012 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff423 ∷ CX21 ∷ []) (wl1663 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 2 2 (Toff423 ∷ CX13 ∷ Toff412 ∷ []) (wl1662 (lit c4)) ▸
       at 3 3 (CX13 ∷ []) (wl1664 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 3 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸ done

  b2 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX13 ∷ CCZ012 ∷ CX13 ∷ []) (Bx4-2310 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx4-2310 ∷ []) (sym (lem-box-tQ-at0412233140 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1665 (lit c4))) ▸ done


-- SWbc-box @0412233140: 11 steps
lem-SWbc-box-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-SWbc-box-at0412233140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (CX31 ∷ Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx4-2310 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0412233140 c4) ▸
       at 3 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸
       at 1 3 (Bx4-2310 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0412233140 c4) ▸
       at 4 2 (CX31 ∷ CCZ023 ∷ []) (wl1343 (lit c4)) ▸
       at 3 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸ done

  b1 : Chain (CX31 ∷ Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) (Bx4-2310 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1668 (lit c4)) ▸
       at 0 3 (Bx4-2310 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0412233140 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done


-- nat-SWbc @0412233140: 23 steps
lem-nat-SWbc-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ Sw13 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw13 ∷ []) (wl1670 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 4 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ Sw13 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ Sw13 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Sw13 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 7 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 8 2 (Toff412 ∷ Sw13 ∷ []) (wl1670 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 11 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 12 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Sw13 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Sw13 ∷ []) (Bx4-2130 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 15 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-430 ∷ []) (refl) ▸
       at 5 6 (Bx2-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- sym-bc @0412233140: 2 steps
lem-sym-bc-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-bc-at0412233140 c4 = run b0
  where
  b0 : Chain (Bx4-2310 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at0412233140 c4)) ▸
       at 0 3 (Bx4-2130 ∷ []) (lem-nat-SWbc-at0412233140 c4) ▸ done


-- sym-ab @04122140: 18 steps
lem-sym-ab-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-ab-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2130 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 4 1 (Bx4-10 ∷ []) (refl) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ [])
  b1 = at 2 6 (Bx1-430 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (wp0733 c4) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸
       at 10 1 (Bx4-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (Bx4-1230 ∷ [])
  b2 = at 5 6 (Bx1-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- box-perm-1342 @04203243: 3 steps
lem-box-perm-1342-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1342-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Bx4-2310 ∷ []) (lem-pairs-at04203243 c4) ▸
       at 0 1 (Bx4-2130 ∷ []) (lem-sym-bc-at0412233140 c4) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-sym-ab-at04122140 c4) ▸ done


-- box-perm-1342 @0314203142: 3 steps
lem-box-perm-1342-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-1342-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-pairs-at0314203142 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4) ▸
       at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸ done


-- sym-ab @0413203142: 18 steps
lem-sym-ab-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-sym-ab-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3012 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (sym (wp1437 c4)) ▸
       at 4 1 (Bx4-02 ∷ []) (refl) ▸
       at 7 1 (Bx4-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ [])
  b1 = at 2 6 (Bx0-412 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (sym (wp1437 c4)) ▸
       at 7 1 (Bx4-02 ∷ []) (refl) ▸
       at 10 1 (Bx4-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (Bx4-0312 ∷ [])
  b2 = at 5 6 (Bx0-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- cQ @0410233142: 7 steps
lem-cQ-at0410233142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 4 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸ done


-- box-tQ @0410233142: 13 steps
lem-box-tQ-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233142 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done


-- tP @0410233142: 7 steps
lem-tP-at0410233142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233142 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done


-- P-box @0410233142: 8 steps
lem-P-box-at0410233142 : Ws → ⟪ (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-P-box-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-0312 ∷ Toff412 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0410233142 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233142 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233142 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-0312 ∷ []) (sym (lem-box-tQ-at0410233142 c4)) ▸ done


-- VPQ @0410233142: 14 steps
lem-VPQ-at0410233142 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0410233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done

