{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D136 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0018 ; wl0155 ; wl0175 ; wl0179 ; wl0181 ; wl0204 ; wl0230 ; wl0258 ; wl0263 ; wl0280 ; wl0289 ; wl0297 ; wl0334 ; wl0341 ; wl0411 ; wl0454 ; wl0456 ; wl0467 ; wl0468 ; wl0469 ; wl0470 ; wl0471 ; wl0560 ; wl0616 ; wl0619 ; wl0620 ; wl0621 ; wl0624 ; wl0625 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0639 ; wl0651 ; wl0707 ; wl0755 ; wl0757 ; wl0770 ; wl0831 ; wl0901 ; wl1126 ; wl1131 ; wl1150 ; wl1472 ; wl1473 ; wl1474 ; wl1485 ; wl1486 ; wl1500 ; wl1502 ; wl1546 ; wl1564 ; wl1565 ; wl1566 ; wl1567 ; wl1568 ; wl1569 ; wl1570 ; wl1571 ; wl1589 ; wl1592 ; wl1594 ; wl1596 ; wl1597 ; wl1598 ; wl1599 ; wl1600 ; wl1601 ; wl1602 ; wl1603 ; wl1604 ; wl1605 ; wl1606 ; wl1607 ; wl1608 ; wl1609 ; wl1610 ; wl1611 ; wl1612 ; wl1613 ; wl1614 ; wl1615 ; wl1616 ; wl1617 ; wl1618 ; wl1619 ; wp0001 ; wp0002 ; wp0003 ; wp0007 ; wp0021 ; wp0022 ; wp0032 ; wp0034 ; wp0035 ; wp0036 ; wp0039 ; wp0081 ; wp0087 ; wp0092 ; wp0101 ; wp0104 ; wp0109 ; wp0110 ; wp0135 ; wp0186 ; wp0198 ; wp0211 ; wp0212 ; wp0315 ; wp0316 ; wp0317 ; wp0318 ; wp0375 ; wp0384 ; wp0513 ; wp0514 ; wp0515 ; wp0669 ; wp0672 ; wp0675 ; wp0676 ; wp0677 ; wp0678 ; wp0679 ; wp0695 ; wp0696 ; wp0733 ; wp0746 ; wp0766 ; wp0767 ; wp0827 ; wp0914 ; wp0919 ; wp0992 ; wp1190 ; wp1191 ; wp1193 ; wp1196 ; wp1197 ; wp1198 ; wp1199 ; wp1321 ; wp1322 ; wp1323 ; wp1374 ; wp1377 ; wp1391 ; wp1392 ; wp1399 ; wp1400 ; wp1401 ; wp1402 ; wp1403 ; wp1404 ; wp1405 ; wp1406 ; wp1407 ; wp1408 ; wp1409 ; wp1410 ; wp1411 ; wp1412 ; wp1413 ; wp1414 ; wp1415 ; wp1416 ; wp1417 ; wp1418)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-pairs-at02233440 ; lem-sym-bc-at022440)
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-tQ-at04122041 ; lem-box-tQ-at04233042)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-box-tQ-at0413213240 ; lem-box-tQ-at0440 ; lem-cQ-at0413213240 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CS03-TOFF412 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd12-TOFF403 ; lem-comm-CX31-CCZ024 ; lem-comm-CZ03-TOFF412 ; lem-comm-CZ12-TOFF403 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF203 ; lem-comm-CX30-CCZ124 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ03-CCZ124 ; lem-comm-TOFF214-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CS02-TOFF413 ; lem-comm-CS12-TOFF403 ; lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-CX41-TOFF203 ; lem-comm-CZ02-TOFF413 ; lem-comm-TOFF403-CSd12 ; lem-comm-TOFF413-CSd02)
-- P-box @0440: 8 steps
lem-P-box-at0440 : Ws → ⟪ (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-P-box-at0440 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at0440 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (sym (wp1399 c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at0440 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ03 ∷ []) (sym (wp1400 c4)) ▸
       at 2 2 (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0375 c4)) ▸
       at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸ done


-- VPQ @0440: 14 steps
lem-VPQ-at0440 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done


-- QVQ @0440: 3 steps
lem-QVQ-at0440 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0440 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0440 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @0440: 12 steps
lem-box-cP-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1230 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at0440 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done


-- cQ @0413203142: 7 steps
lem-cQ-at0413203142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 4 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸ done


-- box-tQ @0413203142: 13 steps
lem-box-tQ-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3012 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203142 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done


-- pairs @0440: 4 steps
lem-pairs-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-pairs-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 0 1 (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) (sym (lem-P-box-at0440 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0440 c4) ▸
       at 4 2 [] (wp0317 c4) ▸
       at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸ done


-- CXbc-box @0413203142: 17 steps
lem-CXbc-box-at0413203142 : Ws → ⟪ (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CX01 ∷ CCZ024 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CCZ124 ∷ CX30 ∷ CS23 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ CX01 ∷ []) (wp1401 c4) ▸
       at 1 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 3 2 (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1402 c4) ▸
       at 2 2 (Toff403 ∷ CX01 ∷ []) (wp1401 c4) ▸
       at 5 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CX01 ∷ CCZ024 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CCZ124 ∷ CX30 ∷ CS23 ∷ CX01 ∷ []) (Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 6 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 3 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1198 c4) ▸
       at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸ done

  b2 : Chain (Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ []) (Bx4-3012 ∷ CCZ023 ∷ [])
  b2 = at 1 3 (CCZ023 ∷ []) (sym (wl1597 (lit c4))) ▸ done


-- CXcb-box @0413203142: 18 steps
lem-CXcb-box-at0413203142 : Ws → ⟪ (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) (Toff403 ∷ CCZ124 ∷ CX10 ∷ Toff413 ∷ CS12 ∷ CX31 ∷ Toff403 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ124 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ CX10 ∷ Toff413 ∷ []) (wp1403 c4) ▸
       at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 7 2 (Toff403 ∷ CX31 ∷ []) (wp1405 c4) ▸
       at 6 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ CX10 ∷ Toff413 ∷ CS12 ∷ CX31 ∷ Toff403 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ124 ∷ CX10 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff403 ∷ CX31 ∷ []) (wp1405 c4) ▸
       at 4 2 (Toff403 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF403 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 2 2 (Toff403 ∷ CX10 ∷ Toff413 ∷ []) (wp1403 c4) ▸
       at 3 3 (CX10 ∷ []) (wp1406 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸ done

  b2 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ []) (Bx4-3012 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl1599 (lit c4))) ▸ done


-- SWbc-box @0413203142: 11 steps
lem-SWbc-box-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-SWbc-box-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (CX01 ∷ Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0413203142 c4) ▸
       at 3 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸
       at 1 3 (Bx4-3012 ∷ CCZ123 ∷ []) (lem-CXcb-box-at0413203142 c4) ▸
       at 4 2 (CX01 ∷ CCZ023 ∷ []) (wl0560 (lit c4)) ▸
       at 3 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸
       at 2 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸ done

  b1 : Chain (CX01 ∷ Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) (Bx4-3012 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1602 (lit c4)) ▸
       at 0 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0413203142 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done


-- nat-SWbc @0413203142: 23 steps
lem-nat-SWbc-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ Sw01 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 4 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 5 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ Sw01 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Sw01 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 7 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 8 2 (Toff413 ∷ Sw01 ∷ []) (wp0678 c4) ▸
       at 9 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 12 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Sw01 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Sw01 ∷ []) (Bx4-3102 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw01 ∷ []) (wp0676 c4) ▸
       at 14 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 15 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-402 ∷ []) (refl) ▸
       at 5 6 (Bx3-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done


-- sym-bc @0413203142: 2 steps
lem-sym-bc-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-bc-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Bx4-3102 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0413203142 c4)) ▸
       at 0 3 (Bx4-3102 ∷ []) (lem-nat-SWbc-at0413203142 c4) ▸ done


-- sym-ab @0413213042: 18 steps
lem-sym-ab-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-sym-ab-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3102 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 4 1 (Bx4-12 ∷ []) (refl) ▸
       at 7 1 (Bx4-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ [])
  b1 = at 2 6 (Bx1-402 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 7 1 (Bx4-12 ∷ []) (refl) ▸
       at 10 1 (Bx4-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (Bx4-1302 ∷ [])
  b2 = at 5 6 (Bx1-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done


-- box-perm-1342 @0440: 3 steps
lem-box-perm-1342-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-box-perm-1342-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-1302 ∷ [])
  b0 = at 0 1 (Bx4-3012 ∷ []) (lem-pairs-at0440 c4) ▸
       at 0 1 (Bx4-3102 ∷ []) (lem-sym-bc-at0413203142 c4) ▸
       at 0 1 (Bx4-1302 ∷ []) (lem-sym-ab-at0413213042 c4) ▸ done


-- cQ @02142140: 7 steps
lem-cQ-at02142140 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at02142140 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done


-- tP @02142140: 7 steps
lem-tP-at02142140 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at02142140 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at02142140 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸ done


-- VPQ @02142140: 14 steps
lem-VPQ-at02142140 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at02142140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at02142140 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done


-- QVQ @02142140: 3 steps
lem-QVQ-at02142140 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at02142140 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at02142140 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @02142140: 12 steps
lem-box-cP-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at02142140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4130 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at02142140 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at02142140 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done


-- sym-ab @04233042: 18 steps
lem-sym-ab-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-ab-at04233042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1302 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 4 1 (Bx4-32 ∷ []) (refl) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ [])
  b1 = at 2 6 (Bx3-402 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 7 1 (Bx4-32 ∷ []) (refl) ▸
       at 10 1 (Bx4-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (Bx4-3102 ∷ [])
  b2 = at 5 6 (Bx3-402 ∷ []) (refl) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done


-- cQ @0413213042: 7 steps
lem-cQ-at0413213042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸ done


-- box-tQ @0413213042: 13 steps
lem-box-tQ-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3102 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213042 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done


-- CXbc-box @0413213042: 17 steps
lem-CXbc-box-at0413213042 : Ws → ⟪ (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX10 ∷ CCZ124 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213042 c4) ▸
       at 0 2 (Toff413 ∷ CX10 ∷ []) (wp1407 c4) ▸
       at 1 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 3 2 (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1603 (lit c4)) ▸
       at 2 2 (Toff413 ∷ CX10 ∷ []) (wp1407 c4) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX10 ∷ CCZ124 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX10 ∷ []) (Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp1191 c4) ▸
       at 0 4 (Bx4-3102 ∷ []) (sym (lem-box-tQ-at0413213042 c4)) ▸ done

  b2 : Chain (Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ []) (Bx4-3102 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl1599 (lit c4))) ▸ done


-- CXcb-box @0413213042: 18 steps
lem-CXcb-box-at0413213042 : Ws → ⟪ (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) (Toff413 ∷ CCZ024 ∷ CX01 ∷ Toff403 ∷ CS02 ∷ CX30 ∷ Toff413 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ CCZ024 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213042 c4) ▸
       at 0 2 (Toff413 ∷ CX01 ∷ Toff403 ∷ []) (wp1408 c4) ▸
       at 2 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 1 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CX30 ∷ []) (wp1409 c4) ▸
       at 6 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ CX01 ∷ Toff403 ∷ CS02 ∷ CX30 ∷ Toff413 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ CCZ024 ∷ CX01 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff413 ∷ CX30 ∷ []) (wp1409 c4) ▸
       at 4 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 2 2 (Toff413 ∷ CX01 ∷ Toff403 ∷ []) (wp1408 c4) ▸
       at 3 3 (CX01 ∷ []) (wp1410 c4) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ []) (Bx4-3102 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-3102 ∷ []) (sym (lem-box-tQ-at0413213042 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1597 (lit c4))) ▸ done


-- SWbc-box @0413213042: 11 steps
lem-SWbc-box-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (CX10 ∷ Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx4-3102 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0413213042 c4) ▸
       at 3 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸
       at 1 3 (Bx4-3102 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213042 c4) ▸
       at 4 2 (CX10 ∷ CCZ123 ∷ []) (wl0616 (lit c4)) ▸
       at 3 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸
       at 2 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸ done

  b1 : Chain (CX10 ∷ Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) (Bx4-3102 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1604 (lit c4)) ▸
       at 0 3 (Bx4-3102 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0413213042 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @0413213042: 23 steps
lem-nat-SWbc-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ Sw01 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 4 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 5 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ Sw01 ∷ CCZ034 ∷ Bx4-32 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ Sw01 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Sw01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 7 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 8 2 (Toff403 ∷ Sw01 ∷ []) (wp0696 c4) ▸
       at 9 2 (CCZ034 ∷ Sw01 ∷ []) (sym (wp0675 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 11 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 12 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Sw01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ Sw01 ∷ []) (Bx4-3012 ∷ [])
  b2 = at 13 2 (Toff314 ∷ Sw01 ∷ []) (wp0695 c4) ▸
       at 14 2 (CCZ134 ∷ Sw01 ∷ []) (sym (wp0677 c4)) ▸
       at 15 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-412 ∷ []) (refl) ▸
       at 5 6 (Bx3-412 ∷ []) (refl) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- sym-bc @0413213042: 2 steps
lem-sym-bc-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-bc-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0413213042 c4)) ▸
       at 0 3 (Bx4-3012 ∷ []) (lem-nat-SWbc-at0413213042 c4) ▸ done


-- tP @0413203142: 7 steps
lem-tP-at0413203142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203142 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done


-- P-box @0413203142: 8 steps
lem-P-box-at0413203142 : Ws → ⟪ (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-P-box-at0413203142 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203142 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203142 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸ done


-- VPQ @0413203142: 14 steps
lem-VPQ-at0413203142 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done


-- QVQ @0413203142: 3 steps
lem-QVQ-at0413203142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203142 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0413203142 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0413203142: 12 steps
lem-box-cP-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3012 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0413203142 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203142 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done


-- pairs @0413203142: 4 steps
lem-pairs-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-pairs-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) (sym (lem-P-box-at0413203142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0413203142 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸ done


-- box-perm-1423 @04233042: 3 steps
lem-box-perm-1423-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1423-at04233042 c4 = run b0
  where
  b0 : Chain (Bx4-1302 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Bx4-3102 ∷ []) (lem-sym-ab-at04233042 c4) ▸
       at 0 1 (Bx4-3012 ∷ []) (lem-sym-bc-at0413213042 c4) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-pairs-at0413203142 c4) ▸ done


-- box-box-2 @0440: 105 steps
lem-box-box-2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx4-1230 ∷ Bx2-4130 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CX43 ∷ CS03⁻ ∷ CCZ124 ∷ CX43 ∷ CS04 ∷ Toff203 ∷ [])
  b0 = at 0 1 (Bx4-1302 ∷ []) (lem-box-perm-1342-at0440 c4) ▸
       at 0 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233042 c4) ▸
       at 4 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 6 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 10 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 9 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CX43 ∷ CS03⁻ ∷ CCZ124 ∷ CX43 ∷ CS04 ∷ Toff203 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 6 3 (Toff203 ∷ CCZ024 ∷ []) (wp1411 c4) ▸
       at 3 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 3 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ Toff203 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 4 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸
       at 3 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 9 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b3 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ Toff203 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 3 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b4 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff203 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 5 3 (Toff413 ∷ []) (wl1608 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 5 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 11 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸ done

  b5 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff203 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ Bx2-4130 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 9 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 5 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 6 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 2 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸ done

  b6 : Chain (Toff413 ∷ CCZ024 ∷ Bx2-4130 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ Toff203 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 2 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 4 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 8 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 7 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b7 : Chain (Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ Toff203 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff413 ∷ Toff203 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 3 (Toff203 ∷ CCZ024 ∷ []) (wp1411 c4) ▸
       at 1 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 0 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸ done

  b8 : Chain (CCZ124 ∷ Toff413 ∷ Toff203 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 7 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 6 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 3 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 1 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸ done

  b9 : Chain (CCZ124 ∷ Toff203 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

  b10 : Chain (CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ Toff203 ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 3 3 (Toff413 ∷ []) (wl1608 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 3 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 9 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b11 : Chain (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ Toff203 ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx2-4130 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 3 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 0 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 2 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b12 : Chain (Bx2-4130 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx2-4130 ∷ Bx4-1302 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff413 ∷ CCZ013 ∷ []) (wp1412 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 1 4 (Bx4-1302 ∷ []) (sym (lem-box-tQ-at04233042 c4)) ▸ done

  b13 : Chain (Bx2-4130 ∷ Bx4-1302 ∷ []) (Bx2-4130 ∷ Bx4-1230 ∷ [])
  b13 = at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1423-at04233042 c4) ▸ done


-- sym-ab @02142140: 18 steps
lem-sym-ab-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-ab-at02142140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4130 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 4 1 (Bx2-10 ∷ []) (refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ [])
  b1 = at 2 6 (Bx1-230 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸
       at 10 1 (Bx2-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (Bx2-1430 ∷ [])
  b2 = at 5 6 (Bx1-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- box-perm-1423 @02142140: 3 steps
lem-box-perm-1423-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-1423-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-1430 ∷ []) (lem-sym-ab-at02142140 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym-bc-at022440 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-pairs-at02233440 c4) ▸ done


-- CXbc-box @0440: 17 steps
lem-CXbc-box-at0440 : Ws → ⟪ (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX23 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 2 (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1413 c4) ▸
       at 2 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX23 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX23 ∷ []) (Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 4 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸ done

  b2 : Chain (Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done


-- CXcb-box @0440: 18 steps
lem-CXcb-box-at0440 : Ws → ⟪ (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) (Toff412 ∷ CCZ034 ∷ CX32 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ Toff412 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ034 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ CX32 ∷ Toff413 ∷ []) (wl1610 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (sym (wp1414 c4)) ▸
       at 1 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (Toff412 ∷ CS01 ∷ []) (wp1415 c4) ▸
       at 7 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 6 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ CX32 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ Toff412 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ034 ∷ CX32 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 4 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff412 ∷ Toff413 ∷ []) (sym (wl1589 (lit c4))) ▸
       at 2 2 (Toff412 ∷ CX32 ∷ Toff413 ∷ []) (wl1610 (lit c4)) ▸
       at 3 3 (CX32 ∷ []) (wl1612 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-1230 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done


-- SWbc-box @0440: 11 steps
lem-SWbc-box-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-SWbc-box-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (CX23 ∷ Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0440 c4) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 1 3 (Bx4-1230 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0440 c4) ▸
       at 4 2 (CX23 ∷ CCZ012 ∷ []) (wl0411 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (Bx4-1230 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1568 (lit c4)) ▸
       at 0 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @0440: 23 steps
lem-nat-SWbc-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-nat-SWbc-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ Sw23 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (wl1613 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 4 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ Sw23 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ Sw23 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Sw23 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 7 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff413 ∷ Sw23 ∷ []) (wl1613 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 11 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 12 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Sw23 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Sw23 ∷ []) (Bx4-1320 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw23 ∷ []) (wl1614 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 15 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-420 ∷ []) (refl) ▸
       at 5 6 (Bx1-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- sym-bc @0440: 2 steps
lem-sym-bc-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-bc-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-1320 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at0440 c4)) ▸
       at 0 3 (Bx4-1320 ∷ []) (lem-nat-SWbc-at0440 c4) ▸ done


-- sym-ab @04233240: 18 steps
lem-sym-ab-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-ab-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1320 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 4 1 (Bx4-30 ∷ []) (refl) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ [])
  b1 = at 2 6 (Bx3-420 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸
       at 10 1 (Bx4-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (Bx4-3120 ∷ [])
  b2 = at 5 6 (Bx3-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-3120 ∷ []) (refl) ▸ done


-- tP @0413213240: 7 steps
lem-tP-at0413213240 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at0413213240 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213240 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff402 ∷ []) (wp1321 c4) ▸
       at 1 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸ done


-- P-box @0413213240: 8 steps
lem-P-box-at0413213240 : Ws → ⟪ (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-P-box-at0413213240 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213240 c4) ▸
       at 0 2 (Toff413 ∷ Toff402 ∷ []) (sym (lem-tP-at0413213240 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) (sym (wp1416 c4)) ▸
       at 3 2 (Toff413 ∷ Toff402 ∷ []) (sym (lem-tP-at0413213240 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ02 ∷ []) (sym (wp1417 c4)) ▸
       at 2 2 (Toff413 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF413 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp1418 c4)) ▸
       at 0 4 (Bx4-3120 ∷ []) (sym (lem-box-tQ-at0413213240 c4)) ▸ done


-- VPQ @0413213240: 14 steps
lem-VPQ-at0413213240 : Ws → ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0413213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (CS02⁻ ∷ CS13⁻ ∷ S4 ∷ Toff402 ∷ Toff413 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (sym (wl1473 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (sym (wp1322 c4)) ▸
       at 3 2 (CS02⁻ ∷ S4⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S4 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑))) ▸
       at 0 2 (CS02⁻ ∷ CS13⁻ ∷ []) (sym (wl0901 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff402 ∷ Toff413 ∷ []) (lem-tP-at0413213240 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS13⁻ ∷ S4 ∷ Toff402 ∷ Toff413 ∷ S4⁻ ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff402 ∷ CCZ024 ∷ []) (wp1322 c4) ▸
       at 2 4 (Toff413 ∷ CCZ134 ∷ []) (wl1473 (lit c4)) ▸ done


-- QVQ @0413213240: 3 steps
lem-QVQ-at0413213240 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at0413213240 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 1 4 (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at0413213240 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @0413213240: 12 steps
lem-box-cP-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-box-cP-at0413213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3120 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 4 (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-QVQ-at0413213240 c4) ▸
       at 1 2 (Toff402 ∷ Toff413 ∷ []) (lem-tP-at0413213240 c4) ▸
       at 2 2 [] (wl1474 (lit c4)) ▸ done


-- pairs @0413213240: 4 steps
lem-pairs-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-pairs-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) (sym (lem-P-box-at0413213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4) ▸
       at 4 2 [] (wp1323 c4) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done


-- box-perm-2431 @0440: 3 steps
lem-box-perm-2431-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-2431-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Bx4-1320 ∷ []) (lem-sym-bc-at0440 c4) ▸
       at 0 1 (Bx4-3120 ∷ []) (lem-sym-ab-at04233240 c4) ▸
       at 0 1 (Bx4-2031 ∷ []) (lem-pairs-at0413213240 c4) ▸ done


-- CSu-box-3 @04122041: 17 steps
lem-CSu-box-3-at04122041 : Ws → ⟪ (CS34 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS34 ∷ []) ⟫ʷ
lem-CSu-box-3-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34 ∷ Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Toff413 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 2 (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ []) (wl1615 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 7 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff413 ∷ CS34 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Toff413 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1616 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4)) ▸
       at 3 2 (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ []) (wl1615 (lit c4)) ▸
       at 4 6 (CS34 ∷ []) (wl1617 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ []) (Bx4-2031 ∷ CS34 ∷ [])
  b2 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done


-- CSdu-box-3 @04122041: 17 steps
lem-CSdu-box-3-at04122041 : Ws → ⟪ (CS34⁻ ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34⁻ ∷ Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Toff413 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 1 2 (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ []) (wl1618 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 7 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Toff413 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 5 2 (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1616 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4)) ▸
       at 3 2 (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ []) (wl1618 (lit c4)) ▸
       at 4 6 (CS34⁻ ∷ []) (wl1619 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ []) (Bx4-2031 ∷ CS34⁻ ∷ [])
  b2 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

