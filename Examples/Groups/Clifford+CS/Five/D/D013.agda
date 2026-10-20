{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D013 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0456 ; wl0468 ; wl0469 ; wl0901 ; wl1473 ; wl1569 ; wl1570 ; wl1571 ; wl1609 ; wl1611 ; wp0001 ; wp0003 ; wp0021 ; wp0039 ; wp0316 ; wp0375 ; wp0669 ; wp1322 ; wp1399 ; wp1400 ; wp1416 ; wp1417 ; wp1418 ; wl0171 ; wl0270 ; wl0307 ; wl0406 ; wl0516 ; wl1507 ; wl1588 ; wl1661 ; wl1662 ; wl1663 ; wl1664 ; wl1665 ; wp0028 ; wp0075 ; wp0124 ; wp0127 ; wp0155 ; wp0156 ; wp0157 ; wp0167 ; wp0311 ; wp0376 ; wp0454 ; wp0792 ; wp0794 ; wp0795 ; wp1365 ; wp1429 ; wp1430 ; wl0318 ; wl0455 ; wl1677 ; wl1678 ; wp0054 ; wp0120 ; wp0121 ; wp0125 ; wp0213 ; wp0304 ; wp0575 ; wp1003 ; wp1338 ; wp1339 ; wp1340 ; wp1376 ; wp1439 ; wp1440 ; wp1441 ; wp1458 ; wp1459 ; wl0532 ; wl0533 ; wl0323 ; wl0343 ; wl0611 ; wl0626 ; wl0627 ; wl0628 ; wl0766 ; wl0767 ; wl0768 ; wl1249 ; wl1253 ; wl1254 ; wl1255 ; wl1477 ; wl1478 ; wl1726 ; wl1727 ; wl1728 ; wp0038 ; wp0215 ; wp0394 ; wp0451 ; wp0720 ; wp0723 ; wp1206 ; wp1281 ; wp1347 ; wp1470 ; wp1471 ; wp1472 ; wp1473 ; wp1474 ; wp1475 ; wp1489 ; wp1490 ; wp1504 ; wp1505 ; wl1586 ; wl1731 ; wl1732 ; wp0179 ; wp0744 ; wp0747 ; wp0749 ; wp1513 ; wp1514)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143 ; lem-box-tQ-at043043 ; lem-tP-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02132031 ; lem-box-tQ-at022440 ; lem-box-tQ-at03122031 ; lem-box-tQ-at04122041 ; lem-tP-at02132031 ; lem-tP-at022440 ; lem-tP-at03122031 ; lem-tP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-CSdu-box-2-at04203243 ; lem-Su-box-at04203243 ; lem-box-tQ-at0410233142 ; lem-box-tQ-at04122140 ; lem-box-tQ-at0412233140 ; lem-box-tQ-at0413203241 ; lem-box-tQ-at0413213240 ; lem-box-tQ-at04133140 ; lem-tP-at0410233142 ; lem-tP-at04122140 ; lem-tP-at0412233140 ; lem-tP-at0413203241 ; lem-tP-at0413213240 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd12-TOFF403 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CZ03-TOFF412 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS02-CCZ134 ; lem-comm-CS04-CCZ123 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd23-TOFF401 ; lem-comm-CZ03-TOFF214 ; lem-comm-CZ12-TOFF403 ; lem-comm-CZ14-TOFF203 ; lem-comm-CZ14-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-TOFF413 ; lem-comm-CZ02-TOFF413 ; lem-comm-TOFF403-CSd12)

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

-- CSdu-box-2 @04122041: 17 steps
lem-CSdu-box-2-at04122041 : Ws → ⟪ (CS04⁻ ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx4-2031 ∷ []) (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ134 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ Toff402 ∷ CCZ134 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) (wp1470 c4) ▸
       at 3 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 7 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ134 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ Toff402 ∷ CCZ134 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 2 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸
       at 4 2 (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) (wp1459 c4) ▸
       at 3 2 (Toff402 ∷ CS02⁻ ∷ []) (wp1471 c4) ▸
       at 2 2 (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ []) (wp1470 c4) ▸
       at 3 6 (CS04⁻ ∷ []) (wp1472 c4) ▸
       at 3 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸ done

  b2 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CS04⁻ ∷ []) (Bx4-2031 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done

-- Su-box @04122041: 17 steps
lem-Su-box-at04122041 : Ws → ⟪ (S4 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ S4 ∷ []) ⟫ʷ
lem-Su-box-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S4 ∷ Bx4-2031 ∷ []) (Toff402 ∷ S4 ∷ CS02 ∷ CCZ134 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ Toff402 ∷ CCZ134 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) (wp1473 c4) ▸
       at 3 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 7 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ S4 ∷ CS02 ∷ CCZ134 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ Toff402 ∷ CCZ134 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ S4 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 2 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ S4 ∷ []) (sym (wl1249 (lit c4))) ▸
       at 4 2 (Toff402 ∷ CZ02 ∷ CCZ024 ∷ []) (wp1459 c4) ▸
       at 3 2 (Toff402 ∷ CS02 ∷ []) (wp1474 c4) ▸
       at 2 2 (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ []) (wp1473 c4) ▸
       at 3 6 (S4 ∷ []) (wp1475 c4) ▸
       at 3 2 (CCZ134 ∷ S4 ∷ []) (sym (wl1249 (lit c4))) ▸ done

  b2 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ S4 ∷ []) (Bx4-2031 ∷ S4 ∷ [])
  b2 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done

-- P-box @0413203241: 8 steps
lem-P-box-at0413203241 : Ws → ⟪ (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ []) ⟫ʷ
lem-P-box-at0413203241 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) (Bx4-3021 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203241 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203241 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203241 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-3021 ∷ []) (sym (lem-box-tQ-at0413203241 c4)) ▸ done

-- VPQ @0413203241: 14 steps
lem-VPQ-at0413203241 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0413203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done

-- P-box @022440: 8 steps
lem-P-box-at022440 : Ws → ⟪ (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-P-box-at022440 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4) ▸
       at 0 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at022440 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (sym (wl0626 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at022440 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ03 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 2 2 (Toff214 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF214 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0628 (lit c4))) ▸
       at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸ done

-- VPQ @04122140: 14 steps
lem-VPQ-at04122140 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at04122140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at04122140 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done

-- P-box @02132031: 8 steps
lem-P-box-at02132031 : Ws → ⟪ (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-P-box-at02132031 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4) ▸
       at 0 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at02132031 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (sym (lem-tP-at02132031 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ14 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF203 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸ done

-- CSdu-box-2 @0214203143: 17 steps
lem-CSdu-box-2-at0214203143 : Ws → ⟪ (CS02⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Bx2-4013 ∷ []) (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp1489 c4) ▸
       at 3 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 7 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04⁻ ∷ []) (wp0451 c4) ▸
       at 2 2 (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp1489 c4) ▸
       at 3 6 (CS02⁻ ∷ []) (wp1490 c4) ▸
       at 3 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Bx2-4013 ∷ CS02⁻ ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

-- XCSX-box-2 @04203243: 4 steps
lem-XCSX-box-2-at04203243 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04203243 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (Bx4-1023 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at04203243 c4) ▸
       at 0 2 (Bx4-1023 ∷ S4 ∷ []) (lem-Su-box-at04203243 c4) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done

-- CXbc-box @04133140: 17 steps
lem-CXbc-box-at04133140 : Ws → ⟪ (CX21 ∷ Bx4-3210 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx4-3210 ∷ CX21 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX21 ∷ CCZ024 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CCZ014 ∷ CX32 ∷ CS03 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at04133140 c4) ▸
       at 0 2 (Toff423 ∷ CX21 ∷ []) (wl1663 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (sym (wp0720 c4)) ▸
       at 3 2 (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1504 c4) ▸
       at 2 2 (Toff423 ∷ CX21 ∷ []) (wl1663 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX21 ∷ CCZ024 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CCZ014 ∷ CX32 ∷ CS03 ∷ CX21 ∷ []) (Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (sym (wp0720 c4)) ▸
       at 4 3 (CX21 ∷ []) (wp0723 c4) ▸
       at 0 4 (Bx4-3210 ∷ []) (sym (lem-box-tQ-at04133140 c4)) ▸ done

  b2 : Chain (Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ []) (Bx4-3210 ∷ CCZ023 ∷ [])
  b2 = at 1 3 (CCZ023 ∷ []) (sym (wl1478 (lit c4))) ▸ done

-- CXcb-box @04133140: 18 steps
lem-CXcb-box-at04133140 : Ws → ⟪ (CX12 ∷ Bx4-3210 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx4-3210 ∷ CX12 ∷ []) (Toff423 ∷ CCZ014 ∷ CX12 ∷ Toff413 ∷ CS01 ∷ CX31 ∷ Toff423 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ014 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at04133140 c4) ▸
       at 0 2 (Toff423 ∷ CX12 ∷ Toff413 ∷ []) (wl1726 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) (sym (wp1505 c4)) ▸
       at 1 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CS03 ∷ []) (wp1347 c4) ▸
       at 7 2 (Toff423 ∷ CX31 ∷ []) (wl1507 (lit c4)) ▸
       at 6 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ CX12 ∷ Toff413 ∷ CS01 ∷ CX31 ∷ Toff423 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ014 ∷ CX12 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff423 ∷ CX31 ∷ []) (wl1507 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Toff413 ∷ []) (wl1727 (lit c4)) ▸
       at 2 2 (Toff423 ∷ CX12 ∷ Toff413 ∷ []) (wl1726 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl1728 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ013 ∷ []) (wp0394 c4) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b2 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ []) (Bx4-3210 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-3210 ∷ []) (sym (lem-box-tQ-at04133140 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl1477 (lit c4))) ▸ done

-- P-box @03122031: 8 steps
lem-P-box-at03122031 : Ws → ⟪ (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-P-box-at03122031 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03122031 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03122031 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸ done

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
