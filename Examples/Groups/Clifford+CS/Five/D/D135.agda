{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D135 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0155 ; wl0166 ; wl0181 ; wl0204 ; wl0230 ; wl0242 ; wl0256 ; wl0258 ; wl0263 ; wl0271 ; wl0289 ; wl0326 ; wl0341 ; wl0391 ; wl0392 ; wl0393 ; wl0411 ; wl0454 ; wl0456 ; wl0465 ; wl0466 ; wl0467 ; wl0468 ; wl0469 ; wl0470 ; wl0471 ; wl0706 ; wl0831 ; wl0905 ; wl0964 ; wl0965 ; wl0966 ; wl0967 ; wl0968 ; wl0969 ; wl0970 ; wl1020 ; wl1021 ; wl1126 ; wl1220 ; wl1221 ; wl1222 ; wl1270 ; wl1271 ; wl1399 ; wl1433 ; wl1439 ; wl1444 ; wl1445 ; wl1446 ; wl1448 ; wl1449 ; wl1474 ; wl1482 ; wl1483 ; wl1484 ; wl1485 ; wl1486 ; wl1498 ; wl1499 ; wl1505 ; wl1510 ; wl1511 ; wl1513 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1548 ; wl1549 ; wl1550 ; wl1551 ; wl1552 ; wl1553 ; wl1554 ; wl1555 ; wl1556 ; wl1557 ; wl1558 ; wl1559 ; wl1560 ; wl1561 ; wl1562 ; wl1563 ; wl1564 ; wl1565 ; wl1566 ; wl1567 ; wl1568 ; wl1569 ; wl1570 ; wl1571 ; wl1572 ; wl1573 ; wl1574 ; wl1575 ; wl1576 ; wl1577 ; wl1578 ; wl1579 ; wl1580 ; wl1581 ; wl1582 ; wl1583 ; wl1584 ; wl1585 ; wl1586 ; wl1587 ; wl1588 ; wl1589 ; wl1590 ; wl1591 ; wl1592 ; wl1593 ; wl1594 ; wl1595 ; wp0007 ; wp0021 ; wp0032 ; wp0034 ; wp0035 ; wp0036 ; wp0039 ; wp0081 ; wp0082 ; wp0087 ; wp0088 ; wp0089 ; wp0091 ; wp0092 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0123 ; wp0142 ; wp0231 ; wp0261 ; wp0296 ; wp0315 ; wp0316 ; wp0317 ; wp0384 ; wp0516 ; wp0593 ; wp0594 ; wp0596 ; wp0598 ; wp0717 ; wp0718 ; wp0733 ; wp0746 ; wp0749 ; wp0766 ; wp0767 ; wp0986 ; wp0987 ; wp0992 ; wp1003 ; wp1048 ; wp1284 ; wp1285 ; wp1292 ; wp1309 ; wp1310 ; wp1311 ; wp1317 ; wp1373 ; wp1374 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1379 ; wp1380 ; wp1381 ; wp1382 ; wp1383 ; wp1384 ; wp1385 ; wp1386 ; wp1387 ; wp1388 ; wp1389 ; wp1390 ; wp1391 ; wp1392 ; wp1393 ; wp1394 ; wp1395 ; wp1396 ; wp1397 ; wp1398)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at04203243 ; lem-box-cP-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym-bc-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143 ; lem-pairs-at0214203143 ; lem-sym-bc-at02233440)
open import Examples.Groups.Clifford+CS.Five.D.D034 using (lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-box-perm-1423-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-perm-1324-at04122041 ; lem-box-tQ-at04122041 ; lem-tP-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX21-CCZ034 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CSd03-TOFF412 ; lem-comm-CSd12-TOFF403 ; lem-comm-CX02-CCZ134 ; lem-comm-CX31-CCZ024 ; lem-comm-CZ12-TOFF403 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CX03-CCZ124 ; lem-comm-CZ03-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ024-CX31 ; lem-comm-CZ02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ124-CK03 ; lem-comm-CK03-CCZ124 ; lem-comm-CS02-TOFF413 ; lem-comm-CS13-TOFF402 ; lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-CX20-TOFF413 ; lem-comm-CZ13-TOFF402 ; lem-comm-TOFF403-CSd12 ; lem-comm-TOFF413-CX20)
-- F4-CS2-CS2 @0440: 286 steps
lem-F4-CS2-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ024 ∷ CS12⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 8 2 (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4)) ▸
       at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 5 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 12 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 8 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 9 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 8 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 12 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 11 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 10 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 9 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸ done

  b7 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff403 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 9 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 7 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 8 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 4 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 6 2 (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4)) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx4-2031 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ Toff403 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 6 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ Toff413 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b11 = at 7 2 (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4) ▸
       at 6 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 10 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4) ▸
       at 7 2 (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS03 ∷ []) (wp1376 c4) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done

  b12 : Chain (X0 ∷ Bx4-2031 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff403 ∷ Toff413 ∷ CCZ023 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b12 = at 5 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 6 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b15 : Chain (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff413 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 8 (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (sym (wl1548 (lit c4))) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-2031 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b17 = at 3 3 (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4)) ▸
       at 5 2 [] (wl0204 (lit c4)) ▸
       at 4 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸ done

  b18 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b18 = at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1550 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CX34 ∷ CX31 ∷ Toff413 ∷ []) (sym (wl1551 (lit c4))) ▸
       at 7 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 4 2 (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1380 c4) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 7 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸ done

  b19 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ Toff103 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b19 = at 10 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b20 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b20 = at 9 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 3 2 (CX34 ∷ Toff413 ∷ []) (sym (wl1552 (lit c4))) ▸
       at 5 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 4 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 5 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 7 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 8 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸ done

  b21 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ CX34 ∷ CX31 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b21 = at 4 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 5 2 (CX34 ∷ CX31 ∷ Toff413 ∷ []) (sym (wl1551 (lit c4))) ▸
       at 7 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 9 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 8 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 9 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 11 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸ done

  b22 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ CX34 ∷ CX31 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ Toff413 ∷ CS23 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b22 = at 12 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 8 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 9 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wp1382 c4)) ▸
       at 5 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 3 4 (CX31 ∷ Toff103 ∷ []) (wl1553 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b23 : Chain (Bx4-2031 ∷ X0 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CX31 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b23 = at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b24 : Chain (Bx4-2031 ∷ X0 ∷ CX31 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 4 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b25 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1554 (lit c4))) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 6 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff413 ∷ []) (sym (wl1547 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1550 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 7 2 (CX34 ∷ CX31 ∷ Toff413 ∷ []) (sym (wl1551 (lit c4))) ▸
       at 9 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 6 2 (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1380 c4) ▸
       at 8 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 9 2 (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4) ▸
       at 12 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ CCZ024 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b28 = at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CX34 ∷ CCZ023 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ Toff413 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX34 ∷ Toff413 ∷ []) (sym (wl1552 (lit c4))) ▸
       at 7 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 6 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 7 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 9 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ Toff413 ∷ CX31 ∷ Toff403 ∷ CCZ023 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ CX34 ∷ CX31 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b30 = at 7 2 (CX34 ∷ CX31 ∷ Toff413 ∷ []) (sym (wl1551 (lit c4))) ▸
       at 9 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 11 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 10 2 (CS03 ∷ Toff413 ∷ []) (sym (wp1376 c4)) ▸
       at 11 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ Toff413 ∷ []) (sym (wp1375 c4)) ▸
       at 13 2 (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4)) ▸
       at 14 2 (CS23 ∷ Toff413 ∷ []) (sym (wl1546 (lit c4))) ▸ done

  b31 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX34 ∷ CCZ023 ∷ CX34 ∷ CX31 ∷ Toff403 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ Toff413 ∷ Toff103 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b31 = at 10 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸
       at 11 2 (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (sym (wp1379 c4)) ▸
       at 5 3 (CCZ023 ∷ []) (sym (wp1382 c4)) ▸
       at 7 3 (CCZ023 ∷ []) (sym (wp1378 c4)) ▸
       at 5 4 (CX31 ∷ Toff103 ∷ []) (wl1553 (lit c4)) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b32 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸ done

  b33 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ X0 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b34 = at 6 5 (CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1555 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff413 ∷ []) (sym (wl1544 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b35 = at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- F4-K2-I @0440: 1 steps
lem-F4-K2-I-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1556 (lit c4))) ▸ done


-- F4-CS1-I @0440: 15 steps
lem-F4-CS1-I-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-I-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) (X0 ∷ CCZ014 ∷ Toff423 ∷ ι ∷ S0⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S0⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (wl1557 (lit c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 3 (ι ∷ S0⁻ ∷ Toff423 ∷ []) (wl1558 (lit c4)) ▸
       at 3 3 (ι ∷ S0⁻ ∷ CCZ014 ∷ []) (wp1383 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ014 ∷ Toff423 ∷ ι ∷ S0⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b1 = at 2 3 (ι ∷ S0⁻ ∷ Toff423 ∷ []) (wl1558 (lit c4)) ▸
       at 1 3 (ι ∷ S0⁻ ∷ CCZ014 ∷ []) (wp1383 c4) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 0 3 (S0 ∷ X0 ∷ []) (sym (wl1448 (lit c4))) ▸ done


-- F4-I-I @0440: 1 steps
lem-F4-I-I-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1445 (lit c4))) ▸ done


-- F4-K3-I @0440: 1 steps
lem-F4-K3-I-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1559 (lit c4))) ▸ done


-- F4-K3-K2 @0440: 1 steps
lem-F4-K3-K2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1560 (lit c4))) ▸ done


-- box-perm-1324 @04203243: 1 steps
lem-box-perm-1324-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-1324-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4) ▸ done


-- F4-K3-CS1 @0440: 19 steps
lem-F4-K3-CS1-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 1 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸ done

  b1 : Chain (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 4 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 0 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1561 (lit c4))) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done


-- sym-ab @04122041: 18 steps
lem-sym-ab-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-sym-ab-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2031 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (sym (wp1048 c4)) ▸
       at 4 1 (Bx4-01 ∷ []) (refl) ▸
       at 7 1 (Bx4-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ [])
  b1 = at 2 6 (Bx0-431 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (sym (wp1048 c4)) ▸
       at 7 1 (Bx4-01 ∷ []) (refl) ▸
       at 10 1 (Bx4-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (Bx4-0231 ∷ [])
  b2 = at 5 6 (Bx0-431 ∷ []) (refl) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- cQ @041041: 7 steps
lem-cQ-at041041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at041041 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 4 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸ done


-- box-tQ @041041: 13 steps
lem-box-tQ-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at041041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0231 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at041041 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done


-- CXbc-box @041041: 17 steps
lem-CXbc-box-at041041 : Ws → ⟪ (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX23 ∷ CCZ124 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at041041 c4) ▸
       at 0 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 1 2 (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (sym (wl1562 (lit c4))) ▸
       at 3 2 (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1385 c4) ▸
       at 2 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX23 ∷ CCZ124 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX23 ∷ []) (Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (sym (wl1562 (lit c4))) ▸
       at 4 3 (CX23 ∷ []) (wl1563 (lit c4)) ▸
       at 0 4 (Bx4-0231 ∷ []) (sym (lem-box-tQ-at041041 c4)) ▸ done

  b2 : Chain (Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done


-- CXcb-box @041041: 18 steps
lem-CXcb-box-at041041 : Ws → ⟪ (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) (Toff402 ∷ CCZ134 ∷ CX32 ∷ Toff403 ∷ CS13 ∷ CX03 ∷ Toff402 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ134 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at041041 c4) ▸
       at 0 2 (Toff402 ∷ CX32 ∷ Toff403 ∷ []) (wp1386 c4) ▸
       at 2 2 (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (sym (wp1387 c4)) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (Toff402 ∷ CS01 ∷ []) (wp1388 c4) ▸
       at 7 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 6 2 (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ CX32 ∷ Toff403 ∷ CS13 ∷ CX03 ∷ Toff402 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ134 ∷ CX32 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 4 2 (Toff402 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF402 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff403 ∷ []) (sym (wp1389 c4)) ▸
       at 2 2 (Toff402 ∷ CX32 ∷ Toff403 ∷ []) (wp1386 c4) ▸
       at 3 3 (CX32 ∷ []) (wp1390 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 3 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸ done

  b2 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-0231 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-0231 ∷ []) (sym (lem-box-tQ-at041041 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done


-- SWbc-box @041041: 11 steps
lem-SWbc-box-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-SWbc-box-at041041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (CX23 ∷ Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-CXbc-box-at041041 c4) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 1 3 (Bx4-0231 ∷ CCZ013 ∷ []) (lem-CXcb-box-at041041 c4) ▸
       at 4 2 (CX23 ∷ CCZ012 ∷ []) (wl0411 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (Bx4-0231 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1568 (lit c4)) ▸
       at 0 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-CXbc-box-at041041 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @041041: 23 steps
lem-nat-SWbc-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-nat-SWbc-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 4 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-01 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Sw23 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 7 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 9 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 11 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 12 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Sw23 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ Sw23 ∷ []) (Bx4-0321 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 14 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 15 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx0-421 ∷ []) (refl) ▸
       at 5 6 (Bx0-421 ∷ []) (refl) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- sym-bc @041041: 2 steps
lem-sym-bc-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-sym-bc-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at041041 c4)) ▸
       at 0 3 (Bx4-0321 ∷ []) (lem-nat-SWbc-at041041 c4) ▸ done


-- cQ @0410233241: 7 steps
lem-cQ-at0410233241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 4 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸ done


-- box-tQ @0410233241: 13 steps
lem-box-tQ-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0321 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233241 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done


-- tP @0410233241: 7 steps
lem-tP-at0410233241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233241 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233241 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done


-- P-box @0410233241: 8 steps
lem-P-box-at0410233241 : Ws → ⟪ (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-P-box-at0410233241 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0410233241 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233241 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233241 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-0321 ∷ []) (sym (lem-box-tQ-at0410233241 c4)) ▸ done


-- VPQ @0410233241: 14 steps
lem-VPQ-at0410233241 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0410233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done


-- QVQ @0410233241: 3 steps
lem-QVQ-at0410233241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0410233241 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0410233241: 12 steps
lem-box-cP-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0321 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0410233241 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233241 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done


-- cQ @0412213043: 7 steps
lem-cQ-at0412213043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0412213043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸ done


-- box-tQ @0412213043: 13 steps
lem-box-tQ-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0412213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2103 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0412213043 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done


-- pairs @0410233241: 4 steps
lem-pairs-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ []) ⟫ʷ
lem-pairs-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ []) (Bx4-2103 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) (sym (lem-P-box-at0410233241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0410233241 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-2103 ∷ []) (sym (lem-box-tQ-at0412213043 c4)) ▸ done


-- box-perm-1423 @04122041: 3 steps
lem-box-perm-1423-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ []) ⟫ʷ
lem-box-perm-1423-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2103 ∷ [])
  b0 = at 0 1 (Bx4-0231 ∷ []) (lem-sym-ab-at04122041 c4) ▸
       at 0 1 (Bx4-0321 ∷ []) (lem-sym-bc-at041041 c4) ▸
       at 0 1 (Bx4-2103 ∷ []) (lem-pairs-at0410233241 c4) ▸ done


-- tP @0412213043: 7 steps
lem-tP-at0412213043 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0412213043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0412213043 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done


-- VPQ @0412213043: 14 steps
lem-VPQ-at0412213043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0412213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0412213043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done


-- QVQ @0412213043: 3 steps
lem-QVQ-at0412213043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0412213043 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0412213043 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @0412213043: 12 steps
lem-box-cP-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0412213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2103 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at0412213043 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0412213043 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done


-- F4-K3-CS2 @0440: 19 steps
lem-F4-K3-CS2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx4-2103 ∷ []) (lem-box-perm-1423-at04122041 c4) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0412213043 c4) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 1 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸ done

  b1 : Chain (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 4 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 0 4 (Bx4-2103 ∷ []) (sym (lem-box-cP-at0412213043 c4)) ▸
       at 0 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1423-at04122041 c4)) ▸
       at 1 7 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1572 (lit c4))) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- F4-K3-K1 @0440: 1 steps
lem-F4-K3-K1-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1573 (lit c4))) ▸ done


-- F4-CS2-K3 @0440: 21 steps
lem-F4-CS2-K3-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (sym (wl1574 (lit c4))) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1575 (lit c4))) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-box-perm-1423-at04122041 c4) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0412213043 c4) ▸
       at 4 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-2103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 4 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 2 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸
       at 1 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 2 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 4 4 (Bx4-2103 ∷ []) (sym (lem-box-cP-at0412213043 c4)) ▸ done

  b2 : Chain (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-2103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1423-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 0 4 (CK03 ∷ X0 ∷ []) (sym (wl1577 (lit c4))) ▸ done


-- F4-K3-K3 @0440: 1 steps
lem-F4-K3-K3-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1578 (lit c4))) ▸ done


-- F4-I-K3 @0440: 1 steps
lem-F4-I-K3-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1579 (lit c4))) ▸ done


-- F4-K2-K3 @0440: 1 steps
lem-F4-K2-K3-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1580 (lit c4))) ▸ done


-- F4-CS1-K3 @0440: 21 steps
lem-F4-CS1-K3-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-K3-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ []) (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (sym (wl1574 (lit c4))) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK03 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1581 (lit c4))) ▸
       at 1 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 4 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 2 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸
       at 1 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 2 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 4 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done

  b2 : Chain (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 0 4 (CK03 ∷ X0 ∷ []) (sym (wl1577 (lit c4))) ▸ done


-- F4-K1-I @0440: 1 steps
lem-F4-K1-I-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-I-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1449 (lit c4))) ▸ done


-- F4-K1-K3 @0440: 1 steps
lem-F4-K1-K3-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K3-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1582 (lit c4))) ▸ done


-- F4-K1-CS2 @0440: 19 steps
lem-F4-K1-CS2-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 3 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 1 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b1 : Chain (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1394 c4)) ▸
       at 4 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 4 (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1394 c4)) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 0 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 1 7 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1583 (lit c4))) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- F4-K1-K2 @0440: 1 steps
lem-F4-K1-K2-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1584 (lit c4))) ▸ done


-- F4-K1-CS1 @0440: 17 steps
lem-F4-K1-CS1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 4 (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1395 c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 2 4 (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1395 c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1585 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done


-- F4-K1-K1 @0440: 1 steps
lem-F4-K1-K1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1444 (lit c4))) ▸ done


-- F4-K1-CS0 @0440: 19 steps
lem-F4-K1-CS0-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS0-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 1 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b1 : Chain (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1292 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- CSdu-box-3 @0214203143: 17 steps
lem-CSdu-box-3-at0214203143 : Ws → ⟪ (CS12⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12⁻ ∷ Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl0968 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS13⁻ ∷ []) (wl0969 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl0968 (lit c4)) ▸
       at 4 6 (CS12⁻ ∷ []) (wl0970 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ []) (Bx2-4013 ∷ CS12⁻ ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done


-- CSu-box-3 @0214203143: 17 steps
lem-CSu-box-3-at0214203143 : Ws → ⟪ (CS12 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12 ∷ Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 1 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl0964 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS13 ∷ []) (wl0966 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl0964 (lit c4)) ▸
       at 4 6 (CS12 ∷ []) (wl0967 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ []) (Bx2-4013 ∷ CS12 ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done


-- P-box @04122041: 8 steps
lem-P-box-at04122041 : Ws → ⟪ (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-P-box-at04122041 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04122041 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (sym (wl1482 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04122041 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ13 ∷ []) (sym (wl1483 (lit c4))) ▸
       at 2 2 (Toff402 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF402 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1484 (lit c4))) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done


-- cQ @0413213240: 7 steps
lem-cQ-at0413213240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸ done


-- box-tQ @0413213240: 13 steps
lem-box-tQ-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213240 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213240 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done


-- pairs @04122041: 4 steps
lem-pairs-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-pairs-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 1 (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) (sym (lem-P-box-at04122041 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 2 [] (wl1474 (lit c4)) ▸
       at 0 4 (Bx4-3120 ∷ []) (sym (lem-box-tQ-at0413213240 c4)) ▸ done


-- sym-ab @0413213240: 18 steps
lem-sym-ab-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-ab-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-3120 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 4 1 (Bx4-10 ∷ []) (refl) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ [])
  b1 = at 2 6 (Bx1-420 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 7 1 (Bx4-10 ∷ []) (refl) ▸
       at 10 1 (Bx4-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (Bx4-1320 ∷ [])
  b2 = at 5 6 (Bx1-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- cQ @04233240: 7 steps
lem-cQ-at04233240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done


-- box-tQ @04233240: 13 steps
lem-box-tQ-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1320 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233240 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done


-- CXbc-box @04233240: 17 steps
lem-CXbc-box-at04233240 : Ws → ⟪ (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX32 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233240 c4) ▸
       at 0 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 3 2 (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp1396 c4) ▸
       at 2 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX32 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX32 ∷ []) (Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 4 3 (CX32 ∷ []) (wp0718 c4) ▸
       at 0 4 (Bx4-1320 ∷ []) (sym (lem-box-tQ-at04233240 c4)) ▸ done

  b2 : Chain (Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-1320 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done


-- CXcb-box @04233240: 18 steps
lem-CXcb-box-at04233240 : Ws → ⟪ (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) (Toff413 ∷ CCZ024 ∷ CX23 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233240 c4) ▸
       at 0 2 (Toff413 ∷ CX23 ∷ Toff412 ∷ []) (wl1587 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp1397 c4)) ▸
       at 1 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 7 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ CX23 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ CX23 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Toff412 ∷ []) (wl1589 (lit c4)) ▸
       at 2 2 (Toff413 ∷ CX23 ∷ Toff412 ∷ []) (wl1587 (lit c4)) ▸
       at 3 3 (CX23 ∷ []) (wl1590 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-1320 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx4-1320 ∷ []) (sym (lem-box-tQ-at04233240 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done


-- SWbc-box @04233240: 11 steps
lem-SWbc-box-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-SWbc-box-at04233240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (CX32 ∷ Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx4-1320 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04233240 c4) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 1 3 (Bx4-1320 ∷ CCZ012 ∷ []) (lem-CXcb-box-at04233240 c4) ▸
       at 4 2 (CX32 ∷ CCZ013 ∷ []) (wl0706 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (Bx4-1320 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl1591 (lit c4)) ▸
       at 0 3 (Bx4-1320 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04233240 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @04233240: 23 steps
lem-nat-SWbc-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-nat-SWbc-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (wl1593 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 4 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ Sw23 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Sw23 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 7 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 8 2 (Toff412 ∷ Sw23 ∷ []) (wl1593 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw23 ∷ []) (sym (wl1592 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 11 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 12 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Sw23 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ Sw23 ∷ []) (Bx4-1230 ∷ [])
  b2 = at 13 2 (Toff134 ∷ Sw23 ∷ []) (wl1595 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw23 ∷ []) (sym (wl1594 (lit c4))) ▸
       at 15 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-430 ∷ []) (refl) ▸
       at 5 6 (Bx1-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- sym-bc @04233240: 2 steps
lem-sym-bc-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-bc-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at04233240 c4)) ▸
       at 0 3 (Bx4-1230 ∷ []) (lem-nat-SWbc-at04233240 c4) ▸ done


-- box-perm-4132 @04122041: 3 steps
lem-box-perm-4132-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-4132-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Bx4-3120 ∷ []) (lem-pairs-at04122041 c4) ▸
       at 0 1 (Bx4-1320 ∷ []) (lem-sym-ab-at0413213240 c4) ▸
       at 0 1 (Bx4-1230 ∷ []) (lem-sym-bc-at04233240 c4) ▸ done


-- sym-ab @022440: 18 steps
lem-sym-ab-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym-ab-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 4 1 (Bx2-40 ∷ []) (refl) ▸
       at 7 1 (Bx2-40 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ [])
  b1 = at 2 6 (Bx4-230 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 7 1 (Bx2-40 ∷ []) (refl) ▸
       at 10 1 (Bx2-40 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (Bx2-4130 ∷ [])
  b2 = at 5 6 (Bx4-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-4130 ∷ []) (refl) ▸ done


-- box-perm-1342 @0214203143: 3 steps
lem-box-perm-1342-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-box-perm-1342-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-pairs-at0214203143 c4) ▸
       at 0 1 (Bx2-1430 ∷ []) (lem-sym-bc-at02233440 c4) ▸
       at 0 1 (Bx2-4130 ∷ []) (lem-sym-ab-at022440 c4) ▸ done


-- cQ @0440: 7 steps
lem-cQ-at0440 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0440 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done


-- box-tQ @0440: 13 steps
lem-box-tQ-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0440 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0440 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done


-- tP @0440: 7 steps
lem-tP-at0440 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0440 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0440 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done

