{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D214 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0037 ; wl0044 ; wl0045 ; wl0085 ; wl0155 ; wl0171 ; wl0181 ; wl0186 ; wl0191 ; wl0196 ; wl0204 ; wl0230 ; wl0242 ; wl0260 ; wl0263 ; wl0280 ; wl0289 ; wl0302 ; wl0307 ; wl0318 ; wl0323 ; wl0341 ; wl0343 ; wl0406 ; wl0454 ; wl0456 ; wl0467 ; wl0468 ; wl0469 ; wl0470 ; wl0471 ; wl0491 ; wl0492 ; wl0611 ; wl0626 ; wl0627 ; wl0628 ; wl0635 ; wl0636 ; wl0674 ; wl0756 ; wl0766 ; wl0767 ; wl0768 ; wl0788 ; wl0808 ; wl0809 ; wl0829 ; wl0835 ; wl0952 ; wl0965 ; wl0971 ; wl0976 ; wl0978 ; wl1222 ; wl1249 ; wl1253 ; wl1254 ; wl1255 ; wl1263 ; wl1265 ; wl1338 ; wl1350 ; wl1384 ; wl1433 ; wl1441 ; wl1442 ; wl1443 ; wl1477 ; wl1478 ; wl1479 ; wl1480 ; wl1487 ; wl1490 ; wl1494 ; wl1495 ; wl1498 ; wl1499 ; wl1505 ; wl1507 ; wl1510 ; wl1511 ; wl1513 ; wl1545 ; wl1569 ; wl1570 ; wl1571 ; wl1588 ; wl1621 ; wl1625 ; wl1628 ; wl1629 ; wl1630 ; wl1631 ; wl1663 ; wl1717 ; wl1718 ; wl1719 ; wl1720 ; wl1721 ; wl1722 ; wl1723 ; wl1724 ; wl1725 ; wl1726 ; wl1727 ; wl1728 ; wl1729 ; wp0007 ; wp0021 ; wp0028 ; wp0032 ; wp0033 ; wp0037 ; wp0038 ; wp0039 ; wp0054 ; wp0062 ; wp0064 ; wp0075 ; wp0081 ; wp0088 ; wp0089 ; wp0091 ; wp0092 ; wp0155 ; wp0157 ; wp0213 ; wp0215 ; wp0302 ; wp0315 ; wp0316 ; wp0317 ; wp0318 ; wp0320 ; wp0342 ; wp0384 ; wp0394 ; wp0451 ; wp0515 ; wp0516 ; wp0540 ; wp0720 ; wp0722 ; wp0723 ; wp0732 ; wp0789 ; wp0827 ; wp0919 ; wp1003 ; wp1193 ; wp1206 ; wp1281 ; wp1284 ; wp1285 ; wp1293 ; wp1294 ; wp1347 ; wp1391 ; wp1392 ; wp1398 ; wp1402 ; wp1404 ; wp1425 ; wp1426 ; wp1436 ; wp1445 ; wp1449 ; wp1457 ; wp1459 ; wp1467 ; wp1470 ; wp1471 ; wp1472 ; wp1473 ; wp1474 ; wp1475 ; wp1476 ; wp1477 ; wp1478 ; wp1479 ; wp1480 ; wp1481 ; wp1482 ; wp1483 ; wp1484 ; wp1485 ; wp1486 ; wp1487 ; wp1488 ; wp1489 ; wp1490 ; wp1491 ; wp1492 ; wp1493 ; wp1494 ; wp1495 ; wp1496 ; wp1497 ; wp1498 ; wp1499 ; wp1500 ; wp1501 ; wp1502 ; wp1503 ; wp1504 ; wp1505)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-box-tQ-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143 ; lem-box-cP-at022440 ; lem-box-tQ-at022440 ; lem-tP-at022440)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-tQ-at03243240 ; lem-sym-ab-at0314213240 ; lem-sym-ab-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-tQ-at03122031 ; lem-pairs-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D034 using (lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D035 using (lem-box-cP-at02132031 ; lem-box-cP-at03122031 ; lem-box-tQ-at02132031 ; lem-sym-bc-at02132031 ; lem-sym-bc-at02132130 ; lem-sym-bc-at03122130 ; lem-tP-at02132031 ; lem-tP-at03122031)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-sym-bc-at03122031)
open import Examples.Groups.Clifford+CS.Five.D.D040 using (lem-sym-ab-at02132130 ; lem-sym-ab-at022330 ; lem-sym-ab-at03122130 ; lem-sym-ab-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-box-perm-1423-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D078 using (lem-S-sym-xt-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D132 using (lem-ckt-TST)
open import Examples.Groups.Clifford+CS.Five.D.D133 using (lem-box-cP-at04122041 ; lem-box-tQ-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-CSdu-box-3-at0214203143 ; lem-CSu-box-3-at0214203143 ; lem-box-perm-1342-at0214203143 ; lem-sym-ab-at022440 ; lem-sym-ab-at04122041 ; lem-sym-bc-at041041)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-CSdu-box-3-at04122041 ; lem-CSu-box-3-at04122041 ; lem-box-perm-1423-at02142140 ; lem-pairs-at0413213240 ; lem-sym-ab-at02142140 ; lem-sym-ab-at04233240 ; lem-sym-bc-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-Kdu-box-at0214203143 ; lem-Ku-box-at0214203143 ; lem-pairs-at04203243 ; lem-sym-ab-at04122140)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-box-tQ-at04122140 ; lem-cQ-at04122140)
open import Examples.Groups.Clifford+CS.Five.D.D213 using (lem-ckt-TST-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CZ13-CCZ024 ; lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd12-TOFF403 ; lem-comm-CX32-CCZ014 ; lem-comm-CZ12-TOFF403 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CS04-CCZ123 ; lem-comm-CSd02-CCZ134 ; lem-comm-CX30-CCZ124 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ03-TOFF214 ; lem-comm-CZ14-TOFF203 ; lem-comm-CZ14-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ024-CX31)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-TOFF213-CX40)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CS02-TOFF413 ; lem-comm-CSd02-TOFF413 ; lem-comm-CX21-TOFF403 ; lem-comm-SWAP12-BOX⟨4·30⟩ ; lem-comm-TOFF403-CSd12)
-- ckt-B: 3 steps
lem-ckt-B : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
lem-ckt-B c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ [])
  b0 = at 0 97 (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (sym (lem-ckt-TST c4)) ▸
       at 48 1 (Sb2-4-01-3 ∷ []) (lem-S-sym-xt-at14213243 c4) ▸
       at 0 97 (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (lem-ckt-TST-at0440 c4) ▸ done


-- F4-S0-K1 @0440: 1 steps
lem-F4-S0-K1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1293 c4)) ▸ done


-- F4-CS0-K1 @0440: 21 steps
lem-F4-CS0-K1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (sym (wl1441 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1294 c4)) ▸
       at 1 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 4 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 4 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 5 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 2 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 2 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 3 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 4 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸ done

  b2 : Chain (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK01 ∷ X0 ∷ []) (sym (wl1443 (lit c4))) ▸ done


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


-- XCSX-box-2 @04122041: 4 steps
lem-XCSX-box-2-at04122041 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04122041 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (Bx4-2031 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at04122041 c4) ▸
       at 0 2 (Bx4-2031 ∷ S4 ∷ []) (lem-Su-box-at04122041 c4) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done


-- F4-S0-CS2 @0440: 13 steps
lem-F4-S0-CS2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS2-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-XCSX-box-2-at04122041 c4) ▸
       at 1 4 (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1476 c4)) ▸
       at 2 4 (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1477 c4)) ▸
       at 3 4 (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1476 c4)) ▸
       at 4 4 (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1478 c4)) ▸ done

  b1 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done


-- sym-ab @0410233241: 18 steps
lem-sym-ab-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3021 ∷ []) ⟫ʷ
lem-sym-ab-at0410233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0321 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 4 1 (Bx4-31 ∷ []) (refl) ▸
       at 7 1 (Bx4-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ [])
  b1 = at 2 6 (Bx3-421 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (wl0756 (lit c4)) ▸
       at 7 1 (Bx4-31 ∷ []) (refl) ▸
       at 10 1 (Bx4-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (Bx4-3021 ∷ [])
  b2 = at 5 6 (Bx3-421 ∷ []) (refl) ▸
       at 0 6 (Bx4-3021 ∷ []) (refl) ▸ done


-- cQ @0413203241: 7 steps
lem-cQ-at0413203241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 4 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸ done


-- box-tQ @0413203241: 13 steps
lem-box-tQ-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3021 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203241 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done


-- tP @0413203241: 7 steps
lem-tP-at0413203241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203241 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203241 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done


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


-- QVQ @0413203241: 3 steps
lem-QVQ-at0413203241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203241 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0413203241 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0413203241: 12 steps
lem-box-cP-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3021 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0413203241 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203241 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done


-- pairs @0413203241: 4 steps
lem-pairs-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-pairs-at0413203241 c4 = run b0
  where
  b0 : Chain (Bx4-3021 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Toff412 ∷ Bx4-3021 ∷ Toff412 ∷ []) (sym (lem-P-box-at0413203241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0413203241 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 0 4 (Bx4-2130 ∷ []) (sym (lem-box-tQ-at04122140 c4)) ▸ done


-- box-perm-1432 @04122041: 4 steps
lem-box-perm-1432-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Bx4-0231 ∷ []) (lem-sym-ab-at04122041 c4) ▸
       at 0 1 (Bx4-0321 ∷ []) (lem-sym-bc-at041041 c4) ▸
       at 0 1 (Bx4-3021 ∷ []) (lem-sym-ab-at0410233241 c4) ▸
       at 0 1 (Bx4-2130 ∷ []) (lem-pairs-at0413203241 c4) ▸ done


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


-- pairs @022440: 4 steps
lem-pairs-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-pairs-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Toff203 ∷ Bx2-1430 ∷ Toff203 ∷ []) (sym (lem-P-box-at022440 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at022440 c4) ▸
       at 4 2 [] (wl0635 (lit c4)) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸ done


-- box-perm-2341 @02142140: 4 steps
lem-box-perm-2341-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-box-perm-2341-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Bx2-1430 ∷ []) (lem-sym-ab-at02142140 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-pairs-at022440 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4) ▸ done


-- tP @04122140: 7 steps
lem-tP-at04122140 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at04122140 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at04122140 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done


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


-- QVQ @04122140: 3 steps
lem-QVQ-at04122140 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at04122140 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at04122140 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @04122140: 12 steps
lem-box-cP-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at04122140 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at04122140 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at04122140 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done


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


-- pairs @02132031: 4 steps
lem-pairs-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-pairs-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Toff214 ∷ Bx2-3014 ∷ Toff214 ∷ []) (sym (lem-P-box-at02132031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 4 2 [] (wl0636 (lit c4)) ▸
       at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸ done


-- box-perm-4123 @022330: 4 steps
lem-box-perm-4123-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-box-perm-4123-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 1 (Bx2-3104 ∷ []) (lem-sym-ab-at022330 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4) ▸
       at 0 1 (Bx2-1430 ∷ []) (lem-pairs-at02132031 c4) ▸
       at 0 1 (Bx2-4130 ∷ []) (lem-sym-ab-at022440 c4) ▸ done


-- box-box-1 @02142140: 105 steps
lem-box-box-1-at02142140 : Ws → ⟪ (Bx2-4130 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Bx2-4130 ∷ []) ⟫ʷ
lem-box-box-1-at02142140 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-4130 ∷ Bx4-2130 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ124 ∷ CX23 ∷ CS02 ∷ Toff403 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-box-perm-2341-at02142140 c4) ▸
       at 0 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at04122140 c4) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 2 (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1402 c4) ▸
       at 6 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 9 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0260 (lit c4))) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ124 ∷ CX23 ∷ CS02 ∷ Toff403 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 6 3 (Toff403 ∷ CCZ024 ∷ []) (wp1479 c4) ▸
       at 3 4 (Bx4-2130 ∷ []) (sym (lem-box-cP-at04122140 c4)) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at04122140 c4) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ Toff403 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 4 2 (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) (wp1480 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 8 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 7 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS13⁻ ∷ []) (wp1481 c4) ▸
       at 5 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸ done

  b3 : Chain (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ Toff403 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ Toff403 ∷ Toff213 ∷ CCZ134 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff403 ∷ CS13 ∷ []) (wp1482 c4) ▸
       at 3 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b4 : Chain (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ Toff403 ∷ Toff213 ∷ CCZ134 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff403 ∷ K2⁻ ∷ CCZ013 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 5 3 (Toff213 ∷ []) (wl1717 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸
       at 5 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 11 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸ done

  b5 : Chain (Toff213 ∷ CCZ024 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff403 ∷ K2⁻ ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ Bx4-2130 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 9 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS13⁻ ∷ []) (wp1481 c4) ▸
       at 7 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS13 ∷ []) (wp1482 c4) ▸
       at 5 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 6 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 2 4 (Bx4-2130 ∷ []) (sym (lem-box-cP-at04122140 c4)) ▸ done

  b6 : Chain (Toff213 ∷ CCZ024 ∷ Bx4-2130 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff403 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at04122140 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 2 2 (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1402 c4) ▸
       at 4 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 7 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0260 (lit c4))) ▸ done

  b7 : Chain (Toff213 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff403 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff213 ∷ Toff403 ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 3 (Toff403 ∷ CCZ024 ∷ []) (wp1479 c4) ▸
       at 1 4 (Bx4-2130 ∷ []) (sym (lem-box-cP-at04122140 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at04122140 c4) ▸
       at 0 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ []) (wp1480 c4) ▸ done

  b8 : Chain (CCZ124 ∷ Toff213 ∷ Toff403 ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff403 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 7 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 6 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 5 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 4 2 (Toff403 ∷ CS13⁻ ∷ []) (wp1481 c4) ▸
       at 3 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 2 2 (Toff403 ∷ CS13 ∷ []) (wp1482 c4) ▸
       at 1 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸ done

  b9 : Chain (CCZ124 ∷ Toff403 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff403 ∷ Toff213 ∷ CCZ134 ∷ CCZ124 ∷ CCZ013 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

  b10 : Chain (CCZ124 ∷ Toff403 ∷ Toff213 ∷ CCZ134 ∷ CCZ124 ∷ CCZ013 ∷ Toff403 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff403 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 3 3 (Toff213 ∷ []) (wl1717 (lit c4)) ▸
       at 4 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 8 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 7 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸ done

  b11 : Chain (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff403 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx4-2130 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff403 ∷ CS13⁻ ∷ []) (wp1481 c4) ▸
       at 5 2 (Toff403 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF403 (lit c4)) ▸
       at 4 2 (Toff403 ∷ CS13 ∷ []) (wp1482 c4) ▸
       at 3 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 0 4 (Bx4-2130 ∷ []) (sym (lem-box-cP-at04122140 c4)) ▸
       at 2 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b12 : Chain (Bx4-2130 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx4-2130 ∷ Bx2-1304 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 1 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done

  b13 : Chain (Bx4-2130 ∷ Bx2-1304 ∷ []) (Bx4-2130 ∷ Bx2-4130 ∷ [])
  b13 = at 1 1 (Bx2-4130 ∷ []) (lem-box-perm-4123-at022330 c4) ▸ done


-- box-perm-1432 @04122140: 4 steps
lem-box-perm-1432-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-1432-at04122140 c4 = run b0
  where
  b0 : Chain (Bx4-2130 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Bx4-1230 ∷ []) (lem-sym-ab-at04122140 c4) ▸
       at 0 1 (Bx4-1320 ∷ []) (lem-sym-bc-at0440 c4) ▸
       at 0 1 (Bx4-3120 ∷ []) (lem-sym-ab-at04233240 c4) ▸
       at 0 1 (Bx4-2031 ∷ []) (lem-pairs-at0413213240 c4) ▸ done


-- F4-CS0-CS2 @0440: 284 steps
lem-F4-CS0-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb2-4-01-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 5 2 (Bx4-2031 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at04122041 c4) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸ done

  b3 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 4 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 5 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b5 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff401 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (sym (wp1485 c4)) ▸
       at 9 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 8 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 12 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 11 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff413 ∷ CX12 ∷ CS01 ∷ Toff401 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Bx4-2031 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 9 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 7 2 (Toff413 ∷ Toff401 ∷ []) (wp1425 c4) ▸
       at 8 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸ done

  b7 : Chain (X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Bx4-2031 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (Bx4-2031 ∷ CS34 ∷ []) (lem-CSu-box-3-at04122041 c4) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx2-4013 ∷ K3 ∷ CS03 ∷ CCZ024 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 3 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (sym (wl1625 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ Toff413 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff401 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1625 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (sym (wp1485 c4)) ▸
       at 7 2 (Toff413 ∷ Toff401 ∷ Toff301 ∷ []) (wp1484 c4) ▸
       at 6 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff401 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff413 ∷ Toff401 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 9 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (Toff413 ∷ Toff401 ∷ []) (wp1425 c4) ▸
       at 6 3 (CCZ012 ∷ []) (sym (wp1426 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx2-4013 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b11 = at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx2-4130 ∷ []) (lem-box-perm-1342-at0214203143 c4) ▸
       at 2 1 (Bx4-2130 ∷ []) (lem-box-perm-1432-at04122041 c4) ▸
       at 1 2 (Bx4-2130 ∷ Bx2-4130 ∷ []) (lem-box-box-1-at02142140 c4) ▸
       at 1 1 (Bx4-2031 ∷ []) (lem-box-perm-1432-at04122140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-box-perm-1423-at02142140 c4) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X0 ∷ CZ24 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b12 = at 2 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff413 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b13 = at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸ done

  b14 : Chain (Bx4-2031 ∷ X0 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b14 = at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸ done

  b15 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b15 = at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b16 = at 5 3 (Toff213 ∷ CCZ123 ∷ []) (wl0971 (lit c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 3 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (sym (wl1718 (lit c4))) ▸
       at 6 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 5 2 (CS34 ∷ CCZ123 ∷ []) (wl0492 (lit c4)) ▸
       at 6 4 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ []) (sym (wl1719 (lit c4))) ▸
       at 8 2 (CS34⁻ ∷ CCZ123 ∷ []) (wl0491 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ123 ∷ []) (wl1720 (lit c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ X0 ∷ Bx2-4013 ∷ CCZ012 ∷ Toff301 ∷ CS34 ∷ CCZ012 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ123 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Sb2-4-01-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b17 = at 10 2 [] (wl0181 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CCZ012 ∷ []) (wl1265 (lit c4)) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 5 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸ done

  b18 : Chain (Bx4-2031 ∷ X0 ∷ Sb2-4-01-3 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff103 ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b18 = at 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (CS34 ∷ []) (refl) ▸
       at 6 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1486 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸ done

  b19 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff103 ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b19 = at 5 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 8 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b20 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b20 = at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸
       at 3 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 5 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 7 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 7 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b21 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ Toff213 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ Toff213 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b21 = at 8 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 7 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 9 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 11 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 10 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b22 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ Toff213 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ Toff103 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b22 = at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 3 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 5 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 3 4 (CX31 ∷ Toff103 ∷ []) (wp1487 c4) ▸ done

  b23 : Chain (Bx4-2031 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ Toff103 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b23 = at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b24 : Chain (Bx4-2031 ∷ X0 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Sb2-4-01-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b24 = at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 1 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 4 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Sb2-4-01-3 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b25 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 7 2 (CS12 ∷ CS34⁻ ∷ []) (sym (wl1631 (lit c4))) ▸
       at 6 2 (CS12 ∷ Toff301 ∷ []) (sym (wl1384 (lit c4))) ▸
       at 5 2 (CS12 ∷ CS34 ∷ []) (sym (wl1629 (lit c4))) ▸
       at 4 2 (CS12 ∷ Toff301 ∷ []) (sym (wl1384 (lit c4))) ▸
       at 3 2 (CS12 ∷ Bx2-4013 ∷ []) (sym (lem-CSu-box-3-at0214203143 c4)) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 1 (CS34 ∷ []) (refl) ▸
       at 8 1 (CS34⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1486 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 7 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 9 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 7 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 10 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff203 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b28 = at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 10 2 (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff213 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 9 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 8 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 9 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 10 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 11 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 12 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff213 ∷ Toff103 ∷ Toff203 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b30 = at 8 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 9 2 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (sym (wl1721 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 13 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 13 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 15 2 (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4)) ▸ done

  b31 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff103 ∷ Toff203 ∷ Toff203 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ Toff213 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b31 = at 16 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 12 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 5 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 7 3 (Toff103 ∷ []) (wl1621 (lit c4)) ▸
       at 5 4 (CX31 ∷ Toff103 ∷ []) (wp1487 c4) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 1 (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (sym (wl1545 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b32 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff103 ∷ []) (wl1545 (lit c4)) ▸
       at 6 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b33 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CX31 ∷ Toff103 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS12⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 3 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 7 1 (CS34 ∷ []) (refl) ▸
       at 9 1 (CS34⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS12⁻ ∷ X0 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b34 = at 9 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (wl1630 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ Toff301 ∷ []) (sym (wl1722 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CS34 ∷ []) (sym (wl1628 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ Toff301 ∷ []) (sym (wl1722 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ Bx2-4013 ∷ []) (sym (lem-CSdu-box-3-at0214203143 c4)) ▸
       at 8 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ Sb2-4-01-3 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b35 = at 4 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- F4-S0-K2 @0440: 1 steps
lem-F4-S0-K2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1488 c4)) ▸ done


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


-- CKu-box-2 @0214203143: 7 steps
lem-CKu-box-2-at0214203143 : Ws → ⟪ (CK02 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CK02 ∷ []) ⟫ʷ
lem-CKu-box-2-at0214203143 c4 = run b0
  where
  b0 : Chain (CK02 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02 ∷ [])
  b0 = at 0 1 (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ []) (wl1723 (lit c4)) ▸
       at 4 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 3 2 (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4) ▸
       at 2 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 1 2 (Bx2-4013 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2-at0214203143 c4) ▸
       at 1 5 (CK02 ∷ []) (sym (wl1723 (lit c4))) ▸ done


-- F4-CS0-K2 @0440: 20 steps
lem-F4-CS0-K2-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ []) (X0 ∷ Bx2-4013 ∷ K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (sym (wl1487 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 5 4 (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ []) (wp1491 c4) ▸
       at 4 4 (K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ []) (sym (wl1724 (lit c4))) ▸
       at 3 4 (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ []) (wp1492 c4) ▸
       at 2 4 (K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ []) (sym (wl1724 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ Bx2-4013 ∷ K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 1 2 (K2 ∷ Bx2-4013 ∷ []) (sym (lem-Ku-box-at0214203143 c4)) ▸
       at 2 2 (CK02 ∷ Bx2-4013 ∷ []) (sym (lem-CKu-box-2-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 6 2 (S0 ∷ Toff213 ∷ []) (sym (wl1725 (lit c4))) ▸
       at 5 2 (S0 ∷ CCZ024 ∷ []) (wp1493 c4) ▸
       at 4 2 (S0 ∷ Toff213 ∷ []) (sym (wl1725 (lit c4))) ▸
       at 3 2 (S0 ∷ CCZ024 ∷ []) (wp1493 c4) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸ done

  b2 : Chain (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK02 ∷ X0 ∷ []) (sym (wl1490 (lit c4))) ▸ done


-- CSdu-box-2 @04203243: 17 steps
lem-CSdu-box-2-at04203243 : Ws → ⟪ (CS04⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx4-1023 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) (wp1494 c4) ▸
       at 3 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 7 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 4 2 (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) (wp1457 c4) ▸
       at 3 2 (Toff401 ∷ CS01⁻ ∷ []) (wp1495 c4) ▸
       at 2 2 (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) (wp1494 c4) ▸
       at 3 6 (CS04⁻ ∷ []) (wp1496 c4) ▸
       at 3 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CS04⁻ ∷ []) (Bx4-1023 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done


-- Su-box @04203243: 17 steps
lem-Su-box-at04203243 : Ws → ⟪ (S4 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ S4 ∷ []) ⟫ʷ
lem-Su-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S4 ∷ Bx4-1023 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) (wp1497 c4) ▸
       at 3 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 7 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ S4 ∷ CS01 ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ S4 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ S4 ∷ []) (sym (wl1263 (lit c4))) ▸
       at 4 2 (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) (wp1457 c4) ▸
       at 3 2 (Toff401 ∷ CS01 ∷ []) (wp1498 c4) ▸
       at 2 2 (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) (wp1497 c4) ▸
       at 3 6 (S4 ∷ []) (wp1499 c4) ▸
       at 3 2 (CCZ234 ∷ S4 ∷ []) (sym (wl1263 (lit c4))) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ S4 ∷ []) (Bx4-1023 ∷ S4 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done


-- XCSX-box-2 @04203243: 4 steps
lem-XCSX-box-2-at04203243 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04203243 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (Bx4-1023 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at04203243 c4) ▸
       at 0 2 (Bx4-1023 ∷ S4 ∷ []) (lem-Su-box-at04203243 c4) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done


-- F4-S0-CS1 @0440: 13 steps
lem-F4-S0-CS1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS1-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-XCSX-box-2-at04203243 c4) ▸
       at 1 4 (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1500 c4)) ▸
       at 2 4 (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1501 c4)) ▸
       at 3 4 (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1500 c4)) ▸
       at 4 4 (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1502 c4)) ▸ done

  b1 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done


-- sym-ab @0412233140: 18 steps
lem-sym-ab-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-ab-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-2310 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (wp1503 c4) ▸
       at 4 1 (Bx4-30 ∷ []) (refl) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ [])
  b1 = at 2 6 (Bx3-410 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (wp1503 c4) ▸
       at 7 1 (Bx4-30 ∷ []) (refl) ▸
       at 10 1 (Bx4-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (Bx4-3210 ∷ [])
  b2 = at 5 6 (Bx3-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-3210 ∷ []) (refl) ▸ done


-- cQ @04133140: 7 steps
lem-cQ-at04133140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at04133140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸ done


-- box-tQ @04133140: 13 steps
lem-box-tQ-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at04133140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3210 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 0 2 (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl1494 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at04133140 c4) ▸
       at 2 4 (Toff423 ∷ []) (wl1495 (lit c4)) ▸ done


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


-- SWbc-box @04133140: 11 steps
lem-SWbc-box-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-SWbc-box-at04133140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (CX21 ∷ Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx4-3210 ∷ CCZ023 ∷ []) (lem-CXbc-box-at04133140 c4) ▸
       at 3 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸
       at 1 3 (Bx4-3210 ∷ CCZ013 ∷ []) (lem-CXcb-box-at04133140 c4) ▸
       at 4 2 (CX21 ∷ CCZ023 ∷ []) (wl0674 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) (Bx4-3210 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1729 (lit c4)) ▸
       at 0 3 (Bx4-3210 ∷ CCZ023 ∷ []) (lem-CXbc-box-at04133140 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done


-- nat-SWbc @04133140: 23 steps
lem-nat-SWbc-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-nat-SWbc-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ Sw12 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 4 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ Sw12 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Sw12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 7 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 8 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 12 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Sw12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Sw12 ∷ []) (Bx4-3120 ∷ [])
  b2 = at 13 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 15 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-420 ∷ []) (refl) ▸
       at 5 6 (Bx3-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-3120 ∷ []) (refl) ▸ done


-- sym-bc @04133140: 2 steps
lem-sym-bc-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-bc-at04133140 c4 = run b0
  where
  b0 : Chain (Bx4-3210 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at04133140 c4)) ▸
       at 0 3 (Bx4-3120 ∷ []) (lem-nat-SWbc-at04133140 c4) ▸ done


-- box-perm-4132 @04203243: 3 steps
lem-box-perm-4132-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-box-perm-4132-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 1 (Bx4-2310 ∷ []) (lem-pairs-at04203243 c4) ▸
       at 0 1 (Bx4-3210 ∷ []) (lem-sym-ab-at0412233140 c4) ▸
       at 0 1 (Bx4-3120 ∷ []) (lem-sym-bc-at04133140 c4) ▸ done


-- box-perm-2341 @0314213240: 4 steps
lem-box-perm-2341-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-pairs-at03243240 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸ done


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


-- pairs @03122031: 4 steps
lem-pairs-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-pairs-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-2014 ∷ Toff314 ∷ []) (sym (lem-P-box-at03122031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done


-- box-perm-4123 @0330: 4 steps
lem-box-perm-4123-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-4123-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-pairs-at03122031 c4) ▸
       at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸ done

