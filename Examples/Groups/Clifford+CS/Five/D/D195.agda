{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD195 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D195 (Sᴰ : SD195) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-3bdac6c8 ; lem-TR2-bf3fb9f8)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 1 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 2 Sᴰ
  lem-F4-I-S2 : Ws → St 1382
  lem-F4-I-S2 = pickᴰ 3 Sᴰ
  lem-F4-I-S3 : Ws → St 1351
  lem-F4-I-S3 = pickᴰ 4 Sᴰ
  lem-F4-K2-I : Ws → St 1573
  lem-F4-K2-I = pickᴰ 5 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 6 Sᴰ
  lem-F4-K2-S2 : Ws → St 1531
  lem-F4-K2-S2 = pickᴰ 7 Sᴰ
  lem-F4-K2-S3 : Ws → St 1731
  lem-F4-K2-S3 = pickᴰ 8 Sᴰ
  lem-F4-K3-I : Ws → St 1405
  lem-F4-K3-I = pickᴰ 9 Sᴰ
  lem-F4-K3-K3 : Ws → St 1383
  lem-F4-K3-K3 = pickᴰ 10 Sᴰ
  lem-F4-K3-S2 : Ws → St 1406
  lem-F4-K3-S2 = pickᴰ 11 Sᴰ
  lem-F4-K3-S3 : Ws → St 1532
  lem-F4-K3-S3 = pickᴰ 12 Sᴰ
  lem-F4-S2-I : Ws → St 1384
  lem-F4-S2-I = pickᴰ 13 Sᴰ
  lem-F4-S2-K3 : Ws → St 1385
  lem-F4-S2-K3 = pickᴰ 14 Sᴰ
  lem-F4-S2-S2 : Ws → St 1386
  lem-F4-S2-S2 = pickᴰ 15 Sᴰ
  lem-F4-S2-S3 : Ws → St 1533
  lem-F4-S2-S3 = pickᴰ 16 Sᴰ
  lem-F4-S3-I : Ws → St 1353
  lem-F4-S3-I = pickᴰ 17 Sᴰ
  lem-F4-S3-K2 : Ws → St 1354
  lem-F4-S3-K2 = pickᴰ 18 Sᴰ
  lem-F4-S3-S2 : Ws → St 1534
  lem-F4-S3-S2 = pickᴰ 19 Sᴰ
  lem-F4-S3-S3 : Ws → St 1355
  lem-F4-S3-S3 = pickᴰ 20 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1630
  lem-F1-order-Iat0 = pickᴰ 21 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1631
  lem-F1-order-Kat2 = pickᴰ 22 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1632
  lem-F1-order-Kat3 = pickᴰ 23 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1633
  lem-F1-order-SKat2 = pickᴰ 24 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1634
  lem-F1-order-SKat3 = pickᴰ 25 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1635
  lem-F1-order-Sat2 = pickᴰ 26 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1636
  lem-F1-order-Sat3 = pickᴰ 27 Sᴰ
  lem-F2-I-K0 : Ws → St 1637
  lem-F2-I-K0 = pickᴰ 28 Sᴰ
  lem-F2-I-K1 : Ws → St 1638
  lem-F2-I-K1 = pickᴰ 29 Sᴰ
  lem-F2-I-K2 : Ws → St 1639
  lem-F2-I-K2 = pickᴰ 30 Sᴰ
  lem-F2-I-K3 : Ws → St 1640
  lem-F2-I-K3 = pickᴰ 31 Sᴰ
  lem-F2-I-S0 : Ws → St 1641
  lem-F2-I-S0 = pickᴰ 32 Sᴰ
  lem-F2-I-S1 : Ws → St 1642
  lem-F2-I-S1 = pickᴰ 33 Sᴰ
  lem-F2-I-S2 : Ws → St 1643
  lem-F2-I-S2 = pickᴰ 34 Sᴰ
  lem-F2-I-S3 : Ws → St 1644
  lem-F2-I-S3 = pickᴰ 35 Sᴰ
  lem-F2-K0-K1 : Ws → St 1645
  lem-F2-K0-K1 = pickᴰ 36 Sᴰ
  lem-F2-K0-K2 : Ws → St 1646
  lem-F2-K0-K2 = pickᴰ 37 Sᴰ
  lem-F2-K0-K3 : Ws → St 1647
  lem-F2-K0-K3 = pickᴰ 38 Sᴰ
  lem-F2-K1-K2 : Ws → St 1648
  lem-F2-K1-K2 = pickᴰ 39 Sᴰ
  lem-F2-K1-K3 : Ws → St 1649
  lem-F2-K1-K3 = pickᴰ 40 Sᴰ
  lem-F2-K2-K3 : Ws → St 1650
  lem-F2-K2-K3 = pickᴰ 41 Sᴰ
  lem-F2-S0-K1 : Ws → St 1651
  lem-F2-S0-K1 = pickᴰ 42 Sᴰ
  lem-F2-S0-K2 : Ws → St 1652
  lem-F2-S0-K2 = pickᴰ 43 Sᴰ
  lem-F2-S0-K3 : Ws → St 1653
  lem-F2-S0-K3 = pickᴰ 44 Sᴰ
  lem-F2-S0-S1 : Ws → St 1654
  lem-F2-S0-S1 = pickᴰ 45 Sᴰ
  lem-F2-S0-S2 : Ws → St 1655
  lem-F2-S0-S2 = pickᴰ 46 Sᴰ
  lem-F2-S0-S3 : Ws → St 1656
  lem-F2-S0-S3 = pickᴰ 47 Sᴰ
  lem-F2-S1-K0 : Ws → St 1657
  lem-F2-S1-K0 = pickᴰ 48 Sᴰ
  lem-F2-S1-K2 : Ws → St 1658
  lem-F2-S1-K2 = pickᴰ 49 Sᴰ
  lem-F2-S1-K3 : Ws → St 1659
  lem-F2-S1-K3 = pickᴰ 50 Sᴰ
  lem-F2-S1-S2 : Ws → St 1660
  lem-F2-S1-S2 = pickᴰ 51 Sᴰ
  lem-F2-S1-S3 : Ws → St 1661
  lem-F2-S1-S3 = pickᴰ 52 Sᴰ
  lem-F2-S2-K0 : Ws → St 1662
  lem-F2-S2-K0 = pickᴰ 53 Sᴰ
  lem-F2-S2-K1 : Ws → St 1663
  lem-F2-S2-K1 = pickᴰ 54 Sᴰ
  lem-F2-S2-K3 : Ws → St 1664
  lem-F2-S2-K3 = pickᴰ 55 Sᴰ
  lem-F2-S2-S3 : Ws → St 1665
  lem-F2-S2-S3 = pickᴰ 56 Sᴰ
  lem-F2-S3-K0 : Ws → St 1666
  lem-F2-S3-K0 = pickᴰ 57 Sᴰ
  lem-F2-S3-K1 : Ws → St 1667
  lem-F2-S3-K1 = pickᴰ 58 Sᴰ
  lem-F2-S3-K2 : Ws → St 1668
  lem-F2-S3-K2 = pickᴰ 59 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 60 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 61 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 62 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 63 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1393
  lem-F4-CS2-S2 = pickᴰ 64 Sᴰ
  lem-F4-CS2-S3 : Ws → St 1364
  lem-F4-CS2-S3 = pickᴰ 65 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 66 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 67 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1394
  lem-F4-S2-CS2 = pickᴰ 68 Sᴰ
  lem-F4-S3-CS2 : Ws → St 1366
  lem-F4-S3-CS2 = pickᴰ 69 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 70 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 71 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 72 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 73 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 74 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 75 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 76 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 77 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 78 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 79 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1403
  lem-F4-K3-CS2 = pickᴰ 80 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 81 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 82 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 83 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 84 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 85 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 86 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 87 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 88 Sᴰ
  lem-deb-Q-lo-split-a : Ws → St 1753
  lem-deb-Q-lo-split-a = pickᴰ 89 Sᴰ
  lem-deb-Q-hi-split-a : Ws → St 1754
  lem-deb-Q-hi-split-a = pickᴰ 90 Sᴰ
  lem-deb-Q-hi-split-b : Ws → St 1755
  lem-deb-Q-hi-split-b = pickᴰ 91 Sᴰ
  lem-deb-Q-lo-split-b : Ws → St 1756
  lem-deb-Q-lo-split-b = pickᴰ 92 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 93 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 94 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 95 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 96 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 97 Sᴰ
  lem-deb-Q-hi-eps : Ws → St 1757
  lem-deb-Q-hi-eps = pickᴰ 98 Sᴰ
  lem-deb-Q-lo-eps : Ws → St 1758
  lem-deb-Q-lo-eps = pickᴰ 99 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-3bdac6c8 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1758 (lem-deb-Q-lo-eps c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1230 (lem-F4-I-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1394 (lem-F4-S2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1368 (lem-F4-CS2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1403 (lem-F4-K3-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1208 (lem-F4-I-K3 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1385 (lem-F4-S2-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1402 (lem-F4-CS2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1383 (lem-F4-K3-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1382 (lem-F4-I-S2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1386 (lem-F4-S2-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1393 (lem-F4-CS2-S2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1406 (lem-F4-K3-S2 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1183 (lem-F4-I-I c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1384 (lem-F4-S2-I c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1363 (lem-F4-CS2-I c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1405 (lem-F4-K3-I c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1351 (lem-F4-I-S3 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1533 (lem-F4-S2-S3 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1364 (lem-F4-CS2-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1532 (lem-F4-K3-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1753 (lem-deb-Q-lo-split-a c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1756 (lem-deb-Q-lo-split-b c4)

-- deb-Q-lo: 175 steps
lem-deb-Q-lo : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-Q-lo c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 55 (q3 c4) ∷
   rw 52 (q4 c4) ∷
   rw 49 (q4 c4) ∷
   rw 46 (q4 c4) ∷
   rw 43 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw 37 (q5 c4) ∷
   rw 34 (q6 c4) ∷
   rw 31 (q5 c4) ∷
   rw 56 (q7 c4) ∷
   rw 53 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 47 (q8 c4) ∷
   rw 44 (q9 c4) ∷
   rw 41 (q10 c4) ∷
   rw 38 (q9 c4) ∷
   rw 35 (q10 c4) ∷
   rw 32 (q9 c4) ∷
   rw 57 (q3 c4) ∷
   rw 54 (q4 c4) ∷
   rw 51 (q4 c4) ∷
   rw 48 (q4 c4) ∷
   rw 45 (q5 c4) ∷
   rw 42 (q6 c4) ∷
   rw 39 (q5 c4) ∷
   rw 36 (q6 c4) ∷
   rw 33 (q5 c4) ∷
   rw 58 (q7 c4) ∷
   rw 55 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 49 (q8 c4) ∷
   rw 46 (q9 c4) ∷
   rw 43 (q10 c4) ∷
   rw 40 (q9 c4) ∷
   rw 37 (q10 c4) ∷
   rw 34 (q9 c4) ∷
   rw 59 (q3 c4) ∷
   rw 56 (q4 c4) ∷
   rw 53 (q4 c4) ∷
   rw 50 (q4 c4) ∷
   rw 47 (q5 c4) ∷
   rw 44 (q6 c4) ∷
   rw 41 (q5 c4) ∷
   rw 38 (q6 c4) ∷
   rw 35 (q5 c4) ∷
   rw 60 (q11 c4) ∷
   rw 57 (q12 c4) ∷
   rw 54 (q12 c4) ∷
   rw 51 (q12 c4) ∷
   rw 48 (q13 c4) ∷
   rw 45 (q14 c4) ∷
   rw 42 (q13 c4) ∷
   rw 39 (q14 c4) ∷
   rw 36 (q13 c4) ∷
   rw 61 (q11 c4) ∷
   rw 58 (q12 c4) ∷
   rw 55 (q12 c4) ∷
   rw 52 (q12 c4) ∷
   rw 49 (q13 c4) ∷
   rw 46 (q14 c4) ∷
   rw 43 (q13 c4) ∷
   rw 40 (q14 c4) ∷
   rw 37 (q13 c4) ∷
   rw 62 (q11 c4) ∷
   rw 59 (q12 c4) ∷
   rw 56 (q12 c4) ∷
   rw 53 (q12 c4) ∷
   rw 50 (q13 c4) ∷
   rw 47 (q14 c4) ∷
   rw 44 (q13 c4) ∷
   rw 41 (q14 c4) ∷
   rw 38 (q13 c4) ∷
   rw 63 (q15 c4) ∷
   rw 60 (q16 c4) ∷
   rw 57 (q16 c4) ∷
   rw 54 (q16 c4) ∷
   rw 51 (q17 c4) ∷
   rw 48 (q18 c4) ∷
   rw 45 (q17 c4) ∷
   rw 42 (q18 c4) ∷
   rw 39 (q17 c4) ∷
   rw 64 (q11 c4) ∷
   rw 61 (q12 c4) ∷
   rw 58 (q12 c4) ∷
   rw 55 (q12 c4) ∷
   rw 52 (q13 c4) ∷
   rw 49 (q14 c4) ∷
   rw 46 (q13 c4) ∷
   rw 43 (q14 c4) ∷
   rw 40 (q13 c4) ∷
   rw 65 (q19 c4) ∷
   rw 62 (q20 c4) ∷
   rw 59 (q20 c4) ∷
   rw 56 (q20 c4) ∷
   rw 53 (q21 c4) ∷
   rw 50 (q22 c4) ∷
   rw 47 (q21 c4) ∷
   rw 44 (q22 c4) ∷
   rw 41 (q21 c4) ∷
   rw 66 (q19 c4) ∷
   rw 63 (q20 c4) ∷
   rw 60 (q20 c4) ∷
   rw 57 (q20 c4) ∷
   rw 54 (q21 c4) ∷
   rw 51 (q22 c4) ∷
   rw 48 (q21 c4) ∷
   rw 45 (q22 c4) ∷
   rw 42 (q21 c4) ∷
   rw 67 (q19 c4) ∷
   rw 64 (q20 c4) ∷
   rw 61 (q20 c4) ∷
   rw 58 (q20 c4) ∷
   rw 55 (q21 c4) ∷
   rw 52 (q22 c4) ∷
   rw 49 (q21 c4) ∷
   rw 46 (q22 c4) ∷
   rw 43 (q21 c4) ∷
   rw 68 (q19 c4) ∷
   rw 65 (q20 c4) ∷
   rw 62 (q20 c4) ∷
   rw 59 (q20 c4) ∷
   rw 56 (q21 c4) ∷
   rw 53 (q22 c4) ∷
   rw 50 (q21 c4) ∷
   rw 47 (q22 c4) ∷
   rw 44 (q21 c4) ∷
   rw 69 (q19 c4) ∷
   rw 66 (q20 c4) ∷
   rw 63 (q20 c4) ∷
   rw 60 (q20 c4) ∷
   rw 57 (q21 c4) ∷
   rw 54 (q22 c4) ∷
   rw 51 (q21 c4) ∷
   rw 48 (q22 c4) ∷
   rw 45 (q21 c4) ∷
   rw 70 (q19 c4) ∷
   rw 67 (q20 c4) ∷
   rw 64 (q20 c4) ∷
   rw 61 (q20 c4) ∷
   rw 58 (q21 c4) ∷
   rw 55 (q22 c4) ∷
   rw 52 (q21 c4) ∷
   rw 49 (q22 c4) ∷
   rw 46 (q21 c4) ∷
   rw 71 (q19 c4) ∷
   rw 68 (q20 c4) ∷
   rw 65 (q20 c4) ∷
   rw 62 (q20 c4) ∷
   rw 59 (q21 c4) ∷
   rw 56 (q22 c4) ∷
   rw 53 (q21 c4) ∷
   rw 50 (q22 c4) ∷
   rw 47 (q21 c4) ∷
   rw 72 (q19 c4) ∷
   rw 69 (q20 c4) ∷
   rw 66 (q20 c4) ∷
   rw 63 (q20 c4) ∷
   rw 60 (q21 c4) ∷
   rw 57 (q22 c4) ∷
   rw 54 (q21 c4) ∷
   rw 51 (q22 c4) ∷
   rw 48 (q21 c4) ∷
   rw 73 (q19 c4) ∷
   rw 70 (q20 c4) ∷
   rw 67 (q20 c4) ∷
   rw 64 (q20 c4) ∷
   rw 61 (q21 c4) ∷
   rw 58 (q22 c4) ∷
   rw 55 (q21 c4) ∷
   rw 52 (q22 c4) ∷
   rw 49 (q21 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw⁻ 20 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-bf3fb9f8 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1757 (lem-deb-Q-hi-eps c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1366 (lem-F4-S3-CS2 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1365 (lem-F4-K2-CS2 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1207 (lem-F4-I-K2 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1354 (lem-F4-S3-K2 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1367 (lem-F4-CS2-K2 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1352 (lem-F4-K2-K2 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1355 (lem-F4-S3-S3 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1731 (lem-F4-K2-S3 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1353 (lem-F4-S3-I c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1573 (lem-F4-K2-I c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1534 (lem-F4-S3-S2 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1531 (lem-F4-K2-S2 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1754 (lem-deb-Q-hi-split-a c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1755 (lem-deb-Q-hi-split-b c4)

-- deb-Q-hi: 175 steps
lem-deb-Q-hi : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-Q-hi c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 55 (q3 c4) ∷
   rw 52 (q27 c4) ∷
   rw 49 (q27 c4) ∷
   rw 46 (q27 c4) ∷
   rw 43 (q5 c4) ∷
   rw 40 (q28 c4) ∷
   rw 37 (q5 c4) ∷
   rw 34 (q28 c4) ∷
   rw 31 (q5 c4) ∷
   rw 56 (q29 c4) ∷
   rw 53 (q30 c4) ∷
   rw 50 (q30 c4) ∷
   rw 47 (q30 c4) ∷
   rw 44 (q31 c4) ∷
   rw 41 (q32 c4) ∷
   rw 38 (q31 c4) ∷
   rw 35 (q32 c4) ∷
   rw 32 (q31 c4) ∷
   rw 57 (q3 c4) ∷
   rw 54 (q27 c4) ∷
   rw 51 (q27 c4) ∷
   rw 48 (q27 c4) ∷
   rw 45 (q5 c4) ∷
   rw 42 (q28 c4) ∷
   rw 39 (q5 c4) ∷
   rw 36 (q28 c4) ∷
   rw 33 (q5 c4) ∷
   rw 58 (q29 c4) ∷
   rw 55 (q30 c4) ∷
   rw 52 (q30 c4) ∷
   rw 49 (q30 c4) ∷
   rw 46 (q31 c4) ∷
   rw 43 (q32 c4) ∷
   rw 40 (q31 c4) ∷
   rw 37 (q32 c4) ∷
   rw 34 (q31 c4) ∷
   rw 59 (q3 c4) ∷
   rw 56 (q27 c4) ∷
   rw 53 (q27 c4) ∷
   rw 50 (q27 c4) ∷
   rw 47 (q5 c4) ∷
   rw 44 (q28 c4) ∷
   rw 41 (q5 c4) ∷
   rw 38 (q28 c4) ∷
   rw 35 (q5 c4) ∷
   rw 60 (q19 c4) ∷
   rw 57 (q33 c4) ∷
   rw 54 (q33 c4) ∷
   rw 51 (q33 c4) ∷
   rw 48 (q21 c4) ∷
   rw 45 (q34 c4) ∷
   rw 42 (q21 c4) ∷
   rw 39 (q34 c4) ∷
   rw 36 (q21 c4) ∷
   rw 61 (q19 c4) ∷
   rw 58 (q33 c4) ∷
   rw 55 (q33 c4) ∷
   rw 52 (q33 c4) ∷
   rw 49 (q21 c4) ∷
   rw 46 (q34 c4) ∷
   rw 43 (q21 c4) ∷
   rw 40 (q34 c4) ∷
   rw 37 (q21 c4) ∷
   rw 62 (q19 c4) ∷
   rw 59 (q33 c4) ∷
   rw 56 (q33 c4) ∷
   rw 53 (q33 c4) ∷
   rw 50 (q21 c4) ∷
   rw 47 (q34 c4) ∷
   rw 44 (q21 c4) ∷
   rw 41 (q34 c4) ∷
   rw 38 (q21 c4) ∷
   rw 63 (q15 c4) ∷
   rw 60 (q35 c4) ∷
   rw 57 (q35 c4) ∷
   rw 54 (q35 c4) ∷
   rw 51 (q17 c4) ∷
   rw 48 (q36 c4) ∷
   rw 45 (q17 c4) ∷
   rw 42 (q36 c4) ∷
   rw 39 (q17 c4) ∷
   rw 64 (q19 c4) ∷
   rw 61 (q33 c4) ∷
   rw 58 (q33 c4) ∷
   rw 55 (q33 c4) ∷
   rw 52 (q21 c4) ∷
   rw 49 (q34 c4) ∷
   rw 46 (q21 c4) ∷
   rw 43 (q34 c4) ∷
   rw 40 (q21 c4) ∷
   rw 65 (q11 c4) ∷
   rw 62 (q37 c4) ∷
   rw 59 (q37 c4) ∷
   rw 56 (q37 c4) ∷
   rw 53 (q13 c4) ∷
   rw 50 (q38 c4) ∷
   rw 47 (q13 c4) ∷
   rw 44 (q38 c4) ∷
   rw 41 (q13 c4) ∷
   rw 66 (q11 c4) ∷
   rw 63 (q37 c4) ∷
   rw 60 (q37 c4) ∷
   rw 57 (q37 c4) ∷
   rw 54 (q13 c4) ∷
   rw 51 (q38 c4) ∷
   rw 48 (q13 c4) ∷
   rw 45 (q38 c4) ∷
   rw 42 (q13 c4) ∷
   rw 67 (q11 c4) ∷
   rw 64 (q37 c4) ∷
   rw 61 (q37 c4) ∷
   rw 58 (q37 c4) ∷
   rw 55 (q13 c4) ∷
   rw 52 (q38 c4) ∷
   rw 49 (q13 c4) ∷
   rw 46 (q38 c4) ∷
   rw 43 (q13 c4) ∷
   rw 68 (q11 c4) ∷
   rw 65 (q37 c4) ∷
   rw 62 (q37 c4) ∷
   rw 59 (q37 c4) ∷
   rw 56 (q13 c4) ∷
   rw 53 (q38 c4) ∷
   rw 50 (q13 c4) ∷
   rw 47 (q38 c4) ∷
   rw 44 (q13 c4) ∷
   rw 69 (q11 c4) ∷
   rw 66 (q37 c4) ∷
   rw 63 (q37 c4) ∷
   rw 60 (q37 c4) ∷
   rw 57 (q13 c4) ∷
   rw 54 (q38 c4) ∷
   rw 51 (q13 c4) ∷
   rw 48 (q38 c4) ∷
   rw 45 (q13 c4) ∷
   rw 70 (q11 c4) ∷
   rw 67 (q37 c4) ∷
   rw 64 (q37 c4) ∷
   rw 61 (q37 c4) ∷
   rw 58 (q13 c4) ∷
   rw 55 (q38 c4) ∷
   rw 52 (q13 c4) ∷
   rw 49 (q38 c4) ∷
   rw 46 (q13 c4) ∷
   rw 71 (q11 c4) ∷
   rw 68 (q37 c4) ∷
   rw 65 (q37 c4) ∷
   rw 62 (q37 c4) ∷
   rw 59 (q13 c4) ∷
   rw 56 (q38 c4) ∷
   rw 53 (q13 c4) ∷
   rw 50 (q38 c4) ∷
   rw 47 (q13 c4) ∷
   rw 72 (q11 c4) ∷
   rw 69 (q37 c4) ∷
   rw 66 (q37 c4) ∷
   rw 63 (q37 c4) ∷
   rw 60 (q13 c4) ∷
   rw 57 (q38 c4) ∷
   rw 54 (q13 c4) ∷
   rw 51 (q38 c4) ∷
   rw 48 (q13 c4) ∷
   rw 73 (q11 c4) ∷
   rw 70 (q37 c4) ∷
   rw 67 (q37 c4) ∷
   rw 64 (q37 c4) ∷
   rw 61 (q13 c4) ∷
   rw 58 (q38 c4) ∷
   rw 55 (q13 c4) ∷
   rw 52 (q38 c4) ∷
   rw 49 (q13 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 20 (q40 c4) ∷ []) Eq.refl
