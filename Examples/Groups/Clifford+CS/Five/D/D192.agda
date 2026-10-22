{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD192 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D192 (Sᴰ : SD192) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-6ab04641)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 1 Sᴰ
  lem-F4-I-S2 : Ws → St 1382
  lem-F4-I-S2 = pickᴰ 2 Sᴰ
  lem-F4-I-S3 : Ws → St 1351
  lem-F4-I-S3 = pickᴰ 3 Sᴰ
  lem-F4-K3-I : Ws → St 1405
  lem-F4-K3-I = pickᴰ 4 Sᴰ
  lem-F4-K3-K3 : Ws → St 1383
  lem-F4-K3-K3 = pickᴰ 5 Sᴰ
  lem-F4-K3-S2 : Ws → St 1406
  lem-F4-K3-S2 = pickᴰ 6 Sᴰ
  lem-F4-K3-S3 : Ws → St 1532
  lem-F4-K3-S3 = pickᴰ 7 Sᴰ
  lem-F4-S2-I : Ws → St 1384
  lem-F4-S2-I = pickᴰ 8 Sᴰ
  lem-F4-S2-K3 : Ws → St 1385
  lem-F4-S2-K3 = pickᴰ 9 Sᴰ
  lem-F4-S2-S2 : Ws → St 1386
  lem-F4-S2-S2 = pickᴰ 10 Sᴰ
  lem-F4-S2-S3 : Ws → St 1533
  lem-F4-S2-S3 = pickᴰ 11 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1630
  lem-F1-order-Iat0 = pickᴰ 12 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1631
  lem-F1-order-Kat2 = pickᴰ 13 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1632
  lem-F1-order-Kat3 = pickᴰ 14 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1633
  lem-F1-order-SKat2 = pickᴰ 15 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1634
  lem-F1-order-SKat3 = pickᴰ 16 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1635
  lem-F1-order-Sat2 = pickᴰ 17 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1636
  lem-F1-order-Sat3 = pickᴰ 18 Sᴰ
  lem-F2-I-K0 : Ws → St 1637
  lem-F2-I-K0 = pickᴰ 19 Sᴰ
  lem-F2-I-K1 : Ws → St 1638
  lem-F2-I-K1 = pickᴰ 20 Sᴰ
  lem-F2-I-K2 : Ws → St 1639
  lem-F2-I-K2 = pickᴰ 21 Sᴰ
  lem-F2-I-K3 : Ws → St 1640
  lem-F2-I-K3 = pickᴰ 22 Sᴰ
  lem-F2-I-S0 : Ws → St 1641
  lem-F2-I-S0 = pickᴰ 23 Sᴰ
  lem-F2-I-S1 : Ws → St 1642
  lem-F2-I-S1 = pickᴰ 24 Sᴰ
  lem-F2-I-S2 : Ws → St 1643
  lem-F2-I-S2 = pickᴰ 25 Sᴰ
  lem-F2-I-S3 : Ws → St 1644
  lem-F2-I-S3 = pickᴰ 26 Sᴰ
  lem-F2-K0-K1 : Ws → St 1645
  lem-F2-K0-K1 = pickᴰ 27 Sᴰ
  lem-F2-K0-K2 : Ws → St 1646
  lem-F2-K0-K2 = pickᴰ 28 Sᴰ
  lem-F2-K0-K3 : Ws → St 1647
  lem-F2-K0-K3 = pickᴰ 29 Sᴰ
  lem-F2-K1-K2 : Ws → St 1648
  lem-F2-K1-K2 = pickᴰ 30 Sᴰ
  lem-F2-K1-K3 : Ws → St 1649
  lem-F2-K1-K3 = pickᴰ 31 Sᴰ
  lem-F2-K2-K3 : Ws → St 1650
  lem-F2-K2-K3 = pickᴰ 32 Sᴰ
  lem-F2-S0-K1 : Ws → St 1651
  lem-F2-S0-K1 = pickᴰ 33 Sᴰ
  lem-F2-S0-K2 : Ws → St 1652
  lem-F2-S0-K2 = pickᴰ 34 Sᴰ
  lem-F2-S0-K3 : Ws → St 1653
  lem-F2-S0-K3 = pickᴰ 35 Sᴰ
  lem-F2-S0-S1 : Ws → St 1654
  lem-F2-S0-S1 = pickᴰ 36 Sᴰ
  lem-F2-S0-S2 : Ws → St 1655
  lem-F2-S0-S2 = pickᴰ 37 Sᴰ
  lem-F2-S0-S3 : Ws → St 1656
  lem-F2-S0-S3 = pickᴰ 38 Sᴰ
  lem-F2-S1-K0 : Ws → St 1657
  lem-F2-S1-K0 = pickᴰ 39 Sᴰ
  lem-F2-S1-K2 : Ws → St 1658
  lem-F2-S1-K2 = pickᴰ 40 Sᴰ
  lem-F2-S1-K3 : Ws → St 1659
  lem-F2-S1-K3 = pickᴰ 41 Sᴰ
  lem-F2-S1-S2 : Ws → St 1660
  lem-F2-S1-S2 = pickᴰ 42 Sᴰ
  lem-F2-S1-S3 : Ws → St 1661
  lem-F2-S1-S3 = pickᴰ 43 Sᴰ
  lem-F2-S2-K0 : Ws → St 1662
  lem-F2-S2-K0 = pickᴰ 44 Sᴰ
  lem-F2-S2-K1 : Ws → St 1663
  lem-F2-S2-K1 = pickᴰ 45 Sᴰ
  lem-F2-S2-K3 : Ws → St 1664
  lem-F2-S2-K3 = pickᴰ 46 Sᴰ
  lem-F2-S2-S3 : Ws → St 1665
  lem-F2-S2-S3 = pickᴰ 47 Sᴰ
  lem-F2-S3-K0 : Ws → St 1666
  lem-F2-S3-K0 = pickᴰ 48 Sᴰ
  lem-F2-S3-K1 : Ws → St 1667
  lem-F2-S3-K1 = pickᴰ 49 Sᴰ
  lem-F2-S3-K2 : Ws → St 1668
  lem-F2-S3-K2 = pickᴰ 50 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 51 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 52 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 53 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 54 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1393
  lem-F4-CS2-S2 = pickᴰ 55 Sᴰ
  lem-F4-CS2-S3 : Ws → St 1364
  lem-F4-CS2-S3 = pickᴰ 56 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 57 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1394
  lem-F4-S2-CS2 = pickᴰ 58 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 59 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 60 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 61 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 62 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 63 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 64 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 65 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 66 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 67 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1403
  lem-F4-K3-CS2 = pickᴰ 68 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 69 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 70 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 71 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1314
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 72 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 73 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 74 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 75 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 76 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 77 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 78 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 79 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 80 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 81 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 82 Sᴰ
  lem-deb-P-lo-eps : Ws → St 1748
  lem-deb-P-lo-eps = pickᴰ 83 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-6ab04641 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1314 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1748 (lem-deb-P-lo-eps c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1368 (lem-F4-CS2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1230 (lem-F4-I-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1394 (lem-F4-S2-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1403 (lem-F4-K3-CS2 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1402 (lem-F4-CS2-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1208 (lem-F4-I-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1385 (lem-F4-S2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1383 (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1393 (lem-F4-CS2-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1382 (lem-F4-I-S2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1386 (lem-F4-S2-S2 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1406 (lem-F4-K3-S2 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1363 (lem-F4-CS2-I c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1183 (lem-F4-I-I c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1384 (lem-F4-S2-I c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1405 (lem-F4-K3-I c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1364 (lem-F4-CS2-S3 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1351 (lem-F4-I-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1533 (lem-F4-S2-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1532 (lem-F4-K3-S3 c4)

-- deb-P-lo part0: 248 steps
lem-deb-P-lo-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-lo-part0 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q5 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q6 c4) ∷
   rw 65 (q6 c4) ∷
   rw 62 (q4 c4) ∷
   rw 59 (q7 c4) ∷
   rw 56 (q4 c4) ∷
   rw 53 (q7 c4) ∷
   rw 50 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q4 c4) ∷
   rw 75 (q5 c4) ∷
   rw 72 (q6 c4) ∷
   rw 69 (q6 c4) ∷
   rw 66 (q6 c4) ∷
   rw 63 (q4 c4) ∷
   rw 60 (q7 c4) ∷
   rw 57 (q4 c4) ∷
   rw 54 (q7 c4) ∷
   rw 51 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q4 c4) ∷
   rw 76 (q5 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q6 c4) ∷
   rw 67 (q6 c4) ∷
   rw 64 (q4 c4) ∷
   rw 61 (q7 c4) ∷
   rw 58 (q4 c4) ∷
   rw 55 (q7 c4) ∷
   rw 52 (q4 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q5 c4) ∷
   rw 74 (q6 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q6 c4) ∷
   rw 65 (q4 c4) ∷
   rw 62 (q7 c4) ∷
   rw 59 (q4 c4) ∷
   rw 56 (q7 c4) ∷
   rw 53 (q4 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q5 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q6 c4) ∷
   rw 69 (q6 c4) ∷
   rw 66 (q4 c4) ∷
   rw 63 (q7 c4) ∷
   rw 60 (q4 c4) ∷
   rw 57 (q7 c4) ∷
   rw 54 (q4 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q5 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q6 c4) ∷
   rw 67 (q4 c4) ∷
   rw 64 (q7 c4) ∷
   rw 61 (q4 c4) ∷
   rw 58 (q7 c4) ∷
   rw 55 (q4 c4) ∷
   rw 86 (q4 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q5 c4) ∷
   rw 77 (q6 c4) ∷
   rw 74 (q6 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q4 c4) ∷
   rw 65 (q7 c4) ∷
   rw 62 (q4 c4) ∷
   rw 59 (q7 c4) ∷
   rw 56 (q4 c4) ∷
   rw 87 (q8 c4) ∷
   rw 84 (q8 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q10 c4) ∷
   rw 75 (q10 c4) ∷
   rw 72 (q10 c4) ∷
   rw 69 (q8 c4) ∷
   rw 66 (q11 c4) ∷
   rw 63 (q8 c4) ∷
   rw 60 (q11 c4) ∷
   rw 57 (q8 c4) ∷
   rw 88 (q4 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q5 c4) ∷
   rw 79 (q6 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q4 c4) ∷
   rw 67 (q7 c4) ∷
   rw 64 (q4 c4) ∷
   rw 61 (q7 c4) ∷
   rw 58 (q4 c4) ∷
   rw 89 (q8 c4) ∷
   rw 86 (q8 c4) ∷
   rw 83 (q9 c4) ∷
   rw 80 (q10 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q10 c4) ∷
   rw 71 (q8 c4) ∷
   rw 68 (q11 c4) ∷
   rw 65 (q8 c4) ∷
   rw 62 (q11 c4) ∷
   rw 59 (q8 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q5 c4) ∷
   rw 81 (q6 c4) ∷
   rw 78 (q6 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q4 c4) ∷
   rw 69 (q7 c4) ∷
   rw 66 (q4 c4) ∷
   rw 63 (q7 c4) ∷
   rw 60 (q4 c4) ∷
   rw 91 (q12 c4) ∷
   rw 88 (q12 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q14 c4) ∷
   rw 73 (q12 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q12 c4) ∷
   rw 64 (q15 c4) ∷
   rw 61 (q12 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q12 c4) ∷
   rw 86 (q13 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q14 c4) ∷
   rw 74 (q12 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q12 c4) ∷
   rw 65 (q15 c4) ∷
   rw 62 (q12 c4) ∷
   rw 93 (q12 c4) ∷
   rw 90 (q12 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q14 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q12 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q12 c4) ∷
   rw 66 (q15 c4) ∷
   rw 63 (q12 c4) ∷
   rw 94 (q16 c4) ∷
   rw 91 (q16 c4) ∷
   rw 88 (q17 c4) ∷
   rw 85 (q18 c4) ∷
   rw 82 (q18 c4) ∷
   rw 79 (q18 c4) ∷
   rw 76 (q16 c4) ∷
   rw 73 (q19 c4) ∷
   rw 70 (q16 c4) ∷
   rw 67 (q19 c4) ∷
   rw 64 (q16 c4) ∷
   rw 95 (q12 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q13 c4) ∷
   rw 86 (q14 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q12 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q12 c4) ∷
   rw 96 (q20 c4) ∷
   rw 93 (q20 c4) ∷
   rw 90 (q21 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q22 c4) ∷
   rw 81 (q22 c4) ∷
   rw 78 (q20 c4) ∷
   rw 75 (q23 c4) ∷
   rw 72 (q20 c4) ∷
   rw 69 (q23 c4) ∷
   rw 66 (q20 c4) ∷
   rw 97 (q20 c4) ∷
   rw 94 (q20 c4) ∷
   rw 91 (q21 c4) ∷
   rw 88 (q22 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q22 c4) ∷
   rw 79 (q20 c4) ∷
   rw 76 (q23 c4) ∷
   rw 73 (q20 c4) ∷
   rw 70 (q23 c4) ∷
   rw 67 (q20 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q20 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q22 c4) ∷
   rw 80 (q20 c4) ∷
   rw 77 (q23 c4) ∷
   rw 74 (q20 c4) ∷
   rw 71 (q23 c4) ∷
   rw 68 (q20 c4) ∷
   rw 99 (q20 c4) ∷
   rw 96 (q20 c4) ∷
   rw 93 (q21 c4) ∷
   rw 90 (q22 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q22 c4) ∷
   rw 81 (q20 c4) ∷
   rw 78 (q23 c4) ∷
   rw 75 (q20 c4) ∷
   rw 72 (q23 c4) ∷
   rw 69 (q20 c4) ∷
   rw 100 (q20 c4) ∷
   rw 97 (q20 c4) ∷
   rw 94 (q21 c4) ∷
   rw 91 (q22 c4) ∷
   rw 88 (q22 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q20 c4) ∷
   rw 79 (q23 c4) ∷
   rw 76 (q20 c4) ∷
   rw 73 (q23 c4) ∷
   rw 70 (q20 c4) ∷
   rw 101 (q20 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q21 c4) ∷
   rw 92 (q22 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q20 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q20 c4) ∷
   rw 74 (q23 c4) ∷
   rw 71 (q20 c4) ∷
   rw 102 (q20 c4) ∷
   rw 99 (q20 c4) ∷
   rw 96 (q21 c4) ∷ []) Eq.refl
