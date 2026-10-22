{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD189 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D189 (Sᴰ : SD189) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-570a2ddc)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 1 Sᴰ
  lem-F4-I-S2 : Ws → St 1382
  lem-F4-I-S2 = pickᴰ 2 Sᴰ
  lem-F4-I-S3 : Ws → St 1351
  lem-F4-I-S3 = pickᴰ 3 Sᴰ
  lem-F4-K2-I : Ws → St 1573
  lem-F4-K2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 5 Sᴰ
  lem-F4-K2-S2 : Ws → St 1531
  lem-F4-K2-S2 = pickᴰ 6 Sᴰ
  lem-F4-K2-S3 : Ws → St 1731
  lem-F4-K2-S3 = pickᴰ 7 Sᴰ
  lem-F4-S3-I : Ws → St 1353
  lem-F4-S3-I = pickᴰ 8 Sᴰ
  lem-F4-S3-K2 : Ws → St 1354
  lem-F4-S3-K2 = pickᴰ 9 Sᴰ
  lem-F4-S3-S2 : Ws → St 1534
  lem-F4-S3-S2 = pickᴰ 10 Sᴰ
  lem-F4-S3-S3 : Ws → St 1355
  lem-F4-S3-S3 = pickᴰ 11 Sᴰ
  lem-nat-S : Ws → St 1732
  lem-nat-S = pickᴰ 12 Sᴰ
  lem-nat-S-at14213243 : Ws → St 1733
  lem-nat-S-at14213243 = pickᴰ 13 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1630
  lem-F1-order-Iat0 = pickᴰ 14 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1631
  lem-F1-order-Kat2 = pickᴰ 15 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1632
  lem-F1-order-Kat3 = pickᴰ 16 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1633
  lem-F1-order-SKat2 = pickᴰ 17 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1634
  lem-F1-order-SKat3 = pickᴰ 18 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1635
  lem-F1-order-Sat2 = pickᴰ 19 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1636
  lem-F1-order-Sat3 = pickᴰ 20 Sᴰ
  lem-F2-I-K0 : Ws → St 1637
  lem-F2-I-K0 = pickᴰ 21 Sᴰ
  lem-F2-I-K1 : Ws → St 1638
  lem-F2-I-K1 = pickᴰ 22 Sᴰ
  lem-F2-I-K2 : Ws → St 1639
  lem-F2-I-K2 = pickᴰ 23 Sᴰ
  lem-F2-I-K3 : Ws → St 1640
  lem-F2-I-K3 = pickᴰ 24 Sᴰ
  lem-F2-I-S0 : Ws → St 1641
  lem-F2-I-S0 = pickᴰ 25 Sᴰ
  lem-F2-I-S1 : Ws → St 1642
  lem-F2-I-S1 = pickᴰ 26 Sᴰ
  lem-F2-I-S2 : Ws → St 1643
  lem-F2-I-S2 = pickᴰ 27 Sᴰ
  lem-F2-I-S3 : Ws → St 1644
  lem-F2-I-S3 = pickᴰ 28 Sᴰ
  lem-F2-K0-K1 : Ws → St 1645
  lem-F2-K0-K1 = pickᴰ 29 Sᴰ
  lem-F2-K0-K2 : Ws → St 1646
  lem-F2-K0-K2 = pickᴰ 30 Sᴰ
  lem-F2-K0-K3 : Ws → St 1647
  lem-F2-K0-K3 = pickᴰ 31 Sᴰ
  lem-F2-K1-K2 : Ws → St 1648
  lem-F2-K1-K2 = pickᴰ 32 Sᴰ
  lem-F2-K1-K3 : Ws → St 1649
  lem-F2-K1-K3 = pickᴰ 33 Sᴰ
  lem-F2-K2-K3 : Ws → St 1650
  lem-F2-K2-K3 = pickᴰ 34 Sᴰ
  lem-F2-S0-K1 : Ws → St 1651
  lem-F2-S0-K1 = pickᴰ 35 Sᴰ
  lem-F2-S0-K2 : Ws → St 1652
  lem-F2-S0-K2 = pickᴰ 36 Sᴰ
  lem-F2-S0-K3 : Ws → St 1653
  lem-F2-S0-K3 = pickᴰ 37 Sᴰ
  lem-F2-S0-S1 : Ws → St 1654
  lem-F2-S0-S1 = pickᴰ 38 Sᴰ
  lem-F2-S0-S2 : Ws → St 1655
  lem-F2-S0-S2 = pickᴰ 39 Sᴰ
  lem-F2-S0-S3 : Ws → St 1656
  lem-F2-S0-S3 = pickᴰ 40 Sᴰ
  lem-F2-S1-K0 : Ws → St 1657
  lem-F2-S1-K0 = pickᴰ 41 Sᴰ
  lem-F2-S1-K2 : Ws → St 1658
  lem-F2-S1-K2 = pickᴰ 42 Sᴰ
  lem-F2-S1-K3 : Ws → St 1659
  lem-F2-S1-K3 = pickᴰ 43 Sᴰ
  lem-F2-S1-S2 : Ws → St 1660
  lem-F2-S1-S2 = pickᴰ 44 Sᴰ
  lem-F2-S1-S3 : Ws → St 1661
  lem-F2-S1-S3 = pickᴰ 45 Sᴰ
  lem-F2-S2-K0 : Ws → St 1662
  lem-F2-S2-K0 = pickᴰ 46 Sᴰ
  lem-F2-S2-K1 : Ws → St 1663
  lem-F2-S2-K1 = pickᴰ 47 Sᴰ
  lem-F2-S2-K3 : Ws → St 1664
  lem-F2-S2-K3 = pickᴰ 48 Sᴰ
  lem-F2-S2-S3 : Ws → St 1665
  lem-F2-S2-S3 = pickᴰ 49 Sᴰ
  lem-F2-S3-K0 : Ws → St 1666
  lem-F2-S3-K0 = pickᴰ 50 Sᴰ
  lem-F2-S3-K1 : Ws → St 1667
  lem-F2-S3-K1 = pickᴰ 51 Sᴰ
  lem-F2-S3-K2 : Ws → St 1668
  lem-F2-S3-K2 = pickᴰ 52 Sᴰ
  lem-nat-S-at01143043 : Ws → St 1734
  lem-nat-S-at01143043 = pickᴰ 53 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 54 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 55 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 56 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 57 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1393
  lem-F4-CS2-S2 = pickᴰ 58 Sᴰ
  lem-F4-CS2-S3 : Ws → St 1364
  lem-F4-CS2-S3 = pickᴰ 59 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 60 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 61 Sᴰ
  lem-F4-S3-CS2 : Ws → St 1366
  lem-F4-S3-CS2 = pickᴰ 62 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 63 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 64 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 65 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 66 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 67 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 68 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 69 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 70 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 71 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 72 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 73 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 74 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1314
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 75 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 76 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 77 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 78 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 79 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 80 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 81 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 82 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 83 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 84 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 85 Sᴰ
  lem-SW-S : Ws → St 1735
  lem-SW-S = pickᴰ 86 Sᴰ
  lem-SW-S-at01143043 : Ws → St 1736
  lem-SW-S-at01143043 = pickᴰ 87 Sᴰ
  lem-SW-S-at14213243 : Ws → St 1737
  lem-SW-S-at14213243 = pickᴰ 88 Sᴰ
  lem-deb-P-hi-eps : Ws → St 1738
  lem-deb-P-hi-eps = pickᴰ 89 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ []) (lem-SW-S c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ []) (lem-nat-S c4)

-- F0: 3 steps
lem-F0 : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-F0 c4 = derive (Sb3-0-12-4 ∷ []) (Sb4-0-12-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-SW-S-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ []) (lem-nat-S-at14213243 c4)

-- F0 @14213243: 3 steps
lem-F0-at14213243 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = derive (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw03 ∷ Sw03 ∷ []) [] (wl 928 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw03 ∷ []) (lem-SW-S-at01143043 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) (Sb3-1-42-0 ∷ []) (lem-nat-S-at01143043 c4)

-- F0 @01143043: 3 steps
lem-F0-at01143043 : Ws → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at01143043 c4 = derive (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-570a2ddc c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) [] (lem-deb-P-hi-eps c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4)

-- deb-P-hi part0: 248 steps
lem-deb-P-hi-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-hi-part0 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 80 (q13 c4) ∷
   rw 77 (q13 c4) ∷
   rw 74 (q14 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q15 c4) ∷
   rw 62 (q13 c4) ∷
   rw 59 (q16 c4) ∷
   rw 56 (q13 c4) ∷
   rw 53 (q16 c4) ∷
   rw 50 (q13 c4) ∷
   rw 81 (q13 c4) ∷
   rw 78 (q13 c4) ∷
   rw 75 (q14 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q15 c4) ∷
   rw 66 (q15 c4) ∷
   rw 63 (q13 c4) ∷
   rw 60 (q16 c4) ∷
   rw 57 (q13 c4) ∷
   rw 54 (q16 c4) ∷
   rw 51 (q13 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q13 c4) ∷
   rw 76 (q14 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q15 c4) ∷
   rw 64 (q13 c4) ∷
   rw 61 (q16 c4) ∷
   rw 58 (q13 c4) ∷
   rw 55 (q16 c4) ∷
   rw 52 (q13 c4) ∷
   rw 83 (q13 c4) ∷
   rw 80 (q13 c4) ∷
   rw 77 (q14 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q13 c4) ∷
   rw 62 (q16 c4) ∷
   rw 59 (q13 c4) ∷
   rw 56 (q16 c4) ∷
   rw 53 (q13 c4) ∷
   rw 84 (q13 c4) ∷
   rw 81 (q13 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q15 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q15 c4) ∷
   rw 66 (q13 c4) ∷
   rw 63 (q16 c4) ∷
   rw 60 (q13 c4) ∷
   rw 57 (q16 c4) ∷
   rw 54 (q13 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q15 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q13 c4) ∷
   rw 64 (q16 c4) ∷
   rw 61 (q13 c4) ∷
   rw 58 (q16 c4) ∷
   rw 55 (q13 c4) ∷
   rw 86 (q13 c4) ∷
   rw 83 (q13 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q15 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q13 c4) ∷
   rw 65 (q16 c4) ∷
   rw 62 (q13 c4) ∷
   rw 59 (q16 c4) ∷
   rw 56 (q13 c4) ∷
   rw 87 (q17 c4) ∷
   rw 84 (q17 c4) ∷
   rw 81 (q18 c4) ∷
   rw 78 (q19 c4) ∷
   rw 75 (q19 c4) ∷
   rw 72 (q19 c4) ∷
   rw 69 (q17 c4) ∷
   rw 66 (q20 c4) ∷
   rw 63 (q17 c4) ∷
   rw 60 (q20 c4) ∷
   rw 57 (q17 c4) ∷
   rw 88 (q13 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q15 c4) ∷
   rw 76 (q15 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q13 c4) ∷
   rw 67 (q16 c4) ∷
   rw 64 (q13 c4) ∷
   rw 61 (q16 c4) ∷
   rw 58 (q13 c4) ∷
   rw 89 (q17 c4) ∷
   rw 86 (q17 c4) ∷
   rw 83 (q18 c4) ∷
   rw 80 (q19 c4) ∷
   rw 77 (q19 c4) ∷
   rw 74 (q19 c4) ∷
   rw 71 (q17 c4) ∷
   rw 68 (q20 c4) ∷
   rw 65 (q17 c4) ∷
   rw 62 (q20 c4) ∷
   rw 59 (q17 c4) ∷
   rw 90 (q13 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q15 c4) ∷
   rw 78 (q15 c4) ∷
   rw 75 (q15 c4) ∷
   rw 72 (q13 c4) ∷
   rw 69 (q16 c4) ∷
   rw 66 (q13 c4) ∷
   rw 63 (q16 c4) ∷
   rw 60 (q13 c4) ∷
   rw 91 (q21 c4) ∷
   rw 88 (q21 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q23 c4) ∷
   rw 79 (q23 c4) ∷
   rw 76 (q23 c4) ∷
   rw 73 (q21 c4) ∷
   rw 70 (q24 c4) ∷
   rw 67 (q21 c4) ∷
   rw 64 (q24 c4) ∷
   rw 61 (q21 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q21 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q23 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q23 c4) ∷
   rw 74 (q21 c4) ∷
   rw 71 (q24 c4) ∷
   rw 68 (q21 c4) ∷
   rw 65 (q24 c4) ∷
   rw 62 (q21 c4) ∷
   rw 93 (q21 c4) ∷
   rw 90 (q21 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q23 c4) ∷
   rw 81 (q23 c4) ∷
   rw 78 (q23 c4) ∷
   rw 75 (q21 c4) ∷
   rw 72 (q24 c4) ∷
   rw 69 (q21 c4) ∷
   rw 66 (q24 c4) ∷
   rw 63 (q21 c4) ∷
   rw 94 (q25 c4) ∷
   rw 91 (q25 c4) ∷
   rw 88 (q26 c4) ∷
   rw 85 (q27 c4) ∷
   rw 82 (q27 c4) ∷
   rw 79 (q27 c4) ∷
   rw 76 (q25 c4) ∷
   rw 73 (q28 c4) ∷
   rw 70 (q25 c4) ∷
   rw 67 (q28 c4) ∷
   rw 64 (q25 c4) ∷
   rw 95 (q21 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q23 c4) ∷
   rw 83 (q23 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q21 c4) ∷
   rw 74 (q24 c4) ∷
   rw 71 (q21 c4) ∷
   rw 68 (q24 c4) ∷
   rw 65 (q21 c4) ∷
   rw 96 (q29 c4) ∷
   rw 93 (q29 c4) ∷
   rw 90 (q30 c4) ∷
   rw 87 (q31 c4) ∷
   rw 84 (q31 c4) ∷
   rw 81 (q31 c4) ∷
   rw 78 (q29 c4) ∷
   rw 75 (q32 c4) ∷
   rw 72 (q29 c4) ∷
   rw 69 (q32 c4) ∷
   rw 66 (q29 c4) ∷
   rw 97 (q29 c4) ∷
   rw 94 (q29 c4) ∷
   rw 91 (q30 c4) ∷
   rw 88 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q31 c4) ∷
   rw 79 (q29 c4) ∷
   rw 76 (q32 c4) ∷
   rw 73 (q29 c4) ∷
   rw 70 (q32 c4) ∷
   rw 67 (q29 c4) ∷
   rw 98 (q29 c4) ∷
   rw 95 (q29 c4) ∷
   rw 92 (q30 c4) ∷
   rw 89 (q31 c4) ∷
   rw 86 (q31 c4) ∷
   rw 83 (q31 c4) ∷
   rw 80 (q29 c4) ∷
   rw 77 (q32 c4) ∷
   rw 74 (q29 c4) ∷
   rw 71 (q32 c4) ∷
   rw 68 (q29 c4) ∷
   rw 99 (q29 c4) ∷
   rw 96 (q29 c4) ∷
   rw 93 (q30 c4) ∷
   rw 90 (q31 c4) ∷
   rw 87 (q31 c4) ∷
   rw 84 (q31 c4) ∷
   rw 81 (q29 c4) ∷
   rw 78 (q32 c4) ∷
   rw 75 (q29 c4) ∷
   rw 72 (q32 c4) ∷
   rw 69 (q29 c4) ∷
   rw 100 (q29 c4) ∷
   rw 97 (q29 c4) ∷
   rw 94 (q30 c4) ∷
   rw 91 (q31 c4) ∷
   rw 88 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q29 c4) ∷
   rw 79 (q32 c4) ∷
   rw 76 (q29 c4) ∷
   rw 73 (q32 c4) ∷
   rw 70 (q29 c4) ∷
   rw 101 (q29 c4) ∷
   rw 98 (q29 c4) ∷
   rw 95 (q30 c4) ∷
   rw 92 (q31 c4) ∷
   rw 89 (q31 c4) ∷
   rw 86 (q31 c4) ∷
   rw 83 (q29 c4) ∷
   rw 80 (q32 c4) ∷
   rw 77 (q29 c4) ∷
   rw 74 (q32 c4) ∷
   rw 71 (q29 c4) ∷
   rw 102 (q29 c4) ∷
   rw 99 (q29 c4) ∷
   rw 96 (q30 c4) ∷ []) Eq.refl
