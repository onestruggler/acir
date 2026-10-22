{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD151 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D151 (Sᴰ : SD151) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-4726ca8d)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

-- The lemmas of other derivation modules (DSig).
private
  lem-F1-order-Iat0 : Ws → St 1630
  lem-F1-order-Iat0 = pickᴰ 0 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1631
  lem-F1-order-Kat2 = pickᴰ 1 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1632
  lem-F1-order-Kat3 = pickᴰ 2 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1633
  lem-F1-order-SKat2 = pickᴰ 3 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1634
  lem-F1-order-SKat3 = pickᴰ 4 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1635
  lem-F1-order-Sat2 = pickᴰ 5 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1636
  lem-F1-order-Sat3 = pickᴰ 6 Sᴰ
  lem-F2-I-K0 : Ws → St 1637
  lem-F2-I-K0 = pickᴰ 7 Sᴰ
  lem-F2-I-K1 : Ws → St 1638
  lem-F2-I-K1 = pickᴰ 8 Sᴰ
  lem-F2-I-K2 : Ws → St 1639
  lem-F2-I-K2 = pickᴰ 9 Sᴰ
  lem-F2-I-K3 : Ws → St 1640
  lem-F2-I-K3 = pickᴰ 10 Sᴰ
  lem-F2-I-S0 : Ws → St 1641
  lem-F2-I-S0 = pickᴰ 11 Sᴰ
  lem-F2-I-S1 : Ws → St 1642
  lem-F2-I-S1 = pickᴰ 12 Sᴰ
  lem-F2-I-S2 : Ws → St 1643
  lem-F2-I-S2 = pickᴰ 13 Sᴰ
  lem-F2-I-S3 : Ws → St 1644
  lem-F2-I-S3 = pickᴰ 14 Sᴰ
  lem-F2-K0-K1 : Ws → St 1645
  lem-F2-K0-K1 = pickᴰ 15 Sᴰ
  lem-F2-K0-K2 : Ws → St 1646
  lem-F2-K0-K2 = pickᴰ 16 Sᴰ
  lem-F2-K0-K3 : Ws → St 1647
  lem-F2-K0-K3 = pickᴰ 17 Sᴰ
  lem-F2-K1-K2 : Ws → St 1648
  lem-F2-K1-K2 = pickᴰ 18 Sᴰ
  lem-F2-K1-K3 : Ws → St 1649
  lem-F2-K1-K3 = pickᴰ 19 Sᴰ
  lem-F2-K2-K3 : Ws → St 1650
  lem-F2-K2-K3 = pickᴰ 20 Sᴰ
  lem-F2-S0-K1 : Ws → St 1651
  lem-F2-S0-K1 = pickᴰ 21 Sᴰ
  lem-F2-S0-K2 : Ws → St 1652
  lem-F2-S0-K2 = pickᴰ 22 Sᴰ
  lem-F2-S0-K3 : Ws → St 1653
  lem-F2-S0-K3 = pickᴰ 23 Sᴰ
  lem-F2-S0-S1 : Ws → St 1654
  lem-F2-S0-S1 = pickᴰ 24 Sᴰ
  lem-F2-S0-S2 : Ws → St 1655
  lem-F2-S0-S2 = pickᴰ 25 Sᴰ
  lem-F2-S0-S3 : Ws → St 1656
  lem-F2-S0-S3 = pickᴰ 26 Sᴰ
  lem-F2-S1-K0 : Ws → St 1657
  lem-F2-S1-K0 = pickᴰ 27 Sᴰ
  lem-F2-S1-K2 : Ws → St 1658
  lem-F2-S1-K2 = pickᴰ 28 Sᴰ
  lem-F2-S1-K3 : Ws → St 1659
  lem-F2-S1-K3 = pickᴰ 29 Sᴰ
  lem-F2-S1-S2 : Ws → St 1660
  lem-F2-S1-S2 = pickᴰ 30 Sᴰ
  lem-F2-S1-S3 : Ws → St 1661
  lem-F2-S1-S3 = pickᴰ 31 Sᴰ
  lem-F2-S2-K0 : Ws → St 1662
  lem-F2-S2-K0 = pickᴰ 32 Sᴰ
  lem-F2-S2-K1 : Ws → St 1663
  lem-F2-S2-K1 = pickᴰ 33 Sᴰ
  lem-F2-S2-K3 : Ws → St 1664
  lem-F2-S2-K3 = pickᴰ 34 Sᴰ
  lem-F2-S2-S3 : Ws → St 1665
  lem-F2-S2-S3 = pickᴰ 35 Sᴰ
  lem-F2-S3-K0 : Ws → St 1666
  lem-F2-S3-K0 = pickᴰ 36 Sᴰ
  lem-F2-S3-K1 : Ws → St 1667
  lem-F2-S3-K1 = pickᴰ 37 Sᴰ
  lem-F2-S3-K2 : Ws → St 1668
  lem-F2-S3-K2 = pickᴰ 38 Sᴰ
  lem-F4-I-I-at0213243140 : Ws → St 1422
  lem-F4-I-I-at0213243140 = pickᴰ 39 Sᴰ
  lem-F4-I-S2-at0213243140 : Ws → St 1408
  lem-F4-I-S2-at0213243140 = pickᴰ 40 Sᴰ
  lem-F4-I-S3-at0213243140 : Ws → St 1710
  lem-F4-I-S3-at0213243140 = pickᴰ 41 Sᴰ
  lem-F4-K3-I-at0213243140 : Ws → St 1409
  lem-F4-K3-I-at0213243140 = pickᴰ 42 Sᴰ
  lem-F4-K3-S2-at0213243140 : Ws → St 1411
  lem-F4-K3-S2-at0213243140 = pickᴰ 43 Sᴰ
  lem-F4-K3-S3-at0213243140 : Ws → St 1711
  lem-F4-K3-S3-at0213243140 = pickᴰ 44 Sᴰ
  lem-F4-S2-I-at0213243140 : Ws → St 1412
  lem-F4-S2-I-at0213243140 = pickᴰ 45 Sᴰ
  lem-F4-S2-S2-at0213243140 : Ws → St 1414
  lem-F4-S2-S2-at0213243140 = pickᴰ 46 Sᴰ
  lem-F4-S2-S3-at0213243140 : Ws → St 1712
  lem-F4-S2-S3-at0213243140 = pickᴰ 47 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 48 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 49 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 50 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 51 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 52 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 53 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 54 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 55 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 56 Sᴰ
  lem-F4-CS2-I-at0213243140 : Ws → St 1418
  lem-F4-CS2-I-at0213243140 = pickᴰ 57 Sᴰ
  lem-F4-CS2-S2-at0213243140 : Ws → St 1419
  lem-F4-CS2-S2-at0213243140 = pickᴰ 58 Sᴰ
  lem-F4-CS2-S3-at0213243140 : Ws → St 1713
  lem-F4-CS2-S3-at0213243140 = pickᴰ 59 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 60 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 61 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 62 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 63 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 64 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 65 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 66 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 67 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 68 Sᴰ
  lem-deb-CKS-split-b-at0213243140 : Ws → St 1714
  lem-deb-CKS-split-b-at0213243140 = pickᴰ 69 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 70 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 71 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 72 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 73 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 74 Sᴰ
  lem-deb-CKS-split-a-at0213243140 : Ws → St 1715
  lem-deb-CKS-split-a-at0213243140 = pickᴰ 75 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1414 (lem-F4-S2-S2-at0213243140 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1419 (lem-F4-CS2-S2-at0213243140 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1411 (lem-F4-K3-S2-at0213243140 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1408 (lem-F4-I-S2-at0213243140 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1422 (lem-F4-I-I-at0213243140 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1412 (lem-F4-S2-I-at0213243140 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1418 (lem-F4-CS2-I-at0213243140 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1409 (lem-F4-K3-I-at0213243140 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1710 (lem-F4-I-S3-at0213243140 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1712 (lem-F4-S2-S3-at0213243140 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1713 (lem-F4-CS2-S3-at0213243140 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1711 (lem-F4-K3-S3-at0213243140 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1715 (lem-deb-CKS-split-a-at0213243140 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1714 (lem-deb-CKS-split-b-at0213243140 c4)

-- deb-CKS @0213243140 part3: 115 steps
lem-deb-CKS-at0213243140-part3 : Ws → ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ []) ⟫ʷ
lem-deb-CKS-at0213243140-part3 c4 = derive (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ [])
  (rw 141 (q1 c4) ∷
   rw 138 (q1 c4) ∷
   rw 135 (q1 c4) ∷
   rw 132 (q2 c4) ∷
   rw 129 (q3 c4) ∷
   rw 126 (q2 c4) ∷
   rw 123 (q3 c4) ∷
   rw 120 (q2 c4) ∷
   rw 117 (q2 c4) ∷
   rw 114 (q4 c4) ∷
   rw 111 (q1 c4) ∷
   rw 108 (q1 c4) ∷
   rw 105 (q1 c4) ∷
   rw 102 (q2 c4) ∷
   rw 99 (q3 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q3 c4) ∷
   rw 90 (q2 c4) ∷
   rw 145 (q5 c4) ∷
   rw 142 (q6 c4) ∷
   rw 139 (q6 c4) ∷
   rw 136 (q6 c4) ∷
   rw 133 (q7 c4) ∷
   rw 130 (q8 c4) ∷
   rw 127 (q7 c4) ∷
   rw 124 (q8 c4) ∷
   rw 121 (q7 c4) ∷
   rw 118 (q7 c4) ∷
   rw 115 (q5 c4) ∷
   rw 112 (q6 c4) ∷
   rw 109 (q6 c4) ∷
   rw 106 (q6 c4) ∷
   rw 103 (q7 c4) ∷
   rw 100 (q8 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q7 c4) ∷
   rw 146 (q4 c4) ∷
   rw 143 (q1 c4) ∷
   rw 140 (q1 c4) ∷
   rw 137 (q1 c4) ∷
   rw 134 (q2 c4) ∷
   rw 131 (q3 c4) ∷
   rw 128 (q2 c4) ∷
   rw 125 (q3 c4) ∷
   rw 122 (q2 c4) ∷
   rw 119 (q2 c4) ∷
   rw 116 (q4 c4) ∷
   rw 113 (q1 c4) ∷
   rw 110 (q1 c4) ∷
   rw 107 (q1 c4) ∷
   rw 104 (q2 c4) ∷
   rw 101 (q3 c4) ∷
   rw 98 (q2 c4) ∷
   rw 95 (q3 c4) ∷
   rw 92 (q2 c4) ∷
   rw 147 (q9 c4) ∷
   rw 144 (q10 c4) ∷
   rw 141 (q10 c4) ∷
   rw 138 (q10 c4) ∷
   rw 135 (q11 c4) ∷
   rw 132 (q12 c4) ∷
   rw 129 (q11 c4) ∷
   rw 126 (q12 c4) ∷
   rw 123 (q11 c4) ∷
   rw 120 (q11 c4) ∷
   rw 117 (q9 c4) ∷
   rw 114 (q10 c4) ∷
   rw 111 (q10 c4) ∷
   rw 108 (q10 c4) ∷
   rw 105 (q11 c4) ∷
   rw 102 (q12 c4) ∷
   rw 99 (q11 c4) ∷
   rw 96 (q12 c4) ∷
   rw 93 (q11 c4) ∷
   rw 148 (q9 c4) ∷
   rw 145 (q10 c4) ∷
   rw 142 (q10 c4) ∷
   rw 139 (q10 c4) ∷
   rw 136 (q11 c4) ∷
   rw 133 (q12 c4) ∷
   rw 130 (q11 c4) ∷
   rw 127 (q12 c4) ∷
   rw 124 (q11 c4) ∷
   rw 121 (q11 c4) ∷
   rw 118 (q9 c4) ∷
   rw 115 (q10 c4) ∷
   rw 112 (q10 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q12 c4) ∷
   rw 100 (q11 c4) ∷
   rw 97 (q12 c4) ∷
   rw 94 (q11 c4) ∷
   rw 149 (q9 c4) ∷
   rw 146 (q10 c4) ∷
   rw 143 (q10 c4) ∷
   rw 140 (q10 c4) ∷
   rw 137 (q11 c4) ∷
   rw 134 (q12 c4) ∷
   rw 131 (q11 c4) ∷
   rw 128 (q12 c4) ∷
   rw 125 (q11 c4) ∷
   rw 122 (q11 c4) ∷
   rw 119 (q9 c4) ∷
   rw 116 (q10 c4) ∷
   rw 113 (q10 c4) ∷
   rw 110 (q10 c4) ∷
   rw 107 (q11 c4) ∷
   rw 104 (q12 c4) ∷
   rw 101 (q11 c4) ∷
   rw 98 (q12 c4) ∷
   rw 95 (q11 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = wlE 1083 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 6 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q20 : Ws → Eqn
  q20 c4 = wlE 87 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 18 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q26 : Ws → Eqn
  q26 c4 = wlE 3 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q29 : Ws → Eqn
  q29 c4 = wlE 17 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 90 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q32 : Ws → Eqn
  q32 c4 = wlE 13 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-TR2-4726ca8d c4)

-- deb-AD-eps @02132031: 144 steps
lem-deb-AD-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-AD-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q15 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q15 c4) ∷
   rw 6 (q15 c4) ∷
   rw 7 (q15 c4) ∷
   rw 8 (q15 c4) ∷
   rw 9 (q15 c4) ∷
   rw 10 (q15 c4) ∷
   rw 11 (q15 c4) ∷
   rw 12 (q15 c4) ∷
   rw 13 (q15 c4) ∷
   rw 14 (q15 c4) ∷
   rw 15 (q15 c4) ∷
   rw 16 (q15 c4) ∷
   rw 17 (q15 c4) ∷
   rw 18 (q15 c4) ∷
   rw 19 (q15 c4) ∷
   rw 20 (q15 c4) ∷
   rw 21 (q15 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q15 c4) ∷
   rw 24 (q15 c4) ∷
   rw 25 (q15 c4) ∷
   rw 26 (q15 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 24 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 21 (q17 c4) ∷
   rw 20 (q20 c4) ∷
   rw 19 (q17 c4) ∷
   rw 18 (q20 c4) ∷
   rw 17 (q17 c4) ∷
   rw 16 (q19 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q20 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q20 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw 28 (q22 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw 25 (q24 c4) ∷
   rw 24 (q24 c4) ∷
   rw 23 (q24 c4) ∷
   rw 22 (q22 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw 18 (q22 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q24 c4) ∷
   rw 14 (q24 c4) ∷
   rw 13 (q24 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q22 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw 29 (q27 c4) ∷
   rw 28 (q27 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw 26 (q29 c4) ∷
   rw 25 (q29 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q30 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q29 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 16 (q29 c4) ∷
   rw 15 (q29 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q30 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw 30 (q31 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 27 (q32 c4) ∷
   rw 26 (q32 c4) ∷
   rw 25 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q32 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 17 (q32 c4) ∷
   rw 16 (q32 c4) ∷
   rw 15 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl
