{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD148 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D148 (Sᴰ : SD148) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-4726ca8d ; lem-TR2-11f6930f ; lem-TR2-fed8f7c9)
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
  lem-F4-I-S3-at02132031 : Ws → St 1357
  lem-F4-I-S3-at02132031 = pickᴰ 39 Sᴰ
  lem-F4-I-S3-at132132 : Ws → St 1388
  lem-F4-I-S3-at132132 = pickᴰ 40 Sᴰ
  lem-F4-K3-S3-at02132031 : Ws → St 1702
  lem-F4-K3-S3-at02132031 = pickᴰ 41 Sᴰ
  lem-F4-K3-S3-at132132 : Ws → St 1703
  lem-F4-K3-S3-at132132 = pickᴰ 42 Sᴰ
  lem-F4-S2-S3-at02132031 : Ws → St 1704
  lem-F4-S2-S3-at02132031 = pickᴰ 43 Sᴰ
  lem-F4-S2-S3-at132132 : Ws → St 1705
  lem-F4-S2-S3-at132132 = pickᴰ 44 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 45 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 46 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 47 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 48 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 49 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 50 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 51 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 52 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 53 Sᴰ
  lem-F4-CS2-S3-at02132031 : Ws → St 1373
  lem-F4-CS2-S3-at02132031 = pickᴰ 54 Sᴰ
  lem-F4-CS2-S3-at132132 : Ws → St 1398
  lem-F4-CS2-S3-at132132 = pickᴰ 55 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 56 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 57 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 58 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 59 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 60 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 61 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 62 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 63 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 64 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 65 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 66 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 67 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 68 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 69 Sᴰ
  lem-deb-P-lo-split-a-at02132031 : Ws → St 1706
  lem-deb-P-lo-split-a-at02132031 = pickᴰ 70 Sᴰ
  lem-deb-P-lo-split-a-at132132 : Ws → St 1707
  lem-deb-P-lo-split-a-at132132 = pickᴰ 71 Sᴰ
  lem-deb-P-lo-split-b-at02132031 : Ws → St 1708
  lem-deb-P-lo-split-b-at02132031 = pickᴰ 72 Sᴰ
  lem-deb-P-lo-split-b-at132132 : Ws → St 1709
  lem-deb-P-lo-split-b-at132132 = pickᴰ 73 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S3-at02132031 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S3-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) (lem-deb-P-lo-split-a-at02132031 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (lem-deb-P-lo-split-b-at02132031 c4)

-- deb-P-lo @02132031 part1: 100 steps
lem-deb-P-lo-at02132031-part1 : Ws → ⟪ (CK41 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-lo-at02132031-part1 c4 = derive (CK41 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 93 (q1 c4) ∷
   rw 90 (q2 c4) ∷
   rw 87 (q3 c4) ∷
   rw 84 (q3 c4) ∷
   rw 81 (q3 c4) ∷
   rw 78 (q1 c4) ∷
   rw 75 (q4 c4) ∷
   rw 72 (q1 c4) ∷
   rw 69 (q4 c4) ∷
   rw 66 (q1 c4) ∷
   rw 97 (q1 c4) ∷
   rw 94 (q1 c4) ∷
   rw 91 (q2 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q3 c4) ∷
   rw 82 (q3 c4) ∷
   rw 79 (q1 c4) ∷
   rw 76 (q4 c4) ∷
   rw 73 (q1 c4) ∷
   rw 70 (q4 c4) ∷
   rw 67 (q1 c4) ∷
   rw 98 (q1 c4) ∷
   rw 95 (q1 c4) ∷
   rw 92 (q2 c4) ∷
   rw 89 (q3 c4) ∷
   rw 86 (q3 c4) ∷
   rw 83 (q3 c4) ∷
   rw 80 (q1 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q1 c4) ∷
   rw 71 (q4 c4) ∷
   rw 68 (q1 c4) ∷
   rw 99 (q1 c4) ∷
   rw 96 (q1 c4) ∷
   rw 93 (q2 c4) ∷
   rw 90 (q3 c4) ∷
   rw 87 (q3 c4) ∷
   rw 84 (q3 c4) ∷
   rw 81 (q1 c4) ∷
   rw 78 (q4 c4) ∷
   rw 75 (q1 c4) ∷
   rw 72 (q4 c4) ∷
   rw 69 (q1 c4) ∷
   rw 100 (q1 c4) ∷
   rw 97 (q1 c4) ∷
   rw 94 (q2 c4) ∷
   rw 91 (q3 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q3 c4) ∷
   rw 82 (q1 c4) ∷
   rw 79 (q4 c4) ∷
   rw 76 (q1 c4) ∷
   rw 73 (q4 c4) ∷
   rw 70 (q1 c4) ∷
   rw 101 (q1 c4) ∷
   rw 98 (q1 c4) ∷
   rw 95 (q2 c4) ∷
   rw 92 (q3 c4) ∷
   rw 89 (q3 c4) ∷
   rw 86 (q3 c4) ∷
   rw 83 (q1 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q1 c4) ∷
   rw 74 (q4 c4) ∷
   rw 71 (q1 c4) ∷
   rw 102 (q1 c4) ∷
   rw 99 (q1 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q3 c4) ∷
   rw 90 (q3 c4) ∷
   rw 87 (q3 c4) ∷
   rw 84 (q1 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q1 c4) ∷
   rw 75 (q4 c4) ∷
   rw 72 (q1 c4) ∷
   rw 103 (q1 c4) ∷
   rw 100 (q1 c4) ∷
   rw 97 (q2 c4) ∷
   rw 94 (q3 c4) ∷
   rw 91 (q3 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q1 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q1 c4) ∷
   rw 76 (q4 c4) ∷
   rw 73 (q1 c4) ∷
   rw 104 (q1 c4) ∷
   rw 101 (q1 c4) ∷
   rw 98 (q2 c4) ∷
   rw 95 (q3 c4) ∷
   rw 92 (q3 c4) ∷
   rw 89 (q3 c4) ∷
   rw 86 (q1 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q1 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q1 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 27 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl 1083 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q11 : Ws → Eqn
  q11 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-TR2-4726ca8d c4)

-- deb-P-lo-eps @132132: 86 steps
lem-deb-P-lo-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) []
  (rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q7 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q7 c4) ∷
   rw 26 (q7 c4) ∷
   rw 27 (q7 c4) ∷
   rw⁻ 28 (q8 c4) ∷
   rw 27 (q9 c4) ∷
   rw 26 (q9 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw 24 (q11 c4) ∷
   rw 23 (q11 c4) ∷
   rw 22 (q11 c4) ∷
   rw 21 (q9 c4) ∷
   rw 20 (q12 c4) ∷
   rw 19 (q9 c4) ∷
   rw 18 (q12 c4) ∷
   rw 17 (q9 c4) ∷
   rw 16 (q11 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 13 (q11 c4) ∷
   rw 12 (q11 c4) ∷
   rw 11 (q9 c4) ∷
   rw 10 (q12 c4) ∷
   rw 9 (q9 c4) ∷
   rw 8 (q12 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q9 c4) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q9 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 29 (q13 c4) ∷
   rw 28 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 26 (q15 c4) ∷
   rw 25 (q16 c4) ∷
   rw 24 (q16 c4) ∷
   rw 23 (q16 c4) ∷
   rw 22 (q14 c4) ∷
   rw⁻ 21 (q17 c4) ∷
   rw 20 (q14 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 18 (q14 c4) ∷
   rw 17 (q16 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 15 (q16 c4) ∷
   rw 14 (q16 c4) ∷
   rw 13 (q16 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-S3-at132132 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at132132 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K3-S3-at132132 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at132132 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) (lem-deb-P-lo-split-a-at132132 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-deb-P-lo-split-b-at132132 c4)

-- deb-P-lo @132132 part1: 64 steps
lem-deb-P-lo-at132132-part1 : Ws → ⟪ (CK42 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-lo-at132132-part1 c4 = derive (CK42 ∷ CCZ124 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 87 (q19 c4) ∷
   rw 84 (q19 c4) ∷
   rw 81 (q20 c4) ∷
   rw 78 (q21 c4) ∷
   rw 75 (q20 c4) ∷
   rw 72 (q21 c4) ∷
   rw 69 (q20 c4) ∷
   rw 100 (q20 c4) ∷
   rw 97 (q20 c4) ∷
   rw 94 (q22 c4) ∷
   rw 91 (q19 c4) ∷
   rw 88 (q19 c4) ∷
   rw 85 (q19 c4) ∷
   rw 82 (q20 c4) ∷
   rw 79 (q21 c4) ∷
   rw 76 (q20 c4) ∷
   rw 73 (q21 c4) ∷
   rw 70 (q20 c4) ∷
   rw 101 (q20 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q22 c4) ∷
   rw 92 (q19 c4) ∷
   rw 89 (q19 c4) ∷
   rw 86 (q19 c4) ∷
   rw 83 (q20 c4) ∷
   rw 80 (q21 c4) ∷
   rw 77 (q20 c4) ∷
   rw 74 (q21 c4) ∷
   rw 71 (q20 c4) ∷
   rw 102 (q20 c4) ∷
   rw 99 (q20 c4) ∷
   rw 96 (q22 c4) ∷
   rw 93 (q19 c4) ∷
   rw 90 (q19 c4) ∷
   rw 87 (q19 c4) ∷
   rw 84 (q20 c4) ∷
   rw 81 (q21 c4) ∷
   rw 78 (q20 c4) ∷
   rw 75 (q21 c4) ∷
   rw 72 (q20 c4) ∷
   rw 103 (q20 c4) ∷
   rw 100 (q20 c4) ∷
   rw 97 (q22 c4) ∷
   rw 94 (q19 c4) ∷
   rw 91 (q19 c4) ∷
   rw 88 (q19 c4) ∷
   rw 85 (q20 c4) ∷
   rw 82 (q21 c4) ∷
   rw 79 (q20 c4) ∷
   rw 76 (q21 c4) ∷
   rw 73 (q20 c4) ∷
   rw 104 (q20 c4) ∷
   rw 101 (q20 c4) ∷
   rw 98 (q22 c4) ∷
   rw 95 (q19 c4) ∷
   rw 92 (q19 c4) ∷
   rw 89 (q19 c4) ∷
   rw 86 (q20 c4) ∷
   rw 83 (q21 c4) ∷
   rw 80 (q20 c4) ∷
   rw 77 (q21 c4) ∷
   rw 74 (q20 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 27 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) [] (lem-TR2-11f6930f c4)

-- deb-Q-lo-eps: 20 steps
lem-deb-Q-lo-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-lo-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw 1 (q25 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ []) [] (lem-TR2-fed8f7c9 c4)

-- deb-Q-hi-eps: 20 steps
lem-deb-Q-hi-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-hi-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- deb-Q-lo-eps @02132031: 104 steps
lem-deb-Q-lo-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-lo-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 20 (q13 c4) ∷
   rw⁻ 19 (q15 c4) ∷
   rw 18 (q27 c4) ∷
   rw 17 (q27 c4) ∷
   rw 16 (q27 c4) ∷
   rw 15 (q28 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q29 c4) ∷
   rw 11 (q28 c4) ∷
   rw 10 (q27 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 21 (q30 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw 19 (q32 c4) ∷
   rw 18 (q32 c4) ∷
   rw 17 (q32 c4) ∷
   rw 16 (q33 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw 14 (q33 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw 12 (q33 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw 9 (q32 c4) ∷
   rw 8 (q32 c4) ∷
   rw 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 19 (q11 c4) ∷
   rw 18 (q11 c4) ∷
   rw 17 (q9 c4) ∷
   rw 16 (q12 c4) ∷
   rw 15 (q9 c4) ∷
   rw 14 (q12 c4) ∷
   rw 13 (q9 c4) ∷
   rw 12 (q11 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 9 (q11 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 21 (q16 c4) ∷
   rw 20 (q16 c4) ∷
   rw 19 (q16 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 14 (q14 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 11 (q16 c4) ∷
   rw 10 (q16 c4) ∷
   rw 9 (q16 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q25 c4) ∷
   rw 4 (q13 c4) ∷
   rw 3 (q8 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q13 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl
