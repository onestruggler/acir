{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD196 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D196 (Sᴰ : SD196) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-3bdac6c8)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

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
  lem-F4-I-I-at02132031 : Ws → St 1716
  lem-F4-I-I-at02132031 = pickᴰ 39 Sᴰ
  lem-F4-I-K3-at02132031 : Ws → St 1551
  lem-F4-I-K3-at02132031 = pickᴰ 40 Sᴰ
  lem-F4-I-S2-at02132031 : Ws → St 1535
  lem-F4-I-S2-at02132031 = pickᴰ 41 Sᴰ
  lem-F4-I-S3-at02132031 : Ws → St 1357
  lem-F4-I-S3-at02132031 = pickᴰ 42 Sᴰ
  lem-F4-K3-I-at02132031 : Ws → St 1717
  lem-F4-K3-I-at02132031 = pickᴰ 43 Sᴰ
  lem-F4-K3-K3-at02132031 : Ws → St 1553
  lem-F4-K3-K3-at02132031 = pickᴰ 44 Sᴰ
  lem-F4-K3-S2-at02132031 : Ws → St 1718
  lem-F4-K3-S2-at02132031 = pickᴰ 45 Sᴰ
  lem-F4-K3-S3-at02132031 : Ws → St 1702
  lem-F4-K3-S3-at02132031 = pickᴰ 46 Sᴰ
  lem-F4-S2-I-at02132031 : Ws → St 1555
  lem-F4-S2-I-at02132031 = pickᴰ 47 Sᴰ
  lem-F4-S2-K3-at02132031 : Ws → St 1557
  lem-F4-S2-K3-at02132031 = pickᴰ 48 Sᴰ
  lem-F4-S2-S2-at02132031 : Ws → St 1559
  lem-F4-S2-S2-at02132031 = pickᴰ 49 Sᴰ
  lem-F4-S2-S3-at02132031 : Ws → St 1704
  lem-F4-S2-S3-at02132031 = pickᴰ 50 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 51 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 52 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 53 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 54 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 55 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 56 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 57 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 58 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 59 Sᴰ
  lem-F4-CS2-CS2-at02132031 : Ws → St 1370
  lem-F4-CS2-CS2-at02132031 = pickᴰ 60 Sᴰ
  lem-F4-CS2-I-at02132031 : Ws → St 1371
  lem-F4-CS2-I-at02132031 = pickᴰ 61 Sᴰ
  lem-F4-CS2-S2-at02132031 : Ws → St 1541
  lem-F4-CS2-S2-at02132031 = pickᴰ 62 Sᴰ
  lem-F4-CS2-S3-at02132031 : Ws → St 1373
  lem-F4-CS2-S3-at02132031 = pickᴰ 63 Sᴰ
  lem-F4-I-CS2-at02132031 : Ws → St 1374
  lem-F4-I-CS2-at02132031 = pickᴰ 64 Sᴰ
  lem-F4-S2-CS2-at02132031 : Ws → St 1561
  lem-F4-S2-CS2-at02132031 = pickᴰ 65 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 66 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 67 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 68 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 69 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 70 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 71 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 72 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 73 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 74 Sᴰ
  lem-F4-CS2-K3-at02132031 : Ws → St 1563
  lem-F4-CS2-K3-at02132031 = pickᴰ 75 Sᴰ
  lem-F4-K3-CS2-at02132031 : Ws → St 1565
  lem-F4-K3-CS2-at02132031 = pickᴰ 76 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 77 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 78 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 79 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 80 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 81 Sᴰ
  lem-deb-Q-lo-split-a-at02132031 : Ws → St 1759
  lem-deb-Q-lo-split-a-at02132031 = pickᴰ 82 Sᴰ
  lem-deb-Q-lo-split-b-at02132031 : Ws → St 1760
  lem-deb-Q-lo-split-b-at02132031 = pickᴰ 83 Sᴰ
  lem-deb-Q-lo-eps-at02132031 : Ws → St 1761
  lem-deb-Q-lo-eps-at02132031 = pickᴰ 84 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-3bdac6c8 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) [] (lem-deb-Q-lo-eps-at02132031 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-CS2-at02132031 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-CS2-at02132031 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at02132031 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-K3-at02132031 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at02132031 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-K3-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S2-at02132031 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at02132031 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-I-at02132031 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-I-at02132031 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S3-at02132031 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S3-at02132031 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) (lem-deb-Q-lo-split-a-at02132031 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ []) (lem-deb-Q-lo-split-b-at02132031 c4)

-- deb-Q-lo @02132031: 331 steps
lem-deb-Q-lo-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-Q-lo-at02132031 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 5 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q5 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 5 (q8 c4) ∷
   rw 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 7 (q10 c4) ∷
   rw 6 (q10 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw 12 (q15 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q16 c4) ∷
   rw 16 (q16 c4) ∷
   rw 17 (q16 c4) ∷
   rw 18 (q16 c4) ∷
   rw 19 (q16 c4) ∷
   rw 20 (q16 c4) ∷
   rw 21 (q16 c4) ∷
   rw 22 (q16 c4) ∷
   rw 23 (q13 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q11 c4) ∷
   rw 27 (q13 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw 31 (q15 c4) ∷
   rw 32 (q16 c4) ∷
   rw 33 (q16 c4) ∷
   rw 34 (q16 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q19 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw⁻ 16 (q20 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 20 (q20 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw 22 (q17 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 24 (q17 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw 30 (q19 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw⁻ 32 (q20 c4) ∷
   rw⁻ 33 (q20 c4) ∷
   rw 34 (q7 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q22 c4) ∷
   rw 9 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 11 (q22 c4) ∷
   rw 12 (q24 c4) ∷
   rw 13 (q24 c4) ∷
   rw 14 (q24 c4) ∷
   rw 15 (q24 c4) ∷
   rw 16 (q24 c4) ∷
   rw 17 (q24 c4) ∷
   rw 18 (q24 c4) ∷
   rw 19 (q24 c4) ∷
   rw 20 (q24 c4) ∷
   rw 21 (q21 c4) ∷
   rw 22 (q6 c4) ∷
   rw 23 (q21 c4) ∷
   rw 24 (q6 c4) ∷
   rw 25 (q21 c4) ∷
   rw 26 (q22 c4) ∷
   rw 27 (q22 c4) ∷
   rw 28 (q22 c4) ∷
   rw 29 (q23 c4) ∷
   rw 30 (q24 c4) ∷
   rw 31 (q24 c4) ∷
   rw 32 (q24 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q26 c4) ∷
   rw 9 (q15 c4) ∷
   rw 10 (q26 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw 20 (q25 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 22 (q25 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 24 (q25 c4) ∷
   rw 25 (q26 c4) ∷
   rw 26 (q26 c4) ∷
   rw 27 (q26 c4) ∷
   rw 28 (q15 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 55 (q28 c4) ∷
   rw 52 (q29 c4) ∷
   rw 49 (q29 c4) ∷
   rw 46 (q29 c4) ∷
   rw 43 (q30 c4) ∷
   rw 40 (q31 c4) ∷
   rw 37 (q30 c4) ∷
   rw 34 (q31 c4) ∷
   rw 31 (q30 c4) ∷
   rw 56 (q32 c4) ∷
   rw 53 (q33 c4) ∷
   rw 50 (q33 c4) ∷
   rw 47 (q33 c4) ∷
   rw 44 (q34 c4) ∷
   rw 41 (q35 c4) ∷
   rw 38 (q34 c4) ∷
   rw 35 (q35 c4) ∷
   rw 32 (q34 c4) ∷
   rw 57 (q28 c4) ∷
   rw 54 (q29 c4) ∷
   rw 51 (q29 c4) ∷
   rw 48 (q29 c4) ∷
   rw 45 (q30 c4) ∷
   rw 42 (q31 c4) ∷
   rw 39 (q30 c4) ∷
   rw 36 (q31 c4) ∷
   rw 33 (q30 c4) ∷
   rw 58 (q32 c4) ∷
   rw 55 (q33 c4) ∷
   rw 52 (q33 c4) ∷
   rw 49 (q33 c4) ∷
   rw 46 (q34 c4) ∷
   rw 43 (q35 c4) ∷
   rw 40 (q34 c4) ∷
   rw 37 (q35 c4) ∷
   rw 34 (q34 c4) ∷
   rw 59 (q28 c4) ∷
   rw 56 (q29 c4) ∷
   rw 53 (q29 c4) ∷
   rw 50 (q29 c4) ∷
   rw 47 (q30 c4) ∷
   rw 44 (q31 c4) ∷
   rw 41 (q30 c4) ∷
   rw 38 (q31 c4) ∷
   rw 35 (q30 c4) ∷
   rw 60 (q36 c4) ∷
   rw 57 (q37 c4) ∷
   rw 54 (q37 c4) ∷
   rw 51 (q37 c4) ∷
   rw 48 (q38 c4) ∷
   rw 45 (q39 c4) ∷
   rw 42 (q38 c4) ∷
   rw 39 (q39 c4) ∷
   rw 36 (q38 c4) ∷
   rw 61 (q36 c4) ∷
   rw 58 (q37 c4) ∷
   rw 55 (q37 c4) ∷
   rw 52 (q37 c4) ∷
   rw 49 (q38 c4) ∷
   rw 46 (q39 c4) ∷
   rw 43 (q38 c4) ∷
   rw 40 (q39 c4) ∷
   rw 37 (q38 c4) ∷
   rw 62 (q36 c4) ∷
   rw 59 (q37 c4) ∷
   rw 56 (q37 c4) ∷
   rw 53 (q37 c4) ∷
   rw 50 (q38 c4) ∷
   rw 47 (q39 c4) ∷
   rw 44 (q38 c4) ∷
   rw 41 (q39 c4) ∷
   rw 38 (q38 c4) ∷
   rw 63 (q40 c4) ∷
   rw 60 (q41 c4) ∷
   rw 57 (q41 c4) ∷
   rw 54 (q41 c4) ∷
   rw 51 (q42 c4) ∷
   rw 48 (q43 c4) ∷
   rw 45 (q42 c4) ∷
   rw 42 (q43 c4) ∷
   rw 39 (q42 c4) ∷
   rw 64 (q36 c4) ∷
   rw 61 (q37 c4) ∷
   rw 58 (q37 c4) ∷
   rw 55 (q37 c4) ∷
   rw 52 (q38 c4) ∷
   rw 49 (q39 c4) ∷
   rw 46 (q38 c4) ∷
   rw 43 (q39 c4) ∷
   rw 40 (q38 c4) ∷
   rw 65 (q44 c4) ∷
   rw 62 (q45 c4) ∷
   rw 59 (q45 c4) ∷
   rw 56 (q45 c4) ∷
   rw 53 (q46 c4) ∷
   rw 50 (q47 c4) ∷
   rw 47 (q46 c4) ∷
   rw 44 (q47 c4) ∷
   rw 41 (q46 c4) ∷
   rw 66 (q44 c4) ∷
   rw 63 (q45 c4) ∷
   rw 60 (q45 c4) ∷
   rw 57 (q45 c4) ∷
   rw 54 (q46 c4) ∷
   rw 51 (q47 c4) ∷
   rw 48 (q46 c4) ∷
   rw 45 (q47 c4) ∷
   rw 42 (q46 c4) ∷
   rw 67 (q44 c4) ∷
   rw 64 (q45 c4) ∷
   rw 61 (q45 c4) ∷
   rw 58 (q45 c4) ∷
   rw 55 (q46 c4) ∷
   rw 52 (q47 c4) ∷
   rw 49 (q46 c4) ∷
   rw 46 (q47 c4) ∷
   rw 43 (q46 c4) ∷
   rw 68 (q44 c4) ∷
   rw 65 (q45 c4) ∷
   rw 62 (q45 c4) ∷
   rw 59 (q45 c4) ∷
   rw 56 (q46 c4) ∷
   rw 53 (q47 c4) ∷
   rw 50 (q46 c4) ∷
   rw 47 (q47 c4) ∷
   rw 44 (q46 c4) ∷
   rw 69 (q44 c4) ∷
   rw 66 (q45 c4) ∷
   rw 63 (q45 c4) ∷
   rw 60 (q45 c4) ∷
   rw 57 (q46 c4) ∷
   rw 54 (q47 c4) ∷
   rw 51 (q46 c4) ∷
   rw 48 (q47 c4) ∷
   rw 45 (q46 c4) ∷
   rw 70 (q44 c4) ∷
   rw 67 (q45 c4) ∷
   rw 64 (q45 c4) ∷
   rw 61 (q45 c4) ∷
   rw 58 (q46 c4) ∷
   rw 55 (q47 c4) ∷
   rw 52 (q46 c4) ∷
   rw 49 (q47 c4) ∷
   rw 46 (q46 c4) ∷
   rw 71 (q44 c4) ∷
   rw 68 (q45 c4) ∷
   rw 65 (q45 c4) ∷
   rw 62 (q45 c4) ∷
   rw 59 (q46 c4) ∷
   rw 56 (q47 c4) ∷
   rw 53 (q46 c4) ∷
   rw 50 (q47 c4) ∷
   rw 47 (q46 c4) ∷
   rw 72 (q44 c4) ∷
   rw 69 (q45 c4) ∷
   rw 66 (q45 c4) ∷
   rw 63 (q45 c4) ∷
   rw 60 (q46 c4) ∷
   rw 57 (q47 c4) ∷
   rw 54 (q46 c4) ∷
   rw 51 (q47 c4) ∷
   rw 48 (q46 c4) ∷
   rw 73 (q44 c4) ∷
   rw 70 (q45 c4) ∷
   rw 67 (q45 c4) ∷
   rw 64 (q45 c4) ∷
   rw 61 (q46 c4) ∷
   rw 58 (q47 c4) ∷
   rw 55 (q46 c4) ∷
   rw 52 (q47 c4) ∷
   rw 49 (q46 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw⁻ 20 (q49 c4) ∷ []) Eq.refl
