{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD197 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D197 (Sᴰ : SD197) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-bf3fb9f8)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R)

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
  lem-F4-I-I-at132132 : Ws → St 1743
  lem-F4-I-I-at132132 = pickᴰ 39 Sᴰ
  lem-F4-I-K2-at132132 : Ws → St 1387
  lem-F4-I-K2-at132132 = pickᴰ 40 Sᴰ
  lem-F4-I-S2-at132132 : Ws → St 1536
  lem-F4-I-S2-at132132 = pickᴰ 41 Sᴰ
  lem-F4-I-S3-at132132 : Ws → St 1388
  lem-F4-I-S3-at132132 = pickᴰ 42 Sᴰ
  lem-F4-K2-I-at132132 : Ws → St 1744
  lem-F4-K2-I-at132132 = pickᴰ 43 Sᴰ
  lem-F4-K2-K2-at132132 : Ws → St 1389
  lem-F4-K2-K2-at132132 = pickᴰ 44 Sᴰ
  lem-F4-K2-S2-at132132 : Ws → St 1538
  lem-F4-K2-S2-at132132 = pickᴰ 45 Sᴰ
  lem-F4-K2-S3-at132132 : Ws → St 1745
  lem-F4-K2-S3-at132132 = pickᴰ 46 Sᴰ
  lem-F4-S3-I-at132132 : Ws → St 1390
  lem-F4-S3-I-at132132 = pickᴰ 47 Sᴰ
  lem-F4-S3-K2-at132132 : Ws → St 1391
  lem-F4-S3-K2-at132132 = pickᴰ 48 Sᴰ
  lem-F4-S3-S2-at132132 : Ws → St 1540
  lem-F4-S3-S2-at132132 = pickᴰ 49 Sᴰ
  lem-F4-S3-S3-at132132 : Ws → St 1392
  lem-F4-S3-S3-at132132 = pickᴰ 50 Sᴰ
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
  lem-F4-CS2-CS2-at132132 : Ws → St 1395
  lem-F4-CS2-CS2-at132132 = pickᴰ 60 Sᴰ
  lem-F4-CS2-I-at132132 : Ws → St 1396
  lem-F4-CS2-I-at132132 = pickᴰ 61 Sᴰ
  lem-F4-CS2-K2-at132132 : Ws → St 1397
  lem-F4-CS2-K2-at132132 = pickᴰ 62 Sᴰ
  lem-F4-CS2-S2-at132132 : Ws → St 1542
  lem-F4-CS2-S2-at132132 = pickᴰ 63 Sᴰ
  lem-F4-CS2-S3-at132132 : Ws → St 1398
  lem-F4-CS2-S3-at132132 = pickᴰ 64 Sᴰ
  lem-F4-I-CS2-at132132 : Ws → St 1399
  lem-F4-I-CS2-at132132 = pickᴰ 65 Sᴰ
  lem-F4-K2-CS2-at132132 : Ws → St 1400
  lem-F4-K2-CS2-at132132 = pickᴰ 66 Sᴰ
  lem-F4-S3-CS2-at132132 : Ws → St 1401
  lem-F4-S3-CS2-at132132 = pickᴰ 67 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 68 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 69 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 70 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 71 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 72 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 73 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 74 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 75 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 76 Sᴰ
  lem-deb-Q-hi-split-a-at132132 : Ws → St 1762
  lem-deb-Q-hi-split-a-at132132 = pickᴰ 77 Sᴰ
  lem-deb-Q-hi-split-b-at132132 : Ws → St 1763
  lem-deb-Q-hi-split-b-at132132 = pickᴰ 78 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1695
  lem-F1-X-CS0at2 = pickᴰ 79 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1696
  lem-F2-CS0-CS2 = pickᴰ 80 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1698
  lem-F1-X-CS1at2 = pickᴰ 81 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1699
  lem-F1-CS-K0at2 = pickᴰ 82 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1700
  lem-F1-CS-K1at2 = pickᴰ 83 Sᴰ
  lem-deb-Q-hi-eps-at132132 : Ws → St 1764
  lem-deb-Q-hi-eps-at132132 = pickᴰ 84 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl 99 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-bf3fb9f8 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q11 : Ws → Eqn
  q11 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) [] (lem-deb-Q-hi-eps-at132132 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at132132 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-CS2-at132132 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at132132 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-CS2-at132132 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2-at132132 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-K2-at132132 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at132132 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-K2-at132132 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at132132 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S3-at132132 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at132132 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S3-at132132 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at132132 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-I-at132132 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at132132 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-I-at132132 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S3-S2-at132132 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at132132 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K2-S2-at132132 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) (lem-deb-Q-hi-split-a-at132132 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (lem-deb-Q-hi-split-b-at132132 c4)

-- deb-Q-hi @132132: 253 steps
lem-deb-Q-hi-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-Q-hi-at132132 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
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
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 17 (q11 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 20 (q11 c4) ∷
   rw 21 (q8 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 23 (q8 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw 25 (q8 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q9 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw⁻ 30 (q11 c4) ∷
   rw⁻ 31 (q11 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q12 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw⁻ 17 (q15 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw⁻ 19 (q15 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 24 (q12 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw 28 (q14 c4) ∷
   rw⁻ 29 (q15 c4) ∷
   rw⁻ 30 (q15 c4) ∷
   rw⁻ 31 (q15 c4) ∷
   rw 32 (q1 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 55 (q17 c4) ∷
   rw 52 (q18 c4) ∷
   rw 49 (q18 c4) ∷
   rw 46 (q18 c4) ∷
   rw 43 (q19 c4) ∷
   rw 40 (q20 c4) ∷
   rw 37 (q19 c4) ∷
   rw 34 (q20 c4) ∷
   rw 31 (q19 c4) ∷
   rw 56 (q21 c4) ∷
   rw 53 (q22 c4) ∷
   rw 50 (q22 c4) ∷
   rw 47 (q22 c4) ∷
   rw 44 (q23 c4) ∷
   rw 41 (q24 c4) ∷
   rw 38 (q23 c4) ∷
   rw 35 (q24 c4) ∷
   rw 32 (q23 c4) ∷
   rw 57 (q17 c4) ∷
   rw 54 (q18 c4) ∷
   rw 51 (q18 c4) ∷
   rw 48 (q18 c4) ∷
   rw 45 (q19 c4) ∷
   rw 42 (q20 c4) ∷
   rw 39 (q19 c4) ∷
   rw 36 (q20 c4) ∷
   rw 33 (q19 c4) ∷
   rw 58 (q21 c4) ∷
   rw 55 (q22 c4) ∷
   rw 52 (q22 c4) ∷
   rw 49 (q22 c4) ∷
   rw 46 (q23 c4) ∷
   rw 43 (q24 c4) ∷
   rw 40 (q23 c4) ∷
   rw 37 (q24 c4) ∷
   rw 34 (q23 c4) ∷
   rw 59 (q17 c4) ∷
   rw 56 (q18 c4) ∷
   rw 53 (q18 c4) ∷
   rw 50 (q18 c4) ∷
   rw 47 (q19 c4) ∷
   rw 44 (q20 c4) ∷
   rw 41 (q19 c4) ∷
   rw 38 (q20 c4) ∷
   rw 35 (q19 c4) ∷
   rw 60 (q25 c4) ∷
   rw 57 (q26 c4) ∷
   rw 54 (q26 c4) ∷
   rw 51 (q26 c4) ∷
   rw 48 (q27 c4) ∷
   rw 45 (q28 c4) ∷
   rw 42 (q27 c4) ∷
   rw 39 (q28 c4) ∷
   rw 36 (q27 c4) ∷
   rw 61 (q25 c4) ∷
   rw 58 (q26 c4) ∷
   rw 55 (q26 c4) ∷
   rw 52 (q26 c4) ∷
   rw 49 (q27 c4) ∷
   rw 46 (q28 c4) ∷
   rw 43 (q27 c4) ∷
   rw 40 (q28 c4) ∷
   rw 37 (q27 c4) ∷
   rw 62 (q25 c4) ∷
   rw 59 (q26 c4) ∷
   rw 56 (q26 c4) ∷
   rw 53 (q26 c4) ∷
   rw 50 (q27 c4) ∷
   rw 47 (q28 c4) ∷
   rw 44 (q27 c4) ∷
   rw 41 (q28 c4) ∷
   rw 38 (q27 c4) ∷
   rw 63 (q29 c4) ∷
   rw 60 (q30 c4) ∷
   rw 57 (q30 c4) ∷
   rw 54 (q30 c4) ∷
   rw 51 (q31 c4) ∷
   rw 48 (q32 c4) ∷
   rw 45 (q31 c4) ∷
   rw 42 (q32 c4) ∷
   rw 39 (q31 c4) ∷
   rw 64 (q25 c4) ∷
   rw 61 (q26 c4) ∷
   rw 58 (q26 c4) ∷
   rw 55 (q26 c4) ∷
   rw 52 (q27 c4) ∷
   rw 49 (q28 c4) ∷
   rw 46 (q27 c4) ∷
   rw 43 (q28 c4) ∷
   rw 40 (q27 c4) ∷
   rw 65 (q33 c4) ∷
   rw 62 (q34 c4) ∷
   rw 59 (q34 c4) ∷
   rw 56 (q34 c4) ∷
   rw 53 (q35 c4) ∷
   rw 50 (q36 c4) ∷
   rw 47 (q35 c4) ∷
   rw 44 (q36 c4) ∷
   rw 41 (q35 c4) ∷
   rw 66 (q33 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q34 c4) ∷
   rw 57 (q34 c4) ∷
   rw 54 (q35 c4) ∷
   rw 51 (q36 c4) ∷
   rw 48 (q35 c4) ∷
   rw 45 (q36 c4) ∷
   rw 42 (q35 c4) ∷
   rw 67 (q33 c4) ∷
   rw 64 (q34 c4) ∷
   rw 61 (q34 c4) ∷
   rw 58 (q34 c4) ∷
   rw 55 (q35 c4) ∷
   rw 52 (q36 c4) ∷
   rw 49 (q35 c4) ∷
   rw 46 (q36 c4) ∷
   rw 43 (q35 c4) ∷
   rw 68 (q33 c4) ∷
   rw 65 (q34 c4) ∷
   rw 62 (q34 c4) ∷
   rw 59 (q34 c4) ∷
   rw 56 (q35 c4) ∷
   rw 53 (q36 c4) ∷
   rw 50 (q35 c4) ∷
   rw 47 (q36 c4) ∷
   rw 44 (q35 c4) ∷
   rw 69 (q33 c4) ∷
   rw 66 (q34 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q34 c4) ∷
   rw 57 (q35 c4) ∷
   rw 54 (q36 c4) ∷
   rw 51 (q35 c4) ∷
   rw 48 (q36 c4) ∷
   rw 45 (q35 c4) ∷
   rw 70 (q33 c4) ∷
   rw 67 (q34 c4) ∷
   rw 64 (q34 c4) ∷
   rw 61 (q34 c4) ∷
   rw 58 (q35 c4) ∷
   rw 55 (q36 c4) ∷
   rw 52 (q35 c4) ∷
   rw 49 (q36 c4) ∷
   rw 46 (q35 c4) ∷
   rw 71 (q33 c4) ∷
   rw 68 (q34 c4) ∷
   rw 65 (q34 c4) ∷
   rw 62 (q34 c4) ∷
   rw 59 (q35 c4) ∷
   rw 56 (q36 c4) ∷
   rw 53 (q35 c4) ∷
   rw 50 (q36 c4) ∷
   rw 47 (q35 c4) ∷
   rw 72 (q33 c4) ∷
   rw 69 (q34 c4) ∷
   rw 66 (q34 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q35 c4) ∷
   rw 57 (q36 c4) ∷
   rw 54 (q35 c4) ∷
   rw 51 (q36 c4) ∷
   rw 48 (q35 c4) ∷
   rw 73 (q33 c4) ∷
   rw 70 (q34 c4) ∷
   rw 67 (q34 c4) ∷
   rw 64 (q34 c4) ∷
   rw 61 (q35 c4) ∷
   rw 58 (q36 c4) ∷
   rw 55 (q35 c4) ∷
   rw 52 (q36 c4) ∷
   rw 49 (q35 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   rw⁻ 20 (q38 c4) ∷ []) Eq.refl
