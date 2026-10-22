{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD223 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D223 (Sᴰ : SD223) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-1b52048e ; lem-TR2-ff6c1f51)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-TOFF213-CX04 ; lem-comm-TOFF312-CX04 ; lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-TOFF314-CX02 ; lem-comm-push-CK40-sw1-R ; lem-comm-push-CK41-sw0-R ; lem-comm-push-CS14-sw0-R)
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
  lem-S-sym-xt-at14213243 : Ws → St 1948
  lem-S-sym-xt-at14213243 = pickᴰ 39 Sᴰ
  lem-CK-box-at033440 : Ws → St 1949
  lem-CK-box-at033440 = pickᴰ 40 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1669
  lem-F2-S0-CS1 = pickᴰ 41 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1670
  lem-F2-S0-CS2 = pickᴰ 42 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1671
  lem-F2-S2-CS0 = pickᴰ 43 Sᴰ
  lem-box-cP-at031031 : Ws → St 952
  lem-box-cP-at031031 = pickᴰ 44 Sᴰ
  lem-box-perm-1324-at03102132 : Ws → St 904
  lem-box-perm-1324-at03102132 = pickᴰ 45 Sᴰ
  lem-box-cP-at02142041 : Ws → St 1000
  lem-box-cP-at02142041 = pickᴰ 46 Sᴰ
  lem-box-cP-at0314203241 : Ws → St 1001
  lem-box-cP-at0314203241 = pickᴰ 47 Sᴰ
  lem-box2-at03102132 : Ws → St 1950
  lem-box2-at03102132 = pickᴰ 48 Sᴰ
  lem-box-perm-2341-at03102132 : Ws → St 1269
  lem-box-perm-2341-at03102132 = pickᴰ 49 Sᴰ
  lem-F2-I-CS0 : Ws → St 1673
  lem-F2-I-CS0 = pickᴰ 50 Sᴰ
  lem-F2-I-CS1 : Ws → St 1674
  lem-F2-I-CS1 = pickᴰ 51 Sᴰ
  lem-F2-I-CS2 : Ws → St 1675
  lem-F2-I-CS2 = pickᴰ 52 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1676
  lem-F2-S1-CS2 = pickᴰ 53 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1677
  lem-F2-S3-CS0 = pickᴰ 54 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1678
  lem-F2-S3-CS1 = pickᴰ 55 Sᴰ
  lem-box-perm-2431-at02142041 : Ws → St 1951
  lem-box-perm-2431-at02142041 = pickᴰ 56 Sᴰ
  lem-box-perm-4132-at021021 : Ws → St 1952
  lem-box-perm-4132-at021021 = pickᴰ 57 Sᴰ
  lem-box-perm-4132-at03102132 : Ws → St 1953
  lem-box-perm-4132-at03102132 = pickᴰ 58 Sᴰ
  lem-box2-at02142041 : Ws → St 1954
  lem-box2-at02142041 = pickᴰ 59 Sᴰ
  lem-box2-at0314203241 : Ws → St 1955
  lem-box2-at0314203241 = pickᴰ 60 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1680
  lem-F2-K1-CS2 = pickᴰ 61 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1681
  lem-F1-comm-CS-S0at2 = pickᴰ 62 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1682
  lem-F2-K3-CS0 = pickᴰ 63 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1683
  lem-F2-K3-CS1 = pickᴰ 64 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1685
  lem-F1-comm-CS-S1at2 = pickᴰ 65 Sᴰ
  lem-box-box-3-at021021 : Ws → St 1956
  lem-box-box-3-at021021 = pickᴰ 66 Sᴰ
  lem-box-perm-2431-at0314203241 : Ws → St 1957
  lem-box-perm-2431-at0314203241 = pickᴰ 67 Sᴰ
  lem-box-perm-3241-at02142041 : Ws → St 1958
  lem-box-perm-3241-at02142041 = pickᴰ 68 Sᴰ
  lem-box-perm-3241-at0314203241 : Ws → St 1959
  lem-box-perm-3241-at0314203241 = pickᴰ 69 Sᴰ
  lem-box-perm-4213-at02132031 : Ws → St 1960
  lem-box-perm-4213-at02132031 = pickᴰ 70 Sᴰ
  lem-box-perm-4213-at03122031 : Ws → St 1961
  lem-box-perm-4213-at03122031 = pickᴰ 71 Sᴰ
  lem-ckt-Dinv : Ws → St 1962
  lem-ckt-Dinv = pickᴰ 72 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1687
  lem-F1-order-CSat2 = pickᴰ 73 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1688
  lem-F2-K0-CS1 = pickᴰ 74 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1689
  lem-F2-K0-CS2 = pickᴰ 75 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1690
  lem-F2-K2-CS0 = pickᴰ 76 Sᴰ
  lem-L-CX01-2 : Ws → St 1527
  lem-L-CX01-2 = pickᴰ 77 Sᴰ
  lem-L-CX10-2 : Ws → St 1528
  lem-L-CX10-2 = pickᴰ 78 Sᴰ
  lem-Tu-box-at0314203241 : Ws → St 1963
  lem-Tu-box-at0314203241 = pickᴰ 79 Sᴰ
  lem-box-box-3-at03102132 : Ws → St 1964
  lem-box-box-3-at03102132 = pickᴰ 80 Sᴰ
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
  lem-Tu-box-at02142041 : Ws → St 1965
  lem-Tu-box-at02142041 = pickᴰ 86 Sᴰ
  lem-deb-Q-lo-at02132031 : Ws → St 1833
  lem-deb-Q-lo-at02132031 = pickᴰ 87 Sᴰ
  lem-deb-Q-hi-at132132 : Ws → St 1834
  lem-deb-Q-hi-at132132 = pickᴰ 88 Sᴰ
  lem-deb-P-hi : Ws → St 1870
  lem-deb-P-hi = pickᴰ 89 Sᴰ
  lem-deb-P-hi-at132132 : Ws → St 1872
  lem-deb-P-hi-at132132 = pickᴰ 90 Sᴰ
  lem-deb-P-lo-at02132031 : Ws → St 1873
  lem-deb-P-lo-at02132031 = pickᴰ 91 Sᴰ
  lem-deb-P-lo-at132132 : Ws → St 1874
  lem-deb-P-lo-at132132 = pickᴰ 92 Sᴰ
  lem-deb-AD-at02132031 : Ws → St 1966
  lem-deb-AD-at02132031 = pickᴰ 93 Sᴰ
  lem-deb-rel-272at0-R : Ws → St 1967
  lem-deb-rel-272at0-R = pickᴰ 94 Sᴰ
  lem-F1-comm-CSu-CSat0 : Ws → St 1968
  lem-F1-comm-CSu-CSat0 = pickᴰ 95 Sᴰ
  lem-L-CCZ-0 : Ws → St 1969
  lem-L-CCZ-0 = pickᴰ 96 Sᴰ
  lem-deb-rel-269at0-R : Ws → St 1970
  lem-deb-rel-269at0-R = pickᴰ 97 Sᴰ
  lem-deb-rel-269at1-R : Ws → St 1971
  lem-deb-rel-269at1-R = pickᴰ 98 Sᴰ
  lem-ckt-A-R : Ws → St 1972
  lem-ckt-A-R = pickᴰ 99 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1969 (lem-L-CCZ-0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1527 (lem-L-CX01-2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1528 (lem-L-CX10-2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 904 (lem-box-perm-1324-at03102132 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 952 (lem-box-cP-at031031 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1180 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 1046 c4
  q8 : Ws → Eqn
  q8 c4 = wpE 296 c4
  q9 : Ws → Eqn
  q9 c4 = wlE 754 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff314 ∷ CX02 ∷ []) (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = wlE 1371 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 998 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 814 c4
  q14 : Ws → Eqn
  q14 c4 = wlE 420 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1953 (lem-box-perm-4132-at03102132 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1963 (lem-Tu-box-at0314203241 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1957 (lem-box-perm-2431-at0314203241 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1958 (lem-box-perm-3241-at02142041 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1964 (lem-box-box-3-at03102132 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1960 (lem-box-perm-4213-at02132031 c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 442 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1965 (lem-Tu-box-at02142041 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1951 (lem-box-perm-2431-at02142041 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1959 (lem-box-perm-3241-at0314203241 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1956 (lem-box-box-3-at021021 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1961 (lem-box-perm-4213-at03122031 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1952 (lem-box-perm-4132-at021021 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1950 (lem-box2-at03102132 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1954 (lem-box2-at02142041 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1000 (lem-box-cP-at02142041 c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 942 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 790 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 352 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 808 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = wlE 807 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 196 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 768 c4
  q39 : Ws → Eqn
  q39 c4 = sE 1001 (lem-box-cP-at0314203241 c4)
  q40 : Ws → Eqn
  q40 c4 = wlE 852 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 295 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 13 c4
  q43 : Ws → Eqn
  q43 c4 = wlE 879 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = wlE 878 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 861 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 737 c4
  q48 : Ws → Eqn
  q48 c4 = sE 1955 (lem-box2-at0314203241 c4)

-- nf-cx-ccz@0: 265 steps
lem-nf-cx-cczat0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-nf-cx-cczat0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw 7 (q2 c4) ∷
   rw 4 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 5 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 8 (q6 c4) ∷
   rw 10 (q8 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 7 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q15 c4) ∷
   rw 8 (q17 c4) ∷
   rw 8 (q28 c4) ∷
   rw 0 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q6 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 0 (q13 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 4 (q6 c4) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 8 (q10 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 4 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 5 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 8 (q6 c4) ∷
   rw 10 (q8 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q18 c4) ∷
   rw 8 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q27 c4) ∷
   rw 8 (q29 c4) ∷
   rw 7 (q17 c4) ∷
   rw 7 (q28 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw 5 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw 6 (q30 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q32 c4) ∷
   rw 7 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw 9 (q35 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q35 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw 6 (q38 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw 8 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q15 c4) ∷
   rw 7 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw 8 (q40 c4) ∷
   rw 10 (q42 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw 10 (q44 c4) ∷
   rw⁻ 11 (q45 c4) ∷
   rw 12 (q44 c4) ∷
   rw⁻ 13 (q46 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw 7 (q47 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw 8 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw 9 (q15 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q27 c4) ∷
   rw 8 (q29 c4) ∷
   rw 3 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q40 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 8 (q44 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw 5 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q15 c4) ∷
   rw 6 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q40 c4) ∷
   rw 9 (q42 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q46 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q15 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 1373 (lit c4)

-- L-CCZ013-0: 60 steps
lem-L-CCZ013-0 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-L-CCZ013-0 c4 = derive (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw 6 (q2 c4) ∷
   rw 3 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 4 (q6 c4) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 8 (q10 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 6 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw 5 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 7 (q6 c4) ∷
   rw 9 (q8 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw 11 (q10 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q15 c4) ∷
   rw 7 (q17 c4) ∷
   rw 7 (q28 c4) ∷
   rw 0 (q49 c4) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = wpE 1218 c4
  q51 : Ws → Eqn
  q51 c4 = sE 1269 (lem-box-perm-2341-at03102132 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1949 (lem-CK-box-at033440 c4)

-- L-Toff-0: 4 steps
lem-L-Toff-0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-L-Toff-0 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = sE 1872 (lem-deb-P-hi-at132132 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1873 (lem-deb-P-lo-at02132031 c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 1270 c4
  q56 : Ws → Eqn
  q56 c4 = sE 1970 (lem-deb-rel-269at0-R c4)

-- F1-rel-269@0: 4 steps
lem-F1-rel-269at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-269at0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q53 c4) ∷
   rw 42 (q54 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = sE 1870 (lem-deb-P-hi c4)
  q58 : Ws → Eqn
  q58 c4 = sE 1874 (lem-deb-P-lo-at132132 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q60 : Ws → Eqn
  q60 c4 = wpE 1271 c4
  q61 : Ws → Eqn
  q61 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q62 : Ws → Eqn
  q62 c4 = sE 1971 (lem-deb-rel-269at1-R c4)

-- F1-rel-269@1: 12 steps
lem-F1-rel-269at1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-269at1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (rw 0 (q57 c4) ∷
   rw 42 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw 35 (q59 c4) ∷
   rw 58 (q59 c4) ∷
   rw 77 (q59 c4) ∷
   rw⁻ 0 (q60 c4) ∷
   rw 16 (q61 c4) ∷
   rw 35 (q61 c4) ∷
   rw 58 (q61 c4) ∷
   rw 77 (q61 c4) ∷
   rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wlE 6 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 18 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 3 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn [] (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-TR2-1b52048e c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q71 : Ws → Eqn
  q71 c4 = sE 1834 (lem-deb-Q-hi-at132132 c4)
  q72 : Ws → Eqn
  q72 c4 = sE 1833 (lem-deb-Q-lo-at02132031 c4)
  q73 : Ws → Eqn
  q73 c4 = sE 1968 (lem-F1-comm-CSu-CSat0 c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 1272 c4
  q75 : Ws → Eqn
  q75 c4 = sE 1967 (lem-deb-rel-272at0-R c4)

-- F1-rel-272@0: 30 steps
lem-F1-rel-272at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-rel-272at0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 8 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw⁻ 11 (q63 c4) ∷
   rw 12 (q66 c4) ∷
   rw 11 (q67 c4) ∷
   rw 12 (q67 c4) ∷
   rw 13 (q67 c4) ∷
   rw 14 (q67 c4) ∷
   rw 15 (q63 c4) ∷
   rw 10 (q68 c4) ∷
   rw 11 (q68 c4) ∷
   rw 12 (q68 c4) ∷
   rw 13 (q68 c4) ∷
   rw 14 (q65 c4) ∷
   rw 9 (q69 c4) ∷
   rw 10 (q69 c4) ∷
   rw 11 (q69 c4) ∷
   rw 12 (q69 c4) ∷
   rw 13 (q64 c4) ∷
   rw 8 (q70 c4) ∷
   rw 9 (q70 c4) ∷
   rw 10 (q70 c4) ∷
   rw 11 (q70 c4) ∷
   rw 12 (q63 c4) ∷
   rw 0 (q71 c4) ∷
   rw 33 (q72 c4) ∷
   rw⁻ 65 (q73 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw⁻ 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q77 : Ws → Eqn
  q77 c4 = eqn (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q80 : Ws → Eqn
  q80 c4 = wlE 87 (lit c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q82 : Ws → Eqn
  q82 c4 = eqn (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q87 : Ws → Eqn
  q87 c4 = wlE 99 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 17 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q90 : Ws → Eqn
  q90 c4 = wlE 90 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 13 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q94 : Ws → Eqn
  q94 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (lem-TR2-ff6c1f51 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4))
  q99 : Ws → Eqn
  q99 c4 = sE 1966 (lem-deb-AD-at02132031 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 1962 (lem-ckt-Dinv c4)
  q101 : Ws → Eqn
  q101 c4 = sE 1948 (lem-S-sym-xt-at14213243 c4)
  q102 : Ws → Eqn
  q102 c4 = wpE 1308 c4
  q103 : Ws → Eqn
  q103 c4 = sE 1972 (lem-ckt-A-R c4)

-- ckt-A: 264 steps
lem-ckt-A : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-ckt-A c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (rw⁻ 19 (q63 c4) ∷
   rw⁻ 18 (q76 c4) ∷
   rw 17 (q77 c4) ∷
   rw 16 (q78 c4) ∷
   rw 15 (q78 c4) ∷
   rw 14 (q77 c4) ∷
   rw⁻ 13 (q76 c4) ∷
   rw 12 (q78 c4) ∷
   rw 11 (q78 c4) ∷
   rw 10 (q78 c4) ∷
   rw 9 (q79 c4) ∷
   rw 8 (q80 c4) ∷
   rw 7 (q79 c4) ∷
   rw 6 (q80 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 20 (q64 c4) ∷
   rw⁻ 19 (q81 c4) ∷
   rw 18 (q82 c4) ∷
   rw 17 (q83 c4) ∷
   rw 16 (q83 c4) ∷
   rw 15 (q82 c4) ∷
   rw⁻ 14 (q81 c4) ∷
   rw 13 (q83 c4) ∷
   rw 12 (q83 c4) ∷
   rw 11 (q83 c4) ∷
   rw 10 (q84 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw 8 (q84 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw 6 (q84 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw 3 (q83 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q82 c4) ∷
   rw⁻ 21 (q65 c4) ∷
   rw⁻ 20 (q86 c4) ∷
   rw 19 (q87 c4) ∷
   rw 18 (q88 c4) ∷
   rw 17 (q88 c4) ∷
   rw 16 (q87 c4) ∷
   rw⁻ 15 (q86 c4) ∷
   rw 14 (q88 c4) ∷
   rw 13 (q88 c4) ∷
   rw 12 (q88 c4) ∷
   rw 11 (q89 c4) ∷
   rw 10 (q90 c4) ∷
   rw 9 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw 3 (q88 c4) ∷
   rw 2 (q87 c4) ∷
   rw⁻ 22 (q63 c4) ∷
   rw⁻ 21 (q76 c4) ∷
   rw 20 (q80 c4) ∷
   rw 19 (q91 c4) ∷
   rw 18 (q91 c4) ∷
   rw 17 (q80 c4) ∷
   rw⁻ 16 (q76 c4) ∷
   rw 15 (q91 c4) ∷
   rw 14 (q91 c4) ∷
   rw 13 (q91 c4) ∷
   rw 12 (q92 c4) ∷
   rw⁻ 11 (q93 c4) ∷
   rw 10 (q92 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 6 (q80 c4) ∷
   rw 5 (q91 c4) ∷
   rw 4 (q91 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q94 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 7 (q76 c4) ∷
   rw 8 (q67 c4) ∷
   rw 9 (q93 c4) ∷
   rw 10 (q67 c4) ∷
   rw 11 (q93 c4) ∷
   rw 12 (q67 c4) ∷
   rw⁻ 13 (q91 c4) ∷
   rw⁻ 14 (q91 c4) ∷
   rw⁻ 15 (q91 c4) ∷
   rw 16 (q76 c4) ∷
   rw⁻ 17 (q80 c4) ∷
   rw⁻ 18 (q91 c4) ∷
   rw⁻ 19 (q91 c4) ∷
   rw⁻ 20 (q80 c4) ∷
   rw 21 (q76 c4) ∷
   rw⁻ 22 (q80 c4) ∷
   rw⁻ 23 (q91 c4) ∷
   rw⁻ 24 (q91 c4) ∷
   rw⁻ 25 (q80 c4) ∷
   rw 26 (q76 c4) ∷
   rw 27 (q67 c4) ∷
   rw⁻ 28 (q80 c4) ∷
   rw⁻ 29 (q91 c4) ∷
   rw⁻ 30 (q91 c4) ∷
   rw⁻ 31 (q80 c4) ∷
   rw 32 (q76 c4) ∷
   rw⁻ 33 (q80 c4) ∷
   rw⁻ 34 (q91 c4) ∷
   rw⁻ 35 (q91 c4) ∷
   rw⁻ 36 (q80 c4) ∷
   rw 37 (q76 c4) ∷
   rw 38 (q67 c4) ∷
   rw 39 (q67 c4) ∷
   rw 40 (q67 c4) ∷
   rw⁻ 41 (q80 c4) ∷
   rw⁻ 42 (q91 c4) ∷
   rw⁻ 43 (q91 c4) ∷
   rw⁻ 44 (q80 c4) ∷
   rw 45 (q76 c4) ∷
   rw 46 (q63 c4) ∷
   rw⁻ 2 (q87 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw⁻ 5 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 8 (q90 c4) ∷
   rw 9 (q68 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw 11 (q68 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw⁻ 13 (q88 c4) ∷
   rw⁻ 14 (q88 c4) ∷
   rw 15 (q86 c4) ∷
   rw⁻ 16 (q87 c4) ∷
   rw⁻ 17 (q88 c4) ∷
   rw⁻ 18 (q88 c4) ∷
   rw⁻ 19 (q87 c4) ∷
   rw 20 (q86 c4) ∷
   rw⁻ 21 (q87 c4) ∷
   rw⁻ 22 (q88 c4) ∷
   rw⁻ 23 (q88 c4) ∷
   rw⁻ 24 (q87 c4) ∷
   rw 25 (q86 c4) ∷
   rw 26 (q68 c4) ∷
   rw⁻ 27 (q87 c4) ∷
   rw⁻ 28 (q88 c4) ∷
   rw⁻ 29 (q88 c4) ∷
   rw⁻ 30 (q87 c4) ∷
   rw 31 (q86 c4) ∷
   rw⁻ 32 (q87 c4) ∷
   rw⁻ 33 (q88 c4) ∷
   rw⁻ 34 (q88 c4) ∷
   rw⁻ 35 (q87 c4) ∷
   rw 36 (q86 c4) ∷
   rw 37 (q68 c4) ∷
   rw 38 (q68 c4) ∷
   rw 39 (q68 c4) ∷
   rw⁻ 40 (q87 c4) ∷
   rw⁻ 41 (q88 c4) ∷
   rw⁻ 42 (q88 c4) ∷
   rw⁻ 43 (q87 c4) ∷
   rw 44 (q86 c4) ∷
   rw 45 (q65 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q81 c4) ∷
   rw 6 (q69 c4) ∷
   rw 7 (q85 c4) ∷
   rw 8 (q69 c4) ∷
   rw 9 (q85 c4) ∷
   rw 10 (q69 c4) ∷
   rw 11 (q96 c4) ∷
   rw 12 (q96 c4) ∷
   rw 13 (q96 c4) ∷
   rw 14 (q81 c4) ∷
   rw 15 (q95 c4) ∷
   rw 16 (q96 c4) ∷
   rw 17 (q96 c4) ∷
   rw 18 (q95 c4) ∷
   rw 19 (q81 c4) ∷
   rw 20 (q95 c4) ∷
   rw 21 (q96 c4) ∷
   rw 22 (q96 c4) ∷
   rw 23 (q95 c4) ∷
   rw 24 (q81 c4) ∷
   rw 25 (q69 c4) ∷
   rw 26 (q95 c4) ∷
   rw 27 (q96 c4) ∷
   rw 28 (q96 c4) ∷
   rw 29 (q95 c4) ∷
   rw 30 (q81 c4) ∷
   rw 31 (q95 c4) ∷
   rw 32 (q96 c4) ∷
   rw 33 (q96 c4) ∷
   rw 34 (q95 c4) ∷
   rw 35 (q81 c4) ∷
   rw 36 (q69 c4) ∷
   rw 37 (q69 c4) ∷
   rw 38 (q69 c4) ∷
   rw 39 (q95 c4) ∷
   rw 40 (q96 c4) ∷
   rw 41 (q96 c4) ∷
   rw 42 (q95 c4) ∷
   rw 43 (q81 c4) ∷
   rw 44 (q64 c4) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q76 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 7 (q70 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw 9 (q70 c4) ∷
   rw 10 (q98 c4) ∷
   rw 11 (q98 c4) ∷
   rw 12 (q98 c4) ∷
   rw 13 (q76 c4) ∷
   rw 14 (q97 c4) ∷
   rw 15 (q98 c4) ∷
   rw 16 (q98 c4) ∷
   rw 17 (q97 c4) ∷
   rw 18 (q76 c4) ∷
   rw 19 (q97 c4) ∷
   rw 20 (q98 c4) ∷
   rw 21 (q98 c4) ∷
   rw 22 (q97 c4) ∷
   rw 23 (q76 c4) ∷
   rw 24 (q70 c4) ∷
   rw 25 (q97 c4) ∷
   rw 26 (q98 c4) ∷
   rw 27 (q98 c4) ∷
   rw 28 (q97 c4) ∷
   rw 29 (q76 c4) ∷
   rw 30 (q97 c4) ∷
   rw 31 (q98 c4) ∷
   rw 32 (q98 c4) ∷
   rw 33 (q97 c4) ∷
   rw 34 (q76 c4) ∷
   rw 35 (q70 c4) ∷
   rw 36 (q70 c4) ∷
   rw 37 (q70 c4) ∷
   rw 38 (q97 c4) ∷
   rw 39 (q98 c4) ∷
   rw 40 (q98 c4) ∷
   rw 41 (q97 c4) ∷
   rw 42 (q76 c4) ∷
   rw 43 (q63 c4) ∷
   rw 0 (q99 c4) ∷
   rw⁻ 42 (q100 c4) ∷
   rw 43 (q101 c4) ∷
   rw 44 (q101 c4) ∷
   rw 45 (q101 c4) ∷
   rw 0 (q102 c4) ∷
   rw⁻ 0 (q103 c4) ∷ []) Eq.refl
