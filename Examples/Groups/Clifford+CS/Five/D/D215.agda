{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD215 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D215 (Sᴰ : SD215) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ134-CX02 : Ws → St 1300
  lem-comm-CCZ134-CX02 = pickᴰ 0 Sᴰ
  lem-comm-TOFF302-CS14 : Ws → St 1360
  lem-comm-TOFF302-CS14 = pickᴰ 1 Sᴰ
  lem-comm-TOFF302-CSd14 : Ws → St 339
  lem-comm-TOFF302-CSd14 = pickᴰ 2 Sᴰ
  lem-comm-TOFF302-CX14 : Ws → St 1361
  lem-comm-TOFF302-CX14 = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R : Ws → St 2009
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R : Ws → St 2010
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-TR2-1b52048e : Ws → St 2109
  lem-TR2-1b52048e = pickᴰ 6 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 7 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 8 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 9 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 10 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 11 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 12 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 13 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 14 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 15 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 16 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 17 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 18 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 19 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 20 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 21 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 22 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 23 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 24 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 25 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 26 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 27 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 28 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 29 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 30 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 31 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 32 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 33 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 34 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 35 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 36 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 37 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 38 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 39 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 40 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 41 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 42 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 43 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 44 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 45 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 46 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 47 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 48 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 49 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 50 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 51 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 52 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 53 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 54 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 55 Sᴰ
  lem-box2-at03243240 : Ws → St 1341
  lem-box2-at03243240 = pickᴰ 56 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 57 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 58 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 59 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 60 Sᴰ
  lem-CKc-box-at0312203441 : Ws → St 2142
  lem-CKc-box-at0312203441 = pickᴰ 61 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 62 Sᴰ
  lem-S2-SBOX⟨3·0·41·2⟩ : Ws → St 2091
  lem-S2-SBOX⟨3·0·41·2⟩ = pickᴰ 63 Sᴰ
  lem-S2-SBOX⟨3·1·42·0⟩ : Ws → St 2092
  lem-S2-SBOX⟨3·1·42·0⟩ = pickᴰ 64 Sᴰ
  lem-box-perm-3421-at03243240 : Ws → St 2144
  lem-box-perm-3421-at03243240 = pickᴰ 65 Sᴰ
  lem-box-perm-4312-at0312203441 : Ws → St 2145
  lem-box-perm-4312-at0312203441 = pickᴰ 66 Sᴰ
  lem-L-CCZ-0-part2 : Ws → St 2149
  lem-L-CCZ-0-part2 = pickᴰ 67 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 68 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 69 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 70 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 71 Sᴰ
  lem-L-CCZ-0-part1 : Ws → St 2150
  lem-L-CCZ-0-part1 = pickᴰ 72 Sᴰ
  lem-L-CCZ-0-part3 : Ws → St 2151
  lem-L-CCZ-0-part3 = pickᴰ 73 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 74 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 75 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 76 Sᴰ
  lem-F1-comm-CSu-CSat1 : Ws → St 2152
  lem-F1-comm-CSu-CSat1 = pickᴰ 77 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 78 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 79 Sᴰ
  lem-F0-at01143043 : Ws → St 2086
  lem-F0-at01143043 = pickᴰ 80 Sᴰ
  lem-F0-at14213243 : Ws → St 2087
  lem-F0-at14213243 = pickᴰ 81 Sᴰ
  lem-deb-Q-hi : Ws → St 2117
  lem-deb-Q-hi = pickᴰ 82 Sᴰ
  lem-deb-Q-lo-at132132 : Ws → St 2120
  lem-deb-Q-lo-at132132 = pickᴰ 83 Sᴰ
  lem-nf-rel-268at0 : Ws → St 2153
  lem-nf-rel-268at0 = pickᴰ 84 Sᴰ
  lem-L-CCZ-0-part0 : Ws → St 2154
  lem-L-CCZ-0-part0 = pickᴰ 85 Sᴰ
  lem-deb-P-hi : Ws → St 2155
  lem-deb-P-hi = pickᴰ 86 Sᴰ
  lem-deb-P-hi-at02132031 : Ws → St 2156
  lem-deb-P-hi-at02132031 = pickᴰ 87 Sᴰ
  lem-deb-P-hi-at132132 : Ws → St 2157
  lem-deb-P-hi-at132132 = pickᴰ 88 Sᴰ
  lem-deb-P-lo-at02132031 : Ws → St 2158
  lem-deb-P-lo-at02132031 = pickᴰ 89 Sᴰ
  lem-deb-P-lo-at132132 : Ws → St 2159
  lem-deb-P-lo-at132132 = pickᴰ 90 Sᴰ
  lem-deb-rel-272at1-R : Ws → St 2160
  lem-deb-rel-272at1-R = pickᴰ 91 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2086 (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2087 (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2091 (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2092 (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 1025 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 1026 c4
  q8 : Ws → Eqn
  q8 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q9 : Ws → Eqn
  q9 c4 = wlE 1220 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1300 (lem-comm-CCZ134-CX02 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1221 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 1003 c4
  q13 : Ws → Eqn
  q13 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q14 : Ws → Eqn
  q14 c4 = wlE 1206 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 1007 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 220 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 1006 c4
  q18 : Ws → Eqn
  q18 c4 = sE 1361 (lem-comm-TOFF302-CX14 c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 1005 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 1190 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 1008 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 1222 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 1223 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 261 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 1224 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 1027 c4
  q27 : Ws → Eqn
  q27 c4 = sE 2144 (lem-box-perm-3421-at03243240 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 2142 (lem-CKc-box-at0312203441 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 2145 (lem-box-perm-4312-at0312203441 c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 301 c4
  q31 : Ws → Eqn
  q31 c4 = sE 1360 (lem-comm-TOFF302-CS14 c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 1233 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = sE 339 (lem-comm-TOFF302-CSd14 c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 1041 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 272 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 1111 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 1249 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1251 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 391 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wlE 393 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 392 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1341 (lem-box2-at03243240 c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 1042 c4
  q44 : Ws → Eqn
  q44 c4 = wlE 263 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 1123 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 341 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 167 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 1124 c4
  q49 : Ws → Eqn
  q49 c4 = wpE 743 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 1125 c4
  q51 : Ws → Eqn
  q51 c4 = sE 2153 (lem-nf-rel-268at0 c4)

-- F1-rel-268@0: 484 steps
lem-F1-rel-268at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268at0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw 8 (q3 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   re 10 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 12 1 (CS01 ∷ []) ∷
   re 14 1 (CS01⁻ ∷ []) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 13 (q15 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 16 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 13 (q8 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q12 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw 19 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw 23 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 24 (q33 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw⁻ 21 (q35 c4) ∷
   rw 21 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw 22 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw⁻ 19 (q35 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q27 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw 25 (q37 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw 23 (q37 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 3 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 6 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 6 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 9 (q5 c4) ∷
   rw 13 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 14 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 16 (q34 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw⁻ 11 (q35 c4) ∷
   rw 11 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 12 (q33 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 10 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw 18 (q15 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q10 c4) ∷
   rw 26 (q12 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q14 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 22 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw 26 (q18 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 20 (q21 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q12 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 22 (q26 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q38 c4) ∷
   rw 26 (q39 c4) ∷
   rw 25 (q40 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q41 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q24 c4) ∷
   rw⁻ 25 (q39 c4) ∷
   rw⁻ 24 (q38 c4) ∷
   rw 24 (q39 c4) ∷
   rw 23 (q40 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q41 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 23 (q39 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 24 (q27 c4) ∷
   rw 24 (q28 c4) ∷
   rw 27 (q29 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 30 (q38 c4) ∷
   rw 30 (q39 c4) ∷
   rw 29 (q40 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q41 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 28 (q38 c4) ∷
   rw 28 (q39 c4) ∷
   rw 27 (q40 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q41 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q24 c4) ∷
   rw⁻ 27 (q39 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw 32 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw 33 (q33 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw⁻ 31 (q30 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw 30 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw 31 (q33 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 32 (q38 c4) ∷
   rw 32 (q39 c4) ∷
   rw 31 (q40 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q41 c4) ∷
   rw 34 (q10 c4) ∷
   rw 35 (q24 c4) ∷
   rw⁻ 31 (q39 c4) ∷
   rw⁻ 30 (q38 c4) ∷
   rw 30 (q39 c4) ∷
   rw 29 (q40 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q41 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 30 (q27 c4) ∷
   rw 30 (q28 c4) ∷
   rw 33 (q29 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 36 (q38 c4) ∷
   rw 36 (q39 c4) ∷
   rw 35 (q40 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q41 c4) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q24 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw⁻ 34 (q38 c4) ∷
   rw 34 (q39 c4) ∷
   rw 33 (q40 c4) ∷
   rw 34 (q10 c4) ∷
   rw 35 (q41 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q24 c4) ∷
   rw⁻ 33 (q39 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 37 (q36 c4) ∷
   rw 36 (q37 c4) ∷
   rw⁻ 35 (q36 c4) ∷
   rw 34 (q37 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 35 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q46 c4) ∷
   rw 7 (q48 c4) ∷
   rw 17 (q46 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q44 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 15 (q46 c4) ∷
   rw 16 (q46 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 2154 (lem-L-CCZ-0-part0 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 2150 (lem-L-CCZ-0-part1 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 2149 (lem-L-CCZ-0-part2 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 2151 (lem-L-CCZ-0-part3 c4)

-- L-CCZ-0: 4 steps
lem-L-CCZ-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-L-CCZ-0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = sE 2156 (lem-deb-P-hi-at02132031 c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 1264 c4

-- F1-CS-K0@0: 3 steps
lem-F1-CS-K0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at0 c4 = derive (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 2 (q56 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = sE 2157 (lem-deb-P-hi-at132132 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q60 : Ws → Eqn
  q60 c4 = wpE 1266 c4
  q61 : Ws → Eqn
  q61 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)

-- F1-CS-K0@1: 7 steps
lem-F1-CS-K0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at1 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw 35 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 18 (q61 c4) ∷
   rw 37 (q61 c4) ∷
   rw⁻ 2 (q58 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = sE 2158 (lem-deb-P-lo-at02132031 c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 1268 c4

-- F1-CS-K1@0: 3 steps
lem-F1-CS-K1at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1at0 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 2 (q62 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = sE 2159 (lem-deb-P-lo-at132132 c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 1269 c4

-- F1-CS-K1@1: 7 steps
lem-F1-CS-K1at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1at1 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 16 (q59 c4) ∷
   rw 35 (q59 c4) ∷
   rw 0 (q65 c4) ∷
   rw 18 (q61 c4) ∷
   rw 37 (q61 c4) ∷
   rw⁻ 2 (q64 c4) ∷ []) Eq.refl

-- deb-rel-269@0-R: 2 steps
lem-deb-rel-269at0-R : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-rel-269at0-R c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 42 (q58 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = sE 2155 (lem-deb-P-hi c4)

-- deb-rel-269@1-R: 2 steps
lem-deb-rel-269at1-R : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-rel-269at1-R c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 42 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wlE 3 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 6 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = sE 2109 (lem-TR2-1b52048e c4)
  q70 : Ws → Eqn
  q70 c4 = sE 2010 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R c4)
  q71 : Ws → Eqn
  q71 c4 = sE 2009 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R c4)
  q72 : Ws → Eqn
  q72 c4 = sE 2117 (lem-deb-Q-hi c4)
  q73 : Ws → Eqn
  q73 c4 = sE 2120 (lem-deb-Q-lo-at132132 c4)
  q74 : Ws → Eqn
  q74 c4 = sE 2152 (lem-F1-comm-CSu-CSat1 c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 1273 c4
  q76 : Ws → Eqn
  q76 c4 = sE 2160 (lem-deb-rel-272at1-R c4)

-- F1-rel-272@1: 26 steps
lem-F1-rel-272at1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-272at1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 8 (q67 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 10 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw 10 (q70 c4) ∷
   rw 11 (q70 c4) ∷
   rw 12 (q70 c4) ∷
   rw 13 (q68 c4) ∷
   rw 8 (q71 c4) ∷
   rw 9 (q71 c4) ∷
   rw 10 (q71 c4) ∷
   rw 11 (q71 c4) ∷
   rw 12 (q67 c4) ∷
   rw 0 (q72 c4) ∷
   rw 33 (q73 c4) ∷
   rw⁻ 65 (q74 c4) ∷
   rw 9 (q59 c4) ∷
   rw 28 (q59 c4) ∷
   rw 42 (q59 c4) ∷
   rw 61 (q59 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 9 (q61 c4) ∷
   rw 28 (q61 c4) ∷
   rw 42 (q61 c4) ∷
   rw 61 (q61 c4) ∷
   rw⁻ 0 (q76 c4) ∷ []) Eq.refl
