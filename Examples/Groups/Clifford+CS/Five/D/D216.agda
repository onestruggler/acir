{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD216 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D216 (Sᴰ : SD216) where

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
  lem-comm-push-CS04-sw0-L : Ws → St 1620
  lem-comm-push-CS04-sw0-L = pickᴰ 0 Sᴰ
  lem-comm-push-CS14-sw0-R : Ws → St 2008
  lem-comm-push-CS14-sw0-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : Ws → St 1623
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L : Ws → St 1968
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R : Ws → St 1624
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L : Ws → St 1969
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L : Ws → St 1970
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R : Ws → St 1625
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R : Ws → St 1626
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : Ws → St 1627
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R = pickᴰ 9 Sᴰ
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L : Ws → St 1971
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L = pickᴰ 10 Sᴰ
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : Ws → St 1628
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R = pickᴰ 11 Sᴰ
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L : Ws → St 1972
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L = pickᴰ 12 Sᴰ
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L : Ws → St 1973
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L = pickᴰ 13 Sᴰ
  lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L : Ws → St 1974
  lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L = pickᴰ 14 Sᴰ
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : Ws → St 1629
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R = pickᴰ 15 Sᴰ
  lem-TR2-78b381c2 : Ws → St 2161
  lem-TR2-78b381c2 = pickᴰ 16 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 17 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 18 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 19 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 20 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 21 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 22 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 23 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 24 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 25 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 26 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 27 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 28 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 29 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 30 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 31 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 32 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 33 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 34 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 35 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 36 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 37 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 38 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 39 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 40 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 41 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 42 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 43 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 44 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 45 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 46 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 47 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 48 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 49 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 50 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 51 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 52 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 53 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 54 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 55 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 56 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 57 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 58 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 59 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 60 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 61 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 62 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 63 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 64 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 65 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 66 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 67 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 68 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 69 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 70 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 71 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 72 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 73 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 74 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 75 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 76 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 77 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 78 Sᴰ
  lem-deb-CKS-at0213243140 : Ws → St 2162
  lem-deb-CKS-at0213243140 = pickᴰ 79 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 1423 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 18 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1424 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1974 (lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1425 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 6 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1426 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 13 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1968 (lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (c₂ (Swap) (S))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = sE 1973 (lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1427 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 3 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 1428 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 11 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1971 (lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q21 : Ws → Eqn
  q21 c4 = sE 1970 (lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 95 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 4 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1429 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 129 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1972 (lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q28 : Ws → Eqn
  q28 c4 = wlE 8 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1969 (lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 90 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 2161 (lem-TR2-78b381c2 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1624 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1626 (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1625 (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1628 (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1627 (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1623 (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1629 (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4)
  q39 : Ws → Eqn
  q39 c4 = sE 2008 (lem-comm-push-CS14-sw0-R c4)
  q40 : Ws → Eqn
  q40 c4 = sE 2162 (lem-deb-CKS-at0213243140 c4)

-- ckt-A-R: 191 steps
lem-ckt-A-R : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-ckt-A-R c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw 9 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 8 (q9 c4) ∷
   rw 7 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw 12 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q17 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw 13 (q25 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 10 3 (CK42 ∷ []) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw⁻ 15 (q27 c4) ∷
   rw 14 (q28 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q29 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 14 (q28 c4) ∷
   rw 15 (q27 c4) ∷
   rw 16 (q32 c4) ∷
   rw 17 (q32 c4) ∷
   rw 18 (q32 c4) ∷
   rw 19 (q32 c4) ∷
   rw 20 (q15 c4) ∷
   rw 6 (q33 c4) ∷
   re 8 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 7 (q23 c4) ∷
   rw 8 (q33 c4) ∷
   re 10 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 9 (q23 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw 15 (q33 c4) ∷
   rw 16 (q33 c4) ∷
   rw 17 (q33 c4) ∷
   rw 18 (q33 c4) ∷
   rw 19 (q23 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 9 (q34 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q19 c4) ∷
   rw 14 (q34 c4) ∷
   rw 15 (q34 c4) ∷
   rw 16 (q34 c4) ∷
   rw 17 (q34 c4) ∷
   rw 18 (q7 c4) ∷
   rw 4 (q35 c4) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 (q15 c4) ∷
   rw 6 (q35 c4) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 (q15 c4) ∷
   rw 8 (q35 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 13 (q35 c4) ∷
   rw 14 (q35 c4) ∷
   rw 15 (q35 c4) ∷
   rw 16 (q35 c4) ∷
   rw 17 (q15 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q36 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q36 c4) ∷
   rw 13 (q36 c4) ∷
   rw 14 (q36 c4) ∷
   rw 15 (q36 c4) ∷
   rw 16 (q2 c4) ∷
   rw 2 (q37 c4) ∷
   re 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q37 c4) ∷
   re 6 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q37 c4) ∷
   rw 12 (q37 c4) ∷
   rw 13 (q37 c4) ∷
   rw 14 (q37 c4) ∷
   rw 15 (q7 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 5 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q38 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q38 c4) ∷
   rw 14 (q2 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 48 (q1 c4) ∷ []) Eq.refl
