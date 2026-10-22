{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD147 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D147 (Sᴰ : SD147) where

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
  lem-comm-push-CK40-sw0-L : Ws → St 1877
  lem-comm-push-CK40-sw0-L = pickᴰ 0 Sᴰ
  lem-comm-push-CS04-sw0-L : Ws → St 1620
  lem-comm-push-CS04-sw0-L = pickᴰ 1 Sᴰ
  lem-comm-push-CS04-sw1-L : Ws → St 1621
  lem-comm-push-CS04-sw1-L = pickᴰ 2 Sᴰ
  lem-comm-push-CK40-sw1-L : Ws → St 1878
  lem-comm-push-CK40-sw1-L = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L : Ws → St 1879
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L : Ws → St 1880
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L : Ws → St 1881
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L : Ws → St 1882
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L = pickᴰ 7 Sᴰ
  lem-TR2-0d166c34 : Ws → St 1883
  lem-TR2-0d166c34 = pickᴰ 8 Sᴰ
  lem-TR2-4726ca8d : Ws → St 1884
  lem-TR2-4726ca8d = pickᴰ 9 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 10 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 11 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 12 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 13 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 14 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 15 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 16 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 17 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 18 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 19 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 20 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 21 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 22 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 23 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 24 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 25 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 26 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 27 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 28 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 29 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 30 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 31 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 32 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 33 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 34 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 35 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 36 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 37 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 38 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 39 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 40 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 41 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 42 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 43 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 44 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 45 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 46 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 47 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 48 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 49 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 50 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 51 Sᴰ
  lem-CXAu-S : Ws → St 1927
  lem-CXAu-S = pickᴰ 52 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 53 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 54 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 55 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 56 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 57 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 58 Sᴰ
  lem-CXAu-S-at14213243 : Ws → St 1934
  lem-CXAu-S-at14213243 = pickᴰ 59 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 60 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 61 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 62 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 63 Sᴰ
  lem-CXAu-S-at01143043 : Ws → St 1939
  lem-CXAu-S-at01143043 = pickᴰ 64 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 65 Sᴰ
  lem-L-CCZ-1-part2 : Ws → St 1941
  lem-L-CCZ-1-part2 = pickᴰ 66 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 67 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 68 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 69 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 70 Sᴰ
  lem-L-CCZ-1-part1 : Ws → St 1946
  lem-L-CCZ-1-part1 = pickᴰ 71 Sᴰ
  lem-L-CCZ-1-part3 : Ws → St 1947
  lem-L-CCZ-1-part3 = pickᴰ 72 Sᴰ
  lem-CXuA-S : Ws → St 1948
  lem-CXuA-S = pickᴰ 73 Sᴰ
  lem-CXuA-S-at14213243 : Ws → St 1949
  lem-CXuA-S-at14213243 = pickᴰ 74 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 75 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 76 Sᴰ
  lem-CXuA-S-at01143043 : Ws → St 1952
  lem-CXuA-S-at01143043 = pickᴰ 77 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 78 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 79 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 80 Sᴰ
  lem-L-CCZ-1-part0 : Ws → St 1956
  lem-L-CCZ-1-part0 = pickᴰ 81 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 547 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1948 (lem-CXuA-S c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1927 (lem-CXAu-S c4)

-- SW-S: 5 steps
lem-SW-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-SW-S c4 = derive (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = wlE 258 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1949 (lem-CXuA-S-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1934 (lem-CXAu-S-at14213243 c4)

-- SW-S @14213243: 5 steps
lem-SW-S-at14213243 : Ws → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at14213243 c4 = derive (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q4 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 961 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1952 (lem-CXuA-S-at01143043 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1939 (lem-CXAu-S-at01143043 c4)

-- SW-S @01143043: 5 steps
lem-SW-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ
lem-SW-S-at01143043 c4 = derive (Sw03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = sE 1956 (lem-L-CCZ-1-part0 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1946 (lem-L-CCZ-1-part1 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1941 (lem-L-CCZ-1-part2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1947 (lem-L-CCZ-1-part3 c4)

-- L-CCZ-1: 4 steps
lem-L-CCZ-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-L-CCZ-1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wlE 1083 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1883 (lem-TR2-0d166c34 c4)

-- deb-P-hi-eps: 28 steps
lem-deb-P-hi-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = wlE 6 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1882 (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q19 : Ws → Eqn
  q19 c4 = wlE 13 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1878 (lem-comm-push-CK40-sw1-L c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 18 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1881 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q25 : Ws → Eqn
  q25 c4 = sE 1877 (lem-comm-push-CK40-sw0-L c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 3 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1879 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q29 : Ws → Eqn
  q29 c4 = wlE 11 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 99 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1880 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q33 : Ws → Eqn
  q33 c4 = wlE 87 (lit c4)

-- deb-P-hi-eps @02132031: 144 steps
lem-deb-P-hi-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
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
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw 22 (q22 c4) ∷
   rw 21 (q25 c4) ∷
   rw 20 (q22 c4) ∷
   rw 19 (q25 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw 12 (q22 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q22 c4) ∷
   rw 9 (q25 c4) ∷
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
   rw⁻ 27 (q32 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw 23 (q33 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw 13 (q33 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

-- deb-P-hi-eps @132132: 86 steps
lem-deb-P-hi-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 28 (q26 c4) ∷
   rw 27 (q27 c4) ∷
   rw 26 (q27 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q29 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q30 c4) ∷
   rw 17 (q27 c4) ∷
   rw 16 (q29 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q29 c4) ∷
   rw 12 (q29 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw 28 (q31 c4) ∷
   rw 27 (q31 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q33 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = sE 1884 (lem-TR2-4726ca8d c4)

-- deb-P-lo-eps: 28 steps
lem-deb-P-lo-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = sE 1621 (lem-comm-push-CS04-sw1-L c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q38 : Ws → Eqn
  q38 c4 = wlE 17 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 90 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))

-- deb-P-lo-eps @02132031: 144 steps
lem-deb-P-lo-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 24 (q35 c4) ∷
   rw 23 (q35 c4) ∷
   rw 22 (q35 c4) ∷
   rw 21 (q17 c4) ∷
   rw 20 (q33 c4) ∷
   rw 19 (q17 c4) ∷
   rw 18 (q33 c4) ∷
   rw 17 (q17 c4) ∷
   rw 16 (q35 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 14 (q35 c4) ∷
   rw 13 (q35 c4) ∷
   rw 12 (q35 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q33 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q33 c4) ∷
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
   rw 25 (q36 c4) ∷
   rw 24 (q36 c4) ∷
   rw 23 (q36 c4) ∷
   rw 22 (q22 c4) ∷
   rw⁻ 21 (q37 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw 18 (q22 c4) ∷
   rw 17 (q36 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q36 c4) ∷
   rw 14 (q36 c4) ∷
   rw 13 (q36 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 11 (q37 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 9 (q37 c4) ∷
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
   rw 26 (q38 c4) ∷
   rw 25 (q38 c4) ∷
   rw 24 (q38 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q39 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q39 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q38 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 16 (q38 c4) ∷
   rw 15 (q38 c4) ∷
   rw 14 (q38 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q39 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q39 c4) ∷
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
   rw 27 (q19 c4) ∷
   rw 26 (q19 c4) ∷
   rw 25 (q19 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q40 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 21 (q40 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q19 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 17 (q19 c4) ∷
   rw 16 (q19 c4) ∷
   rw 15 (q19 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q40 c4) ∷
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
   rw 0 (q14 c4) ∷ []) Eq.refl
