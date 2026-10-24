{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD200 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D200 (Sᴰ : SD200) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-TR2-e425e28a : Ws → St 2045
  lem-TR2-e425e28a = pickᴰ 0 Sᴰ
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 1 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 2 Sᴰ
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 3 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 4 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 5 Sᴰ
  lem-F4-K3-S2 : Ws → St 1619
  lem-F4-K3-S2 = pickᴰ 6 Sᴰ
  lem-F4-S2-I : Ws → St 1597
  lem-F4-S2-I = pickᴰ 7 Sᴰ
  lem-F4-S2-K3 : Ws → St 1598
  lem-F4-S2-K3 = pickᴰ 8 Sᴰ
  lem-F4-S2-S2 : Ws → St 1599
  lem-F4-S2-S2 = pickᴰ 9 Sᴰ
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
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 52 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 53 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 54 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1607
  lem-F4-S2-CS2 = pickᴰ 55 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 56 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 57 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 58 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 59 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 60 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 61 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 62 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 63 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 64 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 65 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 66 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 67 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 68 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 69 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 70 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 71 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 72 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 73 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 74 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 75 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 76 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 77 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 78 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 79 Sᴰ
  lem-deb-CKS-eps : Ws → St 2046
  lem-deb-CKS-eps = pickᴰ 80 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2045 (lem-TR2-e425e28a c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2046 (lem-deb-CKS-eps c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1607 (lem-F4-S2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1411 (lem-F4-I-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1598 (lem-F4-S2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1595 (lem-F4-I-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1599 (lem-F4-S2-S2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1606 (lem-F4-CS2-S2 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1619 (lem-F4-K3-S2 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1386 (lem-F4-I-I c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1597 (lem-F4-S2-I c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1576 (lem-F4-CS2-I c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1618 (lem-F4-K3-I c4)

-- deb-CKS part0: 175 steps
lem-deb-CKS-part0 : Ws → ⟪ (ℓ "侬亊侬亊侬乩乩乩丢侬") ⟫ʷ ≈ ⟪ (ℓ "亰並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬亊侬亊侬乩乩乩丢並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並乩並丢並侬侬侬侬亊侬亊侬乩乩乩丢乩乹乹乹侬亊侬亊侬乩乩乩丢侬侬亊侬亊侬乩乩乩丢乹") ⟫ʷ
lem-deb-CKS-part0 c4 = derive (ℓ "侬亊侬亊侬乩乩乩丢侬") (ℓ "亰並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬亊侬亊侬乩乩乩丢並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並乩並丢並侬侬侬侬亊侬亊侬乩乩乩丢乩乹乹乹侬亊侬亊侬乩乩乩丢侬侬亊侬亊侬乩乩乩丢乹")
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw 124 (q4 c4) ∷
   rw 121 (q5 c4) ∷
   rw 118 (q5 c4) ∷
   rw 115 (q5 c4) ∷
   rw 112 (q6 c4) ∷
   rw 109 (q7 c4) ∷
   rw 106 (q6 c4) ∷
   rw 103 (q7 c4) ∷
   rw 100 (q6 c4) ∷
   rw 97 (q6 c4) ∷
   rw 94 (q4 c4) ∷
   rw 91 (q5 c4) ∷
   rw 88 (q5 c4) ∷
   rw 85 (q5 c4) ∷
   rw 82 (q6 c4) ∷
   rw 79 (q7 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q7 c4) ∷
   rw 70 (q6 c4) ∷
   rw 125 (q8 c4) ∷
   rw 122 (q9 c4) ∷
   rw 119 (q9 c4) ∷
   rw 116 (q9 c4) ∷
   rw 113 (q10 c4) ∷
   rw 110 (q11 c4) ∷
   rw 107 (q10 c4) ∷
   rw 104 (q11 c4) ∷
   rw 101 (q10 c4) ∷
   rw 98 (q10 c4) ∷
   rw 95 (q8 c4) ∷
   rw 92 (q9 c4) ∷
   rw 89 (q9 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q10 c4) ∷
   rw 80 (q11 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q11 c4) ∷
   rw 71 (q10 c4) ∷
   rw 126 (q4 c4) ∷
   rw 123 (q5 c4) ∷
   rw 120 (q5 c4) ∷
   rw 117 (q5 c4) ∷
   rw 114 (q6 c4) ∷
   rw 111 (q7 c4) ∷
   rw 108 (q6 c4) ∷
   rw 105 (q7 c4) ∷
   rw 102 (q6 c4) ∷
   rw 99 (q6 c4) ∷
   rw 96 (q4 c4) ∷
   rw 93 (q5 c4) ∷
   rw 90 (q5 c4) ∷
   rw 87 (q5 c4) ∷
   rw 84 (q6 c4) ∷
   rw 81 (q7 c4) ∷
   rw 78 (q6 c4) ∷
   rw 75 (q7 c4) ∷
   rw 72 (q6 c4) ∷
   rw 127 (q8 c4) ∷
   rw 124 (q9 c4) ∷
   rw 121 (q9 c4) ∷
   rw 118 (q9 c4) ∷
   rw 115 (q10 c4) ∷
   rw 112 (q11 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q10 c4) ∷
   rw 100 (q10 c4) ∷
   rw 97 (q8 c4) ∷
   rw 94 (q9 c4) ∷
   rw 91 (q9 c4) ∷
   rw 88 (q9 c4) ∷
   rw 85 (q10 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q10 c4) ∷
   rw 76 (q11 c4) ∷
   rw 73 (q10 c4) ∷
   rw 128 (q4 c4) ∷
   rw 125 (q5 c4) ∷
   rw 122 (q5 c4) ∷
   rw 119 (q5 c4) ∷
   rw 116 (q6 c4) ∷
   rw 113 (q7 c4) ∷
   rw 110 (q6 c4) ∷
   rw 107 (q7 c4) ∷
   rw 104 (q6 c4) ∷
   rw 101 (q6 c4) ∷
   rw 98 (q4 c4) ∷
   rw 95 (q5 c4) ∷
   rw 92 (q5 c4) ∷
   rw 89 (q5 c4) ∷
   rw 86 (q6 c4) ∷
   rw 83 (q7 c4) ∷
   rw 80 (q6 c4) ∷
   rw 77 (q7 c4) ∷
   rw 74 (q6 c4) ∷
   rw 129 (q12 c4) ∷
   rw 126 (q13 c4) ∷
   rw 123 (q13 c4) ∷
   rw 120 (q13 c4) ∷
   rw 117 (q14 c4) ∷
   rw 114 (q15 c4) ∷
   rw 111 (q14 c4) ∷
   rw 108 (q15 c4) ∷
   rw 105 (q14 c4) ∷
   rw 102 (q14 c4) ∷
   rw 99 (q12 c4) ∷
   rw 96 (q13 c4) ∷
   rw 93 (q13 c4) ∷
   rw 90 (q13 c4) ∷
   rw 87 (q14 c4) ∷
   rw 84 (q15 c4) ∷
   rw 81 (q14 c4) ∷
   rw 78 (q15 c4) ∷
   rw 75 (q14 c4) ∷
   rw 130 (q12 c4) ∷
   rw 127 (q13 c4) ∷
   rw 124 (q13 c4) ∷
   rw 121 (q13 c4) ∷
   rw 118 (q14 c4) ∷
   rw 115 (q15 c4) ∷
   rw 112 (q14 c4) ∷
   rw 109 (q15 c4) ∷
   rw 106 (q14 c4) ∷
   rw 103 (q14 c4) ∷
   rw 100 (q12 c4) ∷
   rw 97 (q13 c4) ∷
   rw 94 (q13 c4) ∷
   rw 91 (q13 c4) ∷
   rw 88 (q14 c4) ∷
   rw 85 (q15 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q15 c4) ∷
   rw 76 (q14 c4) ∷
   rw 131 (q12 c4) ∷
   rw 128 (q13 c4) ∷
   rw 125 (q13 c4) ∷
   rw 122 (q13 c4) ∷
   rw 119 (q14 c4) ∷
   rw 116 (q15 c4) ∷
   rw 113 (q14 c4) ∷
   rw 110 (q15 c4) ∷
   rw 107 (q14 c4) ∷
   rw 104 (q14 c4) ∷
   rw 101 (q12 c4) ∷
   rw 98 (q13 c4) ∷
   rw 95 (q13 c4) ∷
   rw 92 (q13 c4) ∷
   rw 89 (q14 c4) ∷
   rw 86 (q15 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q15 c4) ∷
   rw 77 (q14 c4) ∷
   rw 132 (q16 c4) ∷
   rw 129 (q17 c4) ∷
   rw 126 (q17 c4) ∷
   rw 123 (q17 c4) ∷
   rw 120 (q18 c4) ∷
   rw 117 (q19 c4) ∷
   rw 114 (q18 c4) ∷
   rw 111 (q19 c4) ∷
   rw 108 (q18 c4) ∷
   rw 105 (q18 c4) ∷
   rw 102 (q16 c4) ∷
   rw 99 (q17 c4) ∷
   rw 96 (q17 c4) ∷
   rw 93 (q17 c4) ∷
   rw 90 (q18 c4) ∷
   rw 87 (q19 c4) ∷
   rw 84 (q18 c4) ∷
   rw 81 (q19 c4) ∷
   rw 78 (q18 c4) ∷
   rw 133 (q12 c4) ∷ []) Eq.refl
