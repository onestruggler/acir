{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD189 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D189 (Sᴰ : SD189) where

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
  lem-TR2-570a2ddc : Ws → St 1996
  lem-TR2-570a2ddc = pickᴰ 0 Sᴰ
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 1 Sᴰ
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 2 Sᴰ
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 3 Sᴰ
  lem-F4-I-S3 : Ws → St 1564
  lem-F4-I-S3 = pickᴰ 4 Sᴰ
  lem-F4-K2-I : Ws → St 1809
  lem-F4-K2-I = pickᴰ 5 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 6 Sᴰ
  lem-F4-K2-S2 : Ws → St 1767
  lem-F4-K2-S2 = pickᴰ 7 Sᴰ
  lem-F4-K2-S3 : Ws → St 1997
  lem-F4-K2-S3 = pickᴰ 8 Sᴰ
  lem-F4-S3-I : Ws → St 1566
  lem-F4-S3-I = pickᴰ 9 Sᴰ
  lem-F4-S3-K2 : Ws → St 1567
  lem-F4-S3-K2 = pickᴰ 10 Sᴰ
  lem-F4-S3-S2 : Ws → St 1770
  lem-F4-S3-S2 = pickᴰ 11 Sᴰ
  lem-F4-S3-S3 : Ws → St 1568
  lem-F4-S3-S3 = pickᴰ 12 Sᴰ
  lem-nat-S : Ws → St 1998
  lem-nat-S = pickᴰ 13 Sᴰ
  lem-nat-S-at14213243 : Ws → St 1999
  lem-nat-S-at14213243 = pickᴰ 14 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 15 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 16 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 17 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 18 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 19 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 20 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 21 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 22 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 23 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 24 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 25 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 26 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 27 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 28 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 29 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 30 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 31 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 32 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 33 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 34 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 35 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 36 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 37 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 38 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 39 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 40 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 41 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 42 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 43 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 44 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 45 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 46 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 47 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 48 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 49 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 50 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 51 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 52 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 53 Sᴰ
  lem-nat-S-at01143043 : Ws → St 2000
  lem-nat-S-at01143043 = pickᴰ 54 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 55 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 56 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 57 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 58 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 59 Sᴰ
  lem-F4-CS2-S3 : Ws → St 1577
  lem-F4-CS2-S3 = pickᴰ 60 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 61 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 62 Sᴰ
  lem-F4-S3-CS2 : Ws → St 1579
  lem-F4-S3-CS2 = pickᴰ 63 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 64 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 65 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 66 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 67 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 68 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 69 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 70 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 71 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 72 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 73 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 74 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 75 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 76 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 77 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 78 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 79 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 80 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 81 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 82 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 83 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 84 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 85 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 86 Sᴰ
  lem-SW-S : Ws → St 2001
  lem-SW-S = pickᴰ 87 Sᴰ
  lem-SW-S-at01143043 : Ws → St 2002
  lem-SW-S-at01143043 = pickᴰ 88 Sᴰ
  lem-SW-S-at14213243 : Ws → St 2003
  lem-SW-S-at14213243 = pickᴰ 89 Sᴰ
  lem-deb-P-hi-eps : Ws → St 2004
  lem-deb-P-hi-eps = pickᴰ 90 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 4 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2001 (lem-SW-S c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1998 (lem-nat-S c4)

-- F0: 3 steps
lem-F0 : Ws → ⟪ (ℓ "俐") ⟫ʷ ≈ ⟪ (ℓ "俢") ⟫ʷ
lem-F0 c4 = derive (ℓ "俐") (ℓ "俢")
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = wlE 3 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2003 (lem-SW-S-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1999 (lem-nat-S-at14213243 c4)

-- F0 @14213243: 3 steps
lem-F0-at14213243 : Ws → ⟪ (ℓ "俄") ⟫ʷ ≈ ⟪ (ℓ "俖") ⟫ʷ
lem-F0-at14213243 c4 = derive (ℓ "俄") (ℓ "俖")
  (rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 928 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2002 (lem-SW-S-at01143043 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2000 (lem-nat-S-at01143043 c4)

-- F0 @01143043: 3 steps
lem-F0-at01143043 : Ws → ⟪ (ℓ "侧") ⟫ʷ ≈ ⟪ (ℓ "俜") ⟫ʷ
lem-F0-at01143043 c4 = derive (ℓ "侧") (ℓ "俜")
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = sE 1996 (lem-TR2-570a2ddc c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q12 : Ws → Eqn
  q12 c4 = sE 2004 (lem-deb-P-hi-eps c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1579 (lem-F4-S3-CS2 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1410 (lem-F4-I-K2 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1567 (lem-F4-S3-K2 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1565 (lem-F4-K2-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1577 (lem-F4-CS2-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1564 (lem-F4-I-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1568 (lem-F4-S3-S3 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1997 (lem-F4-K2-S3 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1576 (lem-F4-CS2-I c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1386 (lem-F4-I-I c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1566 (lem-F4-S3-I c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1809 (lem-F4-K2-I c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1606 (lem-F4-CS2-S2 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1595 (lem-F4-I-S2 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1770 (lem-F4-S3-S2 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1767 (lem-F4-K2-S2 c4)

-- deb-P-hi part0: 248 steps
lem-deb-P-hi-part0 : Ws → ⟪ (ℓ "侬亇侬") ⟫ʷ ≈ ⟪ (ℓ "亇亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並並丢並並乹並侬侬侬侬侬侬侬亇侬亇侬乹乹乹丢乹乩乩乩乩乩乩並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並乩並丢並並侬並並侬並乩乩侬亇侬亇侬乹乹乹丢侬侬乩乩乩") ⟫ʷ
lem-deb-P-hi-part0 c4 = derive (ℓ "侬亇侬") (ℓ "亇亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並並丢並並乹並侬侬侬侬侬侬侬亇侬亇侬乹乹乹丢乹乩乩乩乩乩乩並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並乩並丢並並侬並並侬並乩乩侬亇侬亇侬乹乹乹丢侬侬乩乩乩")
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
