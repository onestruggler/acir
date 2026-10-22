{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD149 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D149 (Sᴰ : SD149) where

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
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L : Ws → St 1879
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L : Ws → St 1880
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L = pickᴰ 1 Sᴰ
  lem-TR2-fed8f7c9 : Ws → St 1958
  lem-TR2-fed8f7c9 = pickᴰ 2 Sᴰ
  lem-TR2-11f6930f : Ws → St 1957
  lem-TR2-11f6930f = pickᴰ 3 Sᴰ
  lem-TR2-4726ca8d : Ws → St 1884
  lem-TR2-4726ca8d = pickᴰ 4 Sᴰ
  lem-TR2-8fc9546c : Ws → St 1967
  lem-TR2-8fc9546c = pickᴰ 5 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 6 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 7 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 8 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 9 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 10 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 11 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 12 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 13 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 14 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 15 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 16 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 17 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 18 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 19 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 20 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 21 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 22 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 23 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 24 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 25 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 26 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 27 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 28 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 29 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 30 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 31 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 32 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 33 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 34 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 35 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 36 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 37 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 38 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 39 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 40 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 41 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 42 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 43 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 44 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 45 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 46 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 47 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 48 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 49 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 50 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 51 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 52 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 53 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 54 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 55 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 56 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 57 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 58 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 59 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 60 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 61 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 62 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 63 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 64 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 65 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 66 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 67 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 1083 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 3 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q4 : Ws → Eqn
  q4 c4 = wlE 11 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1879 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 99 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 6 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q10 : Ws → Eqn
  q10 c4 = sE 1880 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 87 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1958 (lem-TR2-fed8f7c9 c4)

-- deb-Q-hi-eps @132132: 62 steps
lem-deb-Q-hi-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-hi-eps-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 18 (q4 c4) ∷
   rw 17 (q4 c4) ∷
   rw 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 13 (q5 c4) ∷
   rw 12 (q6 c4) ∷
   rw 11 (q5 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 8 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = wlE 17 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 90 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 13 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q17 : Ws → Eqn
  q17 c4 = sE 1957 (lem-TR2-11f6930f c4)

-- deb-Q-lo-eps @132132: 62 steps
lem-deb-Q-lo-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-Q-lo-eps-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 18 (q13 c4) ∷
   rw 17 (q13 c4) ∷
   rw 16 (q13 c4) ∷
   rw 15 (q5 c4) ∷
   rw 14 (q14 c4) ∷
   rw 13 (q5 c4) ∷
   rw 12 (q14 c4) ∷
   rw 11 (q5 c4) ∷
   rw 10 (q13 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 8 (q13 c4) ∷
   rw 7 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw 5 (q5 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw 19 (q15 c4) ∷
   rw 18 (q15 c4) ∷
   rw 17 (q15 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 12 (q10 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 9 (q15 c4) ∷
   rw 8 (q15 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = sE 1884 (lem-TR2-4726ca8d c4)

-- deb-AD-eps: 28 steps
lem-deb-AD-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-AD-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 1 (q18 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 1967 (lem-TR2-8fc9546c c4)

-- deb-CKS-eps: 43 steps
lem-deb-CKS-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-CKS-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
  (rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 23 (q1 c4) ∷
   rw 24 (q1 c4) ∷
   rw 25 (q1 c4) ∷
   rw 26 (q1 c4) ∷
   rw 27 (q1 c4) ∷
   rw 28 (q1 c4) ∷
   rw 29 (q1 c4) ∷
   rw 30 (q1 c4) ∷
   rw 31 (q1 c4) ∷
   rw 32 (q1 c4) ∷
   rw 33 (q1 c4) ∷
   rw 34 (q1 c4) ∷
   rw 35 (q1 c4) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 1 (q19 c4) ∷
   rw 0 (q1 c4) ∷ []) Eq.refl
