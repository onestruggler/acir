{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD196 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D196 (Sᴰ : SD196) where

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
  lem-comm-push-CS04-sw1-R : Ws → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 0 Sᴰ
  lem-comm-push-CS14-sw0-R : Ws → St 2008
  lem-comm-push-CS14-sw0-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : Ws → St 1840
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L : Ws → St 1879
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L : Ws → St 1880
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R : Ws → St 2009
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R : Ws → St 2010
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L : Ws → St 1881
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : Ws → St 1841
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L : Ws → St 1882
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L = pickᴰ 9 Sᴰ
  lem-TR2-3bdac6c8 : Ws → St 2026
  lem-TR2-3bdac6c8 = pickᴰ 10 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 11 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 12 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 13 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 14 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 15 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 16 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 17 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 18 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 19 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 20 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 21 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 22 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 23 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 24 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 25 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 26 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 27 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 28 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 29 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 30 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 31 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 32 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 33 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 34 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 35 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 36 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 37 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 38 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 39 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 40 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 41 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 42 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 43 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 44 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 45 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 46 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 47 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 48 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 49 Sᴰ
  lem-F4-I-I-at02132031 : Ws → St 1981
  lem-F4-I-I-at02132031 = pickᴰ 50 Sᴰ
  lem-F4-I-K3-at02132031 : Ws → St 1787
  lem-F4-I-K3-at02132031 = pickᴰ 51 Sᴰ
  lem-F4-I-S2-at02132031 : Ws → St 1771
  lem-F4-I-S2-at02132031 = pickᴰ 52 Sᴰ
  lem-F4-I-S3-at02132031 : Ws → St 1570
  lem-F4-I-S3-at02132031 = pickᴰ 53 Sᴰ
  lem-F4-K3-I-at02132031 : Ws → St 1982
  lem-F4-K3-I-at02132031 = pickᴰ 54 Sᴰ
  lem-F4-K3-K3-at02132031 : Ws → St 1789
  lem-F4-K3-K3-at02132031 = pickᴰ 55 Sᴰ
  lem-F4-K3-S2-at02132031 : Ws → St 1983
  lem-F4-K3-S2-at02132031 = pickᴰ 56 Sᴰ
  lem-F4-K3-S3-at02132031 : Ws → St 1959
  lem-F4-K3-S3-at02132031 = pickᴰ 57 Sᴰ
  lem-F4-S2-I-at02132031 : Ws → St 1791
  lem-F4-S2-I-at02132031 = pickᴰ 58 Sᴰ
  lem-F4-S2-K3-at02132031 : Ws → St 1793
  lem-F4-S2-K3-at02132031 = pickᴰ 59 Sᴰ
  lem-F4-S2-S2-at02132031 : Ws → St 1795
  lem-F4-S2-S2-at02132031 = pickᴰ 60 Sᴰ
  lem-F4-S2-S3-at02132031 : Ws → St 1961
  lem-F4-S2-S3-at02132031 = pickᴰ 61 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 62 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 63 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 64 Sᴰ
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
  lem-F4-CS2-CS2-at02132031 : Ws → St 1583
  lem-F4-CS2-CS2-at02132031 = pickᴰ 71 Sᴰ
  lem-F4-CS2-I-at02132031 : Ws → St 1584
  lem-F4-CS2-I-at02132031 = pickᴰ 72 Sᴰ
  lem-F4-CS2-S2-at02132031 : Ws → St 1777
  lem-F4-CS2-S2-at02132031 = pickᴰ 73 Sᴰ
  lem-F4-CS2-S3-at02132031 : Ws → St 1586
  lem-F4-CS2-S3-at02132031 = pickᴰ 74 Sᴰ
  lem-F4-I-CS2-at02132031 : Ws → St 1587
  lem-F4-I-CS2-at02132031 = pickᴰ 75 Sᴰ
  lem-F4-S2-CS2-at02132031 : Ws → St 1797
  lem-F4-S2-CS2-at02132031 = pickᴰ 76 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 77 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 78 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 79 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 80 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 81 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 82 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 83 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 84 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 85 Sᴰ
  lem-F4-CS2-K3-at02132031 : Ws → St 1799
  lem-F4-CS2-K3-at02132031 = pickᴰ 86 Sᴰ
  lem-F4-K3-CS2-at02132031 : Ws → St 1801
  lem-F4-K3-CS2-at02132031 = pickᴰ 87 Sᴰ
  lem-F1-X-CS0at2 : Ws → St 1950
  lem-F1-X-CS0at2 = pickᴰ 88 Sᴰ
  lem-F2-CS0-CS2 : Ws → St 1951
  lem-F2-CS0-CS2 = pickᴰ 89 Sᴰ
  lem-F1-X-CS1at2 : Ws → St 1953
  lem-F1-X-CS1at2 = pickᴰ 90 Sᴰ
  lem-F1-CS-K0at2 : Ws → St 1954
  lem-F1-CS-K0at2 = pickᴰ 91 Sᴰ
  lem-F1-CS-K1at2 : Ws → St 1955
  lem-F1-CS-K1at2 = pickᴰ 92 Sᴰ
  lem-deb-Q-lo-split-a-at02132031 : Ws → St 2034
  lem-deb-Q-lo-split-a-at02132031 = pickᴰ 93 Sᴰ
  lem-deb-Q-lo-split-b-at02132031 : Ws → St 2035
  lem-deb-Q-lo-split-b-at02132031 = pickᴰ 94 Sᴰ
  lem-deb-Q-lo-eps-at02132031 : Ws → St 2036
  lem-deb-Q-lo-eps-at02132031 = pickᴰ 95 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 6 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1882 (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 87 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 18 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1881 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (ℓ "丫亇") (ℓ "亇丫") (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q7 : Ws → Eqn
  q7 c4 = wlE 3 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1879 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 90 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1880 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (ℓ "乊亊") (ℓ "亊乊") (c₃ (Swap ↑) (CK₁₀))
  q12 : Ws → Eqn
  q12 c4 = sE 2026 (lem-TR2-3bdac6c8 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2010 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 13 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (ℓ "乊丢") (ℓ "丢乊") (c₃ (Swap ↑) (S ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (ℓ "乊乹") (ℓ "乹乊") (c₃ (Swap ↑) (CS))
  q17 : Ws → Eqn
  q17 c4 = sE 2009 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 17 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (ℓ "乥丢") (ℓ "丢乥") (c₄ (Swap ↑ ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = wlE 11 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1840 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4)
  q22 : Ws → Eqn
  q22 c4 = sE 2008 (lem-comm-push-CS14-sw0-R c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (ℓ "丫丢") (ℓ "丢丫") (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (ℓ "丫乩") (ℓ "乩丫") (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q25 : Ws → Eqn
  q25 c4 = sE 1841 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4)
  q26 : Ws → Eqn
  q26 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)
  q27 : Ws → Eqn
  q27 c4 = sE 2036 (lem-deb-Q-lo-eps-at02132031 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1587 (lem-F4-I-CS2-at02132031 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1797 (lem-F4-S2-CS2-at02132031 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1583 (lem-F4-CS2-CS2-at02132031 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1801 (lem-F4-K3-CS2-at02132031 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1787 (lem-F4-I-K3-at02132031 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1793 (lem-F4-S2-K3-at02132031 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1799 (lem-F4-CS2-K3-at02132031 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1789 (lem-F4-K3-K3-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1771 (lem-F4-I-S2-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1795 (lem-F4-S2-S2-at02132031 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1777 (lem-F4-CS2-S2-at02132031 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1983 (lem-F4-K3-S2-at02132031 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1981 (lem-F4-I-I-at02132031 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1791 (lem-F4-S2-I-at02132031 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1584 (lem-F4-CS2-I-at02132031 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1982 (lem-F4-K3-I-at02132031 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1570 (lem-F4-I-S3-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 1961 (lem-F4-S2-S3-at02132031 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1586 (lem-F4-CS2-S3-at02132031 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1959 (lem-F4-K3-S3-at02132031 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 2034 (lem-deb-Q-lo-split-a-at02132031 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 2035 (lem-deb-Q-lo-split-b-at02132031 c4)

-- deb-Q-lo @02132031: 331 steps
lem-deb-Q-lo-at02132031 : Ws → ⟪ (ℓ "俄亄俄俄俄") ⟫ʷ ≈ ⟪ (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕") ⟫ʷ
lem-deb-Q-lo-at02132031 c4 = derive (ℓ "俄亄俄俄俄") (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕")
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
