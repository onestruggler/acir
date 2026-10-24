{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD207 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D207 (Sᴰ : SD207) where

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
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R : Ws → St 2009
  lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R : Ws → St 2010
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R = pickᴰ 1 Sᴰ
  lem-TR2-1b52048e : Ws → St 2109
  lem-TR2-1b52048e = pickᴰ 2 Sᴰ
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 3 Sᴰ
  lem-F1-order-Kat2 : Ws → St 1886
  lem-F1-order-Kat2 = pickᴰ 4 Sᴰ
  lem-F1-order-Kat3 : Ws → St 1887
  lem-F1-order-Kat3 = pickᴰ 5 Sᴰ
  lem-F1-order-SKat2 : Ws → St 1888
  lem-F1-order-SKat2 = pickᴰ 6 Sᴰ
  lem-F1-order-SKat3 : Ws → St 1889
  lem-F1-order-SKat3 = pickᴰ 7 Sᴰ
  lem-F1-order-Sat2 : Ws → St 1890
  lem-F1-order-Sat2 = pickᴰ 8 Sᴰ
  lem-F1-order-Sat3 : Ws → St 1891
  lem-F1-order-Sat3 = pickᴰ 9 Sᴰ
  lem-F2-I-K0 : Ws → St 1892
  lem-F2-I-K0 = pickᴰ 10 Sᴰ
  lem-F2-I-K1 : Ws → St 1893
  lem-F2-I-K1 = pickᴰ 11 Sᴰ
  lem-F2-I-K2 : Ws → St 1894
  lem-F2-I-K2 = pickᴰ 12 Sᴰ
  lem-F2-I-K3 : Ws → St 1895
  lem-F2-I-K3 = pickᴰ 13 Sᴰ
  lem-F2-I-S0 : Ws → St 1896
  lem-F2-I-S0 = pickᴰ 14 Sᴰ
  lem-F2-I-S1 : Ws → St 1897
  lem-F2-I-S1 = pickᴰ 15 Sᴰ
  lem-F2-I-S2 : Ws → St 1898
  lem-F2-I-S2 = pickᴰ 16 Sᴰ
  lem-F2-I-S3 : Ws → St 1899
  lem-F2-I-S3 = pickᴰ 17 Sᴰ
  lem-F2-K0-K1 : Ws → St 1900
  lem-F2-K0-K1 = pickᴰ 18 Sᴰ
  lem-F2-K0-K2 : Ws → St 1901
  lem-F2-K0-K2 = pickᴰ 19 Sᴰ
  lem-F2-K0-K3 : Ws → St 1902
  lem-F2-K0-K3 = pickᴰ 20 Sᴰ
  lem-F2-K1-K2 : Ws → St 1903
  lem-F2-K1-K2 = pickᴰ 21 Sᴰ
  lem-F2-K1-K3 : Ws → St 1904
  lem-F2-K1-K3 = pickᴰ 22 Sᴰ
  lem-F2-K2-K3 : Ws → St 1905
  lem-F2-K2-K3 = pickᴰ 23 Sᴰ
  lem-F2-S0-K1 : Ws → St 1906
  lem-F2-S0-K1 = pickᴰ 24 Sᴰ
  lem-F2-S0-K2 : Ws → St 1907
  lem-F2-S0-K2 = pickᴰ 25 Sᴰ
  lem-F2-S0-K3 : Ws → St 1908
  lem-F2-S0-K3 = pickᴰ 26 Sᴰ
  lem-F2-S0-S1 : Ws → St 1909
  lem-F2-S0-S1 = pickᴰ 27 Sᴰ
  lem-F2-S0-S2 : Ws → St 1910
  lem-F2-S0-S2 = pickᴰ 28 Sᴰ
  lem-F2-S0-S3 : Ws → St 1911
  lem-F2-S0-S3 = pickᴰ 29 Sᴰ
  lem-F2-S1-K0 : Ws → St 1912
  lem-F2-S1-K0 = pickᴰ 30 Sᴰ
  lem-F2-S1-K2 : Ws → St 1913
  lem-F2-S1-K2 = pickᴰ 31 Sᴰ
  lem-F2-S1-K3 : Ws → St 1914
  lem-F2-S1-K3 = pickᴰ 32 Sᴰ
  lem-F2-S1-S2 : Ws → St 1915
  lem-F2-S1-S2 = pickᴰ 33 Sᴰ
  lem-F2-S1-S3 : Ws → St 1916
  lem-F2-S1-S3 = pickᴰ 34 Sᴰ
  lem-F2-S2-K0 : Ws → St 1917
  lem-F2-S2-K0 = pickᴰ 35 Sᴰ
  lem-F2-S2-K1 : Ws → St 1918
  lem-F2-S2-K1 = pickᴰ 36 Sᴰ
  lem-F2-S2-K3 : Ws → St 1919
  lem-F2-S2-K3 = pickᴰ 37 Sᴰ
  lem-F2-S2-S3 : Ws → St 1920
  lem-F2-S2-S3 = pickᴰ 38 Sᴰ
  lem-F2-S3-K0 : Ws → St 1921
  lem-F2-S3-K0 = pickᴰ 39 Sᴰ
  lem-F2-S3-K1 : Ws → St 1922
  lem-F2-S3-K1 = pickᴰ 40 Sᴰ
  lem-F2-S3-K2 : Ws → St 1923
  lem-F2-S3-K2 = pickᴰ 41 Sᴰ
  lem-F2-S0-CS1 : Ws → St 1924
  lem-F2-S0-CS1 = pickᴰ 42 Sᴰ
  lem-F2-S0-CS2 : Ws → St 1925
  lem-F2-S0-CS2 = pickᴰ 43 Sᴰ
  lem-F2-S2-CS0 : Ws → St 1926
  lem-F2-S2-CS0 = pickᴰ 44 Sᴰ
  lem-F2-I-CS0 : Ws → St 1928
  lem-F2-I-CS0 = pickᴰ 45 Sᴰ
  lem-F2-I-CS1 : Ws → St 1929
  lem-F2-I-CS1 = pickᴰ 46 Sᴰ
  lem-F2-I-CS2 : Ws → St 1930
  lem-F2-I-CS2 = pickᴰ 47 Sᴰ
  lem-F2-S1-CS2 : Ws → St 1931
  lem-F2-S1-CS2 = pickᴰ 48 Sᴰ
  lem-F2-S3-CS0 : Ws → St 1932
  lem-F2-S3-CS0 = pickᴰ 49 Sᴰ
  lem-F2-S3-CS1 : Ws → St 1933
  lem-F2-S3-CS1 = pickᴰ 50 Sᴰ
  lem-F2-K1-CS2 : Ws → St 1935
  lem-F2-K1-CS2 = pickᴰ 51 Sᴰ
  lem-F1-comm-CS-S0at2 : Ws → St 1936
  lem-F1-comm-CS-S0at2 = pickᴰ 52 Sᴰ
  lem-F2-K3-CS0 : Ws → St 1937
  lem-F2-K3-CS0 = pickᴰ 53 Sᴰ
  lem-F2-K3-CS1 : Ws → St 1938
  lem-F2-K3-CS1 = pickᴰ 54 Sᴰ
  lem-F1-comm-CS-S1at2 : Ws → St 1940
  lem-F1-comm-CS-S1at2 = pickᴰ 55 Sᴰ
  lem-F1-order-CSat2 : Ws → St 1942
  lem-F1-order-CSat2 = pickᴰ 56 Sᴰ
  lem-F2-K0-CS1 : Ws → St 1943
  lem-F2-K0-CS1 = pickᴰ 57 Sᴰ
  lem-F2-K0-CS2 : Ws → St 1944
  lem-F2-K0-CS2 = pickᴰ 58 Sᴰ
  lem-F2-K2-CS0 : Ws → St 1945
  lem-F2-K2-CS0 = pickᴰ 59 Sᴰ
  lem-deb-CKS-part1 : Ws → St 2110
  lem-deb-CKS-part1 = pickᴰ 60 Sᴰ
  lem-deb-CKS-at0213243140-part1 : Ws → St 2111
  lem-deb-CKS-at0213243140-part1 = pickᴰ 61 Sᴰ
  lem-deb-CKS-at0213243140-part2 : Ws → St 2112
  lem-deb-CKS-at0213243140-part2 = pickᴰ 62 Sᴰ
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
  lem-deb-AD-part1 : Ws → St 2113
  lem-deb-AD-part1 = pickᴰ 68 Sᴰ
  lem-deb-CKS-part2 : Ws → St 2114
  lem-deb-CKS-part2 = pickᴰ 69 Sᴰ
  lem-deb-CKS-at0213243140-part3 : Ws → St 2115
  lem-deb-CKS-at0213243140-part3 = pickᴰ 70 Sᴰ
  lem-deb-AD-at02132031-part1 : Ws → St 2116
  lem-deb-AD-at02132031-part1 = pickᴰ 71 Sᴰ
  lem-deb-Q-hi : Ws → St 2117
  lem-deb-Q-hi = pickᴰ 72 Sᴰ
  lem-deb-Q-lo-at02132031 : Ws → St 2118
  lem-deb-Q-lo-at02132031 = pickᴰ 73 Sᴰ
  lem-deb-Q-hi-at132132 : Ws → St 2119
  lem-deb-Q-hi-at132132 = pickᴰ 74 Sᴰ
  lem-deb-Q-lo-at132132 : Ws → St 2120
  lem-deb-Q-lo-at132132 = pickᴰ 75 Sᴰ
  lem-deb-AD-part0 : Ws → St 2121
  lem-deb-AD-part0 = pickᴰ 76 Sᴰ
  lem-deb-CKS-part0 : Ws → St 2122
  lem-deb-CKS-part0 = pickᴰ 77 Sᴰ
  lem-deb-CKS-at0213243140-part0 : Ws → St 2123
  lem-deb-CKS-at0213243140-part0 = pickᴰ 78 Sᴰ
  lem-deb-AD-at02132031-part0 : Ws → St 2124
  lem-deb-AD-at02132031-part0 = pickᴰ 79 Sᴰ
  lem-ckt-TT : Ws → St 2125
  lem-ckt-TT = pickᴰ 80 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 3 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 6 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2109 (lem-TR2-1b52048e c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2010 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2009 (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2118 (lem-deb-Q-lo-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2119 (lem-deb-Q-hi-at132132 c4)

-- deb-rel-272@0-R: 15 steps
lem-deb-rel-272at0-R : Ws → ⟪ (ℓ "俄亄俄俄俄亄侧亄俄") ⟫ʷ ≈ ⟪ (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕亄亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕侧俄") ⟫ʷ
lem-deb-rel-272at0-R c4 = derive (ℓ "俄亄俄俄俄亄侧亄俄") (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕亄亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕侧俄")
  (rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw 10 (q3 c4) ∷
   rw 9 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q4 c4) ∷
   rw 13 (q2 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q1 c4) ∷
   rw 0 (q6 c4) ∷
   rw 33 (q7 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = sE 2120 (lem-deb-Q-lo-at132132 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2117 (lem-deb-Q-hi c4)

-- deb-rel-272@1-R: 3 steps
lem-deb-rel-272at1-R : Ws → ⟪ (ℓ "侧亇侧侧侧亇侬亇侧") ⟫ʷ ≈ ⟪ (ℓ "亇乇丘乇丘乇丐丐丐一丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐一乩乩乩亇亇乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乩乩乩侬侧") ⟫ʷ
lem-deb-rel-272at1-R c4 = derive (ℓ "侧亇侧侧侧亇侬亇侧") (ℓ "亇乇丘乇丘乇丐丐丐一丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐一乩乩乩亇亇乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乩乩乩侬侧")
  (rw 8 (q3 c4) ∷
   rw 0 (q8 c4) ∷
   rw 33 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = sE 2121 (lem-deb-AD-part0 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2113 (lem-deb-AD-part1 c4)

-- deb-AD: 2 steps
lem-deb-AD : Ws → ⟪ (ℓ "亇乩乩亇丢侬亊侬亊侬乩乩乩丢亇乩乩亇丢亇乩乩亇丢侬亇乩乩亇丢") ⟫ʷ ≈ ⟪ (ℓ "亊乹亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹") ⟫ʷ
lem-deb-AD c4 = derive (ℓ "亇乩乩亇丢侬亊侬亊侬乩乩乩丢亇乩乩亇丢亇乩乩亇丢侬亇乩乩亇丢") (ℓ "亊乹亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹")
  (rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = sE 2122 (lem-deb-CKS-part0 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2110 (lem-deb-CKS-part1 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 2114 (lem-deb-CKS-part2 c4)

-- deb-CKS: 3 steps
lem-deb-CKS : Ws → ⟪ (ℓ "侬亊侬亊侬乩乩乩丢侬") ⟫ʷ ≈ ⟪ (ℓ "亰乢丞乢丞乢世世世一世乢乢乢乢丞乢丞乢世世世一世乹乹乹乢丞乢丞乢世世世一乢乢丞乢丞乢世世世一乹") ⟫ʷ
lem-deb-CKS c4 = derive (ℓ "侬亊侬亊侬乩乩乩丢侬") (ℓ "亰乢丞乢丞乢世世世一世乢乢乢乢丞乢丞乢世世世一世乹乹乹乢丞乢丞乢世世世一乢乢丞乢丞乢世世世一乹")
  (rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 2123 (lem-deb-CKS-at0213243140-part0 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2111 (lem-deb-CKS-at0213243140-part1 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 2112 (lem-deb-CKS-at0213243140-part2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2115 (lem-deb-CKS-at0213243140-part3 c4)

-- deb-CKS @0213243140: 4 steps
lem-deb-CKS-at0213243140 : Ws → ⟪ (ℓ "俊中俊中俊丽丽丽上俊") ⟫ʷ ≈ ⟪ (ℓ "五乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢丨丨丨乕丒乕丒乕丢丢丢一乕乕丒乕丒乕丢丢丢一丨") ⟫ʷ
lem-deb-CKS-at0213243140 c4 = derive (ℓ "俊中俊中俊丽丽丽上俊") (ℓ "五乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢丨丨丨乕丒乕丒乕丢丢丢一乕乕丒乕丒乕丢丢丢一丨")
  (rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 2124 (lem-deb-AD-at02132031-part0 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 2116 (lem-deb-AD-at02132031-part1 c4)

-- deb-AD @02132031: 2 steps
lem-deb-AD-at02132031 : Ws → ⟪ (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亁丽丽亁丢俄亁丽丽亁丢") ⟫ʷ ≈ ⟪ (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ
lem-deb-AD-at02132031 c4 = derive (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亁丽丽亁丢俄亁丽丽亁丢") (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕")
  (rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wlE 1083 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 2125 (lem-ckt-TT c4)

-- ckt-TST part52: 55 steps
lem-ckt-TST-part52 : Ws → ⟪ (ℓ "並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part52 c4 = derive (ℓ "並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw 44 (q21 c4) ∷
   rw 45 (q21 c4) ∷
   rw 46 (q21 c4) ∷
   rw 47 (q21 c4) ∷
   rw 48 (q21 c4) ∷
   rw 49 (q21 c4) ∷
   rw 50 (q21 c4) ∷
   rw 51 (q21 c4) ∷
   rw 52 (q21 c4) ∷
   rw 53 (q21 c4) ∷
   rw 54 (q21 c4) ∷
   rw 55 (q21 c4) ∷
   rw 56 (q21 c4) ∷
   rw 57 (q21 c4) ∷
   rw 58 (q21 c4) ∷
   rw 59 (q21 c4) ∷
   rw 60 (q21 c4) ∷
   rw 61 (q21 c4) ∷
   rw 62 (q21 c4) ∷
   rw 63 (q21 c4) ∷
   rw 64 (q21 c4) ∷
   rw 65 (q21 c4) ∷
   rw 66 (q21 c4) ∷
   rw 67 (q21 c4) ∷
   rw 68 (q21 c4) ∷
   rw 69 (q21 c4) ∷
   rw 70 (q21 c4) ∷
   rw 71 (q21 c4) ∷
   rw 72 (q21 c4) ∷
   rw 73 (q21 c4) ∷
   rw 74 (q21 c4) ∷
   rw 75 (q21 c4) ∷
   rw 76 (q21 c4) ∷
   rw 77 (q21 c4) ∷
   rw 78 (q21 c4) ∷
   rw 79 (q21 c4) ∷
   rw 80 (q21 c4) ∷
   rw 81 (q21 c4) ∷
   rw 82 (q21 c4) ∷
   rw 83 (q21 c4) ∷
   rw 84 (q21 c4) ∷
   rw 85 (q21 c4) ∷
   rw 86 (q21 c4) ∷
   rw 87 (q21 c4) ∷
   rw 88 (q21 c4) ∷
   rw 89 (q21 c4) ∷
   rw 90 (q21 c4) ∷
   rw 91 (q21 c4) ∷
   rw 92 (q21 c4) ∷
   rw 93 (q21 c4) ∷
   rw 94 (q21 c4) ∷
   rw 95 (q21 c4) ∷
   rw 96 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 0 (q21 c4) ∷ []) Eq.refl
