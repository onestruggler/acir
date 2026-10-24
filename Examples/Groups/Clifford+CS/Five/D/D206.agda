{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD206 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D206 (Sᴰ : SD206) where

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
  lem-comm-CCZ034-CX12 : Ws → St 1285
  lem-comm-CCZ034-CX12 = pickᴰ 0 Sᴰ
  lem-comm-CCZ134-CS02 : Ws → St 1356
  lem-comm-CCZ134-CS02 = pickᴰ 1 Sᴰ
  lem-comm-CCZ134-CX02 : Ws → St 1300
  lem-comm-CCZ134-CX02 = pickᴰ 2 Sᴰ
  lem-comm-TOFF304-CX12 : Ws → St 1357
  lem-comm-TOFF304-CX12 = pickᴰ 3 Sᴰ
  lem-comm-TOFF312-CX04 : Ws → St 2072
  lem-comm-TOFF312-CX04 = pickᴰ 4 Sᴰ
  lem-comm-CCZ123-CX04 : Ws → St 1358
  lem-comm-CCZ123-CX04 = pickᴰ 5 Sᴰ
  lem-comm-TOFF302-CS14 : Ws → St 1360
  lem-comm-TOFF302-CS14 = pickᴰ 6 Sᴰ
  lem-comm-TOFF302-CSd14 : Ws → St 339
  lem-comm-TOFF302-CSd14 = pickᴰ 7 Sᴰ
  lem-comm-TOFF302-CX14 : Ws → St 1361
  lem-comm-TOFF302-CX14 = pickᴰ 8 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 9 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 10 Sᴰ
  lem-box-cP-at033440 : Ws → St 1125
  lem-box-cP-at033440 = pickᴰ 11 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1332
  lem-box-perm-1324-at03243240 = pickᴰ 12 Sᴰ
  lem-S2-SBOX⟨3·1·42·0⟩ : Ws → St 2092
  lem-S2-SBOX⟨3·1·42·0⟩ = pickᴰ 13 Sᴰ
  lem-L-CX01-0 : Ws → St 2095
  lem-L-CX01-0 = pickᴰ 14 Sᴰ
  lem-L-CX01-1 : Ws → St 1762
  lem-L-CX01-1 = pickᴰ 15 Sᴰ
  lem-L-CX10-1 : Ws → St 2096
  lem-L-CX10-1 = pickᴰ 16 Sᴰ
  lem-deb-P-hi-at02132031-part1 : Ws → St 2097
  lem-deb-P-hi-at02132031-part1 = pickᴰ 17 Sᴰ
  lem-deb-P-hi-at132132-part1 : Ws → St 2098
  lem-deb-P-hi-at132132-part1 = pickᴰ 18 Sᴰ
  lem-deb-P-hi-part1 : Ws → St 2099
  lem-deb-P-hi-part1 = pickᴰ 19 Sᴰ
  lem-deb-P-lo-part1 : Ws → St 2100
  lem-deb-P-lo-part1 = pickᴰ 20 Sᴰ
  lem-deb-P-lo-at02132031-part1 : Ws → St 2101
  lem-deb-P-lo-at02132031-part1 = pickᴰ 21 Sᴰ
  lem-deb-P-lo-at132132-part1 : Ws → St 2102
  lem-deb-P-lo-at132132-part1 = pickᴰ 22 Sᴰ
  lem-F0-at01143043 : Ws → St 2086
  lem-F0-at01143043 = pickᴰ 23 Sᴰ
  lem-F0-at14213243 : Ws → St 2087
  lem-F0-at14213243 = pickᴰ 24 Sᴰ
  lem-deb-P-hi-part0 : Ws → St 2103
  lem-deb-P-hi-part0 = pickᴰ 25 Sᴰ
  lem-deb-P-hi-at02132031-part0 : Ws → St 2104
  lem-deb-P-hi-at02132031-part0 = pickᴰ 26 Sᴰ
  lem-deb-P-hi-at132132-part0 : Ws → St 2105
  lem-deb-P-hi-at132132-part0 = pickᴰ 27 Sᴰ
  lem-deb-P-lo-part0 : Ws → St 2106
  lem-deb-P-lo-part0 = pickᴰ 28 Sᴰ
  lem-deb-P-lo-at02132031-part0 : Ws → St 2107
  lem-deb-P-lo-at02132031-part0 = pickᴰ 29 Sᴰ
  lem-deb-P-lo-at132132-part0 : Ws → St 2108
  lem-deb-P-lo-at132132-part0 = pickᴰ 30 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2095 (lem-L-CX01-0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1762 (lem-L-CX01-1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2096 (lem-L-CX10-1 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2086 (lem-F0-at01143043 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2087 (lem-F0-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2092 (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q7 : Ws → Eqn
  q7 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1225 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 888 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 701 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 108 c4
  q12 : Ws → Eqn
  q12 c4 = sE 1285 (lem-comm-CCZ034-CX12 c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 107 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 106 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 700 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 716 c4
  q17 : Ws → Eqn
  q17 c4 = wlE 779 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 41 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 499 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 2072 (lem-comm-TOFF312-CX04 c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 778 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 501 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 780 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 124 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 861 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 3 c4
  q27 : Ws → Eqn
  q27 c4 = wlE 1226 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 2 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 1309 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1310 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 1130 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 1131 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 295 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 852 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 13 c4
  q36 : Ws → Eqn
  q36 c4 = wlE 879 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 878 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1311 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 109 c4
  q40 : Ws → Eqn
  q40 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 1025 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 1026 c4
  q43 : Ws → Eqn
  q43 c4 = eqn (ℓ "丌京") (ℓ "京丌") (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q44 : Ws → Eqn
  q44 c4 = wlE 1220 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = sE 1300 (lem-comm-CCZ134-CX02 c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 1221 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 1003 c4
  q48 : Ws → Eqn
  q48 c4 = eqn (ℓ "不京") (ℓ "京不") (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q49 : Ws → Eqn
  q49 c4 = wlE 1206 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 1007 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 220 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1006 c4
  q53 : Ws → Eqn
  q53 c4 = sE 1361 (lem-comm-TOFF302-CX14 c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 1005 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 1190 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 1008 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 1222 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wlE 1223 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 261 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 1224 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 1027 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1132 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 1252 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = sE 1360 (lem-comm-TOFF302-CS14 c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1233 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 339 (lem-comm-TOFF302-CSd14 c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 1041 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 1312 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1133 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 1134 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 296 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 103 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 1135 c4
  q74 : Ws → Eqn
  q74 c4 = sE 1332 (lem-box-perm-1324-at03243240 c4)
  q75 : Ws → Eqn
  q75 c4 = sE 1125 (lem-box-cP-at033440 c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 1035 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 691 c4
  q78 : Ws → Eqn
  q78 c4 = sE 1357 (lem-comm-TOFF304-CX12 c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 1036 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1037 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 1038 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 758 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wpE 1039 c4
  q84 : Ws → Eqn
  q84 c4 = wlE 765 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = sE 1358 (lem-comm-CCZ123-CX04 c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 764 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 763 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 618 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 1040 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 1313 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 1314 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wpE 1136 c4
  q93 : Ws → Eqn
  q93 c4 = wlE 960 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 1137 c4
  q95 : Ws → Eqn
  q95 c4 = wpE 301 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 272 c4
  q97 : Ws → Eqn
  q97 c4 = wlE 801 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = sE 1356 (lem-comm-CCZ134-CS02 c4)

-- L-CCZ-0 part0: 500 steps
lem-L-CCZ-0-part0 : Ws → ⟪ (ℓ "侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢") ⟫ʷ ≈ ⟪ (ℓ "佯亝丨亝丩亖亨亝亨丨亝亨丩亖亜亪五亩亜亪五亪五五丯亪五交亢交亢五丰亪五亩亜亪五佨") ⟫ʷ
lem-L-CCZ-0-part0 c4 = derive (ℓ "侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢") (ℓ "佯亝丨亝丩亖亨亝亨丨亝亨丩亖亜亪五亩亜亪五亪五五丯亪五交亢交亢五丰亪五亩亜亪五佨")
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw 12 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 1 (ℓ "佯亝俗亝俛") ∷
   re 2 1 (ℓ "丨") ∷
   re 4 1 (ℓ "丩") ∷
   re 7 1 (ℓ "佯亝俗亝俛") ∷
   re 9 1 (ℓ "丨") ∷
   re 11 1 (ℓ "丩") ∷
   re 16 1 (ℓ "佨亪俑亪俕") ∷
   re 18 1 (ℓ "丯") ∷
   re 20 1 (ℓ "丰") ∷
   rw 16 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw 19 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q20 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw 23 (q20 c4) ∷
   rw⁻ 24 (q22 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw 17 (q23 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q11 c4) ∷
   rw 18 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 16 (q9 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw 20 (q26 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw 18 (q26 c4) ∷
   rw⁻ 19 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q13 c4) ∷
   rw 25 (q12 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q16 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw 22 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw 24 (q20 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw 26 (q20 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw 20 (q23 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q12 c4) ∷
   rw 22 (q13 c4) ∷
   rw 23 (q12 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw 19 (q9 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 24 (q27 c4) ∷
   rw 23 (q28 c4) ∷
   rw⁻ 22 (q27 c4) ∷
   rw 21 (q28 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q14 c4) ∷
   rw 30 (q15 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw 25 (q17 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw 23 (q23 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q14 c4) ∷
   rw 28 (q15 c4) ∷
   rw 22 (q9 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 27 (q30 c4) ∷
   rw 26 (q31 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q14 c4) ∷
   rw 32 (q32 c4) ∷
   rw 26 (q30 c4) ∷
   rw 27 (q33 c4) ∷
   rw⁻ 25 (q29 c4) ∷
   rw 27 (q34 c4) ∷
   rw 29 (q35 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 29 (q20 c4) ∷
   rw⁻ 30 (q37 c4) ∷
   rw 31 (q20 c4) ∷
   rw⁻ 32 (q25 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw 25 (q38 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw 24 (q31 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q14 c4) ∷
   rw 30 (q32 c4) ∷
   rw 24 (q30 c4) ∷
   rw⁻ 25 (q39 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw 26 (q7 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q12 c4) ∷
   rw 33 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q16 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw 29 (q17 c4) ∷
   rw 31 (q18 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 31 (q20 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw 33 (q20 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 30 (q18 c4) ∷
   rw 27 (q23 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q11 c4) ∷
   rw 28 (q12 c4) ∷
   rw 29 (q13 c4) ∷
   rw 30 (q12 c4) ∷
   rw 31 (q14 c4) ∷
   rw 32 (q15 c4) ∷
   rw 26 (q9 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw 10 (q44 c4) ∷
   rw 11 (q45 c4) ∷
   rw 12 (q46 c4) ∷
   rw 13 (q45 c4) ∷
   rw 14 (q47 c4) ∷
   rw⁻ 15 (q48 c4) ∷
   rw 9 (q42 c4) ∷
   rw 10 (q49 c4) ∷
   rw⁻ 8 (q41 c4) ∷
   rw 10 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 13 (q54 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 15 (q55 c4) ∷
   rw⁻ 11 (q51 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 8 (q44 c4) ∷
   rw 9 (q45 c4) ∷
   rw 10 (q46 c4) ∷
   rw 11 (q45 c4) ∷
   rw 12 (q47 c4) ∷
   rw⁻ 13 (q48 c4) ∷
   rw 7 (q42 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   rw 11 (q59 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 9 (q59 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw 10 (q40 c4) ∷
   rw⁻ 13 (q41 c4) ∷
   rw⁻ 13 (q42 c4) ∷
   rw⁻ 12 (q43 c4) ∷
   rw 13 (q44 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q46 c4) ∷
   rw 16 (q45 c4) ∷
   rw 17 (q47 c4) ∷
   rw⁻ 18 (q48 c4) ∷
   rw 12 (q42 c4) ∷
   rw 13 (q49 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw 13 (q50 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 16 (q54 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 18 (q55 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 11 (q42 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 12 (q45 c4) ∷
   rw 13 (q46 c4) ∷
   rw 14 (q45 c4) ∷
   rw 15 (q47 c4) ∷
   rw⁻ 16 (q48 c4) ∷
   rw 10 (q42 c4) ∷
   rw⁻ 11 (q57 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw 12 (q40 c4) ∷
   rw⁻ 15 (q60 c4) ∷
   rw 14 (q61 c4) ∷
   rw⁻ 13 (q60 c4) ∷
   rw 12 (q61 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 13 (q40 c4) ∷
   rw⁻ 17 (q62 c4) ∷
   rw⁻ 16 (q63 c4) ∷
   rw 17 (q64 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw 19 (q66 c4) ∷
   rw⁻ 20 (q65 c4) ∷
   rw⁻ 21 (q67 c4) ∷
   rw⁻ 22 (q68 c4) ∷
   rw 16 (q62 c4) ∷
   rw 15 (q69 c4) ∷
   rw⁻ 15 (q62 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw 15 (q64 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw 17 (q66 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw⁻ 19 (q67 c4) ∷
   rw⁻ 20 (q68 c4) ∷
   rw 14 (q62 c4) ∷
   rw⁻ 15 (q70 c4) ∷
   rw 13 (q69 c4) ∷
   rw 16 (q71 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q45 c4) ∷
   rw 17 (q46 c4) ∷
   rw 18 (q45 c4) ∷
   rw 19 (q47 c4) ∷
   rw⁻ 15 (q71 c4) ∷
   rw⁻ 16 (q72 c4) ∷
   rw⁻ 14 (q73 c4) ∷
   rw⁻ 15 (q40 c4) ∷
   rw 15 (q74 c4) ∷
   rw 15 (q75 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q76 c4) ∷
   rw⁻ 19 (q77 c4) ∷
   rw 20 (q78 c4) ∷
   rw⁻ 21 (q79 c4) ∷
   rw 22 (q78 c4) ∷
   rw⁻ 23 (q80 c4) ∷
   rw⁻ 24 (q81 c4) ∷
   rw 18 (q9 c4) ∷
   rw 17 (q82 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 16 (q76 c4) ∷
   rw⁻ 17 (q77 c4) ∷
   rw 18 (q78 c4) ∷
   rw⁻ 19 (q79 c4) ∷
   rw 20 (q78 c4) ∷
   rw⁻ 21 (q80 c4) ∷
   rw⁻ 22 (q81 c4) ∷
   rw 16 (q9 c4) ∷
   rw⁻ 17 (q83 c4) ∷
   rw 15 (q82 c4) ∷
   rw 18 (q18 c4) ∷
   rw 17 (q84 c4) ∷
   rw 18 (q85 c4) ∷
   rw 19 (q86 c4) ∷
   rw 20 (q85 c4) ∷
   rw 21 (q87 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw 18 (q88 c4) ∷
   rw⁻ 16 (q89 c4) ∷
   rw⁻ 17 (q75 c4) ∷
   rw⁻ 17 (q74 c4) ∷
   rw 17 (q40 c4) ∷
   rw⁻ 21 (q90 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 21 (q52 c4) ∷
   rw 22 (q53 c4) ∷
   rw⁻ 23 (q54 c4) ∷
   rw 24 (q53 c4) ∷
   rw⁻ 25 (q55 c4) ∷
   rw⁻ 26 (q68 c4) ∷
   rw 20 (q90 c4) ∷
   rw 19 (q91 c4) ∷
   rw⁻ 19 (q90 c4) ∷
   rw⁻ 18 (q63 c4) ∷
   rw⁻ 19 (q52 c4) ∷
   rw 20 (q53 c4) ∷
   rw⁻ 21 (q54 c4) ∷
   rw 22 (q53 c4) ∷
   rw⁻ 23 (q55 c4) ∷
   rw⁻ 24 (q68 c4) ∷
   rw 18 (q90 c4) ∷
   rw⁻ 19 (q92 c4) ∷
   rw 17 (q91 c4) ∷
   rw 20 (q71 c4) ∷
   rw 19 (q44 c4) ∷
   rw 20 (q45 c4) ∷
   rw 21 (q46 c4) ∷
   rw 22 (q45 c4) ∷
   rw 23 (q47 c4) ∷
   rw⁻ 19 (q71 c4) ∷
   rw 20 (q93 c4) ∷
   rw⁻ 18 (q94 c4) ∷
   rw⁻ 19 (q40 c4) ∷
   rw 19 (q74 c4) ∷
   rw 19 (q75 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q76 c4) ∷
   rw⁻ 23 (q77 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q79 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q80 c4) ∷
   rw⁻ 28 (q81 c4) ∷
   rw 22 (q9 c4) ∷
   rw 21 (q82 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q76 c4) ∷
   rw⁻ 21 (q77 c4) ∷
   rw 22 (q78 c4) ∷
   rw⁻ 23 (q79 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q80 c4) ∷
   rw⁻ 26 (q81 c4) ∷
   rw 20 (q9 c4) ∷
   rw⁻ 21 (q83 c4) ∷
   rw 19 (q82 c4) ∷
   rw 22 (q18 c4) ∷
   rw 21 (q84 c4) ∷
   rw 22 (q85 c4) ∷
   rw 23 (q86 c4) ∷
   rw 24 (q85 c4) ∷
   rw 25 (q87 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw 22 (q88 c4) ∷
   rw⁻ 20 (q89 c4) ∷
   rw⁻ 21 (q75 c4) ∷
   rw⁻ 21 (q74 c4) ∷
   rw 21 (q74 c4) ∷
   rw 21 (q75 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw⁻ 24 (q76 c4) ∷
   rw⁻ 25 (q77 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q79 c4) ∷
   rw 28 (q78 c4) ∷
   rw⁻ 29 (q80 c4) ∷
   rw⁻ 30 (q81 c4) ∷
   rw 24 (q9 c4) ∷
   rw 23 (q82 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 22 (q76 c4) ∷
   rw⁻ 23 (q77 c4) ∷
   rw 24 (q78 c4) ∷
   rw⁻ 25 (q79 c4) ∷
   rw 26 (q78 c4) ∷
   rw⁻ 27 (q80 c4) ∷
   rw⁻ 28 (q81 c4) ∷
   rw 22 (q9 c4) ∷
   rw⁻ 23 (q83 c4) ∷
   rw 21 (q82 c4) ∷
   rw 24 (q18 c4) ∷
   rw 23 (q84 c4) ∷
   rw 24 (q85 c4) ∷
   rw 25 (q86 c4) ∷
   rw 26 (q85 c4) ∷
   rw 27 (q87 c4) ∷
   rw⁻ 23 (q18 c4) ∷
   rw 24 (q88 c4) ∷
   rw⁻ 22 (q89 c4) ∷
   rw⁻ 23 (q75 c4) ∷
   rw⁻ 23 (q74 c4) ∷
   rw 23 (q40 c4) ∷
   rw 27 (q95 c4) ∷
   rw 26 (q64 c4) ∷
   rw⁻ 27 (q65 c4) ∷
   rw 28 (q66 c4) ∷
   rw⁻ 29 (q65 c4) ∷
   rw⁻ 30 (q67 c4) ∷
   rw⁻ 26 (q95 c4) ∷
   rw⁻ 25 (q96 c4) ∷
   rw 25 (q95 c4) ∷
   rw 24 (q64 c4) ∷
   rw⁻ 25 (q65 c4) ∷
   rw 26 (q66 c4) ∷
   rw⁻ 27 (q65 c4) ∷
   rw⁻ 28 (q67 c4) ∷
   rw⁻ 24 (q95 c4) ∷
   rw⁻ 23 (q96 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw 24 (q40 c4) ∷
   rw⁻ 27 (q97 c4) ∷
   rw 26 (q98 c4) ∷
   rw⁻ 25 (q97 c4) ∷
   rw 24 (q98 c4) ∷
   rw⁻ 25 (q40 c4) ∷
   rw 25 (q74 c4) ∷
   rw 25 (q75 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 28 (q76 c4) ∷
   rw⁻ 29 (q77 c4) ∷
   rw 30 (q78 c4) ∷
   rw⁻ 31 (q79 c4) ∷
   rw 32 (q78 c4) ∷
   rw⁻ 33 (q80 c4) ∷
   rw⁻ 34 (q81 c4) ∷
   rw 28 (q9 c4) ∷
   rw 27 (q82 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 26 (q76 c4) ∷
   rw⁻ 27 (q77 c4) ∷
   rw 28 (q78 c4) ∷
   rw⁻ 29 (q79 c4) ∷
   rw 30 (q78 c4) ∷
   rw⁻ 31 (q80 c4) ∷
   rw⁻ 32 (q81 c4) ∷
   rw 26 (q9 c4) ∷
   rw⁻ 27 (q83 c4) ∷
   rw 25 (q82 c4) ∷
   rw 28 (q18 c4) ∷
   rw 27 (q84 c4) ∷
   rw 28 (q85 c4) ∷
   rw 29 (q86 c4) ∷
   rw 30 (q85 c4) ∷
   rw 31 (q87 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 28 (q88 c4) ∷
   rw⁻ 26 (q89 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 2103 (lem-deb-P-hi-part0 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 2099 (lem-deb-P-hi-part1 c4)

-- deb-P-hi: 2 steps
lem-deb-P-hi : Ws → ⟪ (ℓ "侬亇侬") ⟫ʷ ≈ ⟪ (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乢乢乩乩乩") ⟫ʷ
lem-deb-P-hi c4 = derive (ℓ "侬亇侬") (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乢乢乩乩乩")
  (rw 0 (q99 c4) ∷
   rw 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = sE 2104 (lem-deb-P-hi-at02132031-part0 c4)
  q102 : Ws → Eqn
  q102 c4 = sE 2097 (lem-deb-P-hi-at02132031-part1 c4)

-- deb-P-hi @02132031: 2 steps
lem-deb-P-hi-at02132031 : Ws → ⟪ (ℓ "俄亁俄") ⟫ʷ ≈ ⟪ (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽") ⟫ʷ
lem-deb-P-hi-at02132031 c4 = derive (ℓ "俄亁俄") (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽")
  (rw 0 (q101 c4) ∷
   rw 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = sE 2105 (lem-deb-P-hi-at132132-part0 c4)
  q104 : Ws → Eqn
  q104 c4 = sE 2098 (lem-deb-P-hi-at132132-part1 c4)

-- deb-P-hi @132132: 2 steps
lem-deb-P-hi-at132132 : Ws → ⟪ (ℓ "侧亄侧") ⟫ʷ ≈ ⟪ (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕") ⟫ʷ
lem-deb-P-hi-at132132 c4 = derive (ℓ "侧亄侧") (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕")
  (rw 0 (q103 c4) ∷
   rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = sE 2106 (lem-deb-P-lo-part0 c4)
  q106 : Ws → Eqn
  q106 c4 = sE 2100 (lem-deb-P-lo-part1 c4)

-- deb-P-lo: 2 steps
lem-deb-P-lo : Ws → ⟪ (ℓ "侬亊侬") ⟫ʷ ≈ ⟪ (ℓ "亊亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹") ⟫ʷ
lem-deb-P-lo c4 = derive (ℓ "侬亊侬") (ℓ "亊亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹")
  (rw 0 (q105 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = sE 2107 (lem-deb-P-lo-at02132031-part0 c4)
  q108 : Ws → Eqn
  q108 c4 = sE 2101 (lem-deb-P-lo-at02132031-part1 c4)

-- deb-P-lo @02132031: 2 steps
lem-deb-P-lo-at02132031 : Ws → ⟪ (ℓ "俄亄俄") ⟫ʷ ≈ ⟪ (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ
lem-deb-P-lo-at02132031 c4 = derive (ℓ "俄亄俄") (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕")
  (rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = sE 2108 (lem-deb-P-lo-at132132-part0 c4)
  q110 : Ws → Eqn
  q110 c4 = sE 2102 (lem-deb-P-lo-at132132-part1 c4)

-- deb-P-lo @132132: 2 steps
lem-deb-P-lo-at132132 : Ws → ⟪ (ℓ "侧亇侧") ⟫ʷ ≈ ⟪ (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐一丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐一乇乇乩乩乩") ⟫ʷ
lem-deb-P-lo-at132132 c4 = derive (ℓ "侧亇侧") (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐一丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐一乇乇乩乩乩")
  (rw 0 (q109 c4) ∷
   rw 0 (q110 c4) ∷ []) Eq.refl
