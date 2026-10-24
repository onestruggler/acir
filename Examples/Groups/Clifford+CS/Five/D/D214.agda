{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD214 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D214 (Sᴰ : SD214) where

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
  lem-comm-CCZ134-CSd02 : Ws → St 1359
  lem-comm-CCZ134-CSd02 = pickᴰ 6 Sᴰ
  lem-comm-TOFF302-CS14 : Ws → St 1360
  lem-comm-TOFF302-CS14 = pickᴰ 7 Sᴰ
  lem-comm-TOFF302-CSd14 : Ws → St 339
  lem-comm-TOFF302-CSd14 = pickᴰ 8 Sᴰ
  lem-comm-TOFF302-CX14 : Ws → St 1361
  lem-comm-TOFF302-CX14 = pickᴰ 9 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 10 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 11 Sᴰ
  lem-box-cP-at033440 : Ws → St 1125
  lem-box-cP-at033440 = pickᴰ 12 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1332
  lem-box-perm-1324-at03243240 = pickᴰ 13 Sᴰ
  lem-box-perm-1324-at033440 : Ws → St 1333
  lem-box-perm-1324-at033440 = pickᴰ 14 Sᴰ
  lem-box2-at0310243142 : Ws → St 1340
  lem-box2-at0310243142 = pickᴰ 15 Sᴰ
  lem-CKc-box-at0312203441 : Ws → St 2142
  lem-CKc-box-at0312203441 = pickᴰ 16 Sᴰ
  lem-CKc-box-at033440 : Ws → St 2143
  lem-CKc-box-at033440 = pickᴰ 17 Sᴰ
  lem-S2-SBOX⟨3·0·41·2⟩ : Ws → St 2091
  lem-S2-SBOX⟨3·0·41·2⟩ = pickᴰ 18 Sᴰ
  lem-S2-SBOX⟨3·1·42·0⟩ : Ws → St 2092
  lem-S2-SBOX⟨3·1·42·0⟩ = pickᴰ 19 Sᴰ
  lem-box-perm-3421-at03243240 : Ws → St 2144
  lem-box-perm-3421-at03243240 = pickᴰ 20 Sᴰ
  lem-box-perm-4213-at03243240 : Ws → St 1550
  lem-box-perm-4213-at03243240 = pickᴰ 21 Sᴰ
  lem-box-perm-4312-at0312203441 : Ws → St 2145
  lem-box-perm-4312-at0312203441 = pickᴰ 22 Sᴰ
  lem-F0-at01143043 : Ws → St 2086
  lem-F0-at01143043 = pickᴰ 23 Sᴰ
  lem-F0-at14213243 : Ws → St 2087
  lem-F0-at14213243 = pickᴰ 24 Sᴰ
  lem-nf-comm-CSu-CSat0 : Ws → St 2146
  lem-nf-comm-CSu-CSat0 = pickᴰ 25 Sᴰ
  lem-nf-rel-266at0 : Ws → St 2147
  lem-nf-rel-266at0 = pickᴰ 26 Sᴰ
  lem-nf-rel-267at0 : Ws → St 2148
  lem-nf-rel-267at0 = pickᴰ 27 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2086 (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2087 (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1225 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 888 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 701 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 108 c4
  q8 : Ws → Eqn
  q8 c4 = sE 1285 (lem-comm-CCZ034-CX12 c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 107 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 106 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 700 c4
  q12 : Ws → Eqn
  q12 c4 = wpE 716 c4
  q13 : Ws → Eqn
  q13 c4 = wlE 779 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 41 c4
  q15 : Ws → Eqn
  q15 c4 = wlE 499 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2072 (lem-comm-TOFF312-CX04 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 778 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 501 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 780 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 124 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 861 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 3 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 1226 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 2 c4
  q25 : Ws → Eqn
  q25 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 1025 c4
  q27 : Ws → Eqn
  q27 c4 = wpE 1026 c4
  q28 : Ws → Eqn
  q28 c4 = eqn (ℓ "丌京") (ℓ "京丌") (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q29 : Ws → Eqn
  q29 c4 = wlE 1220 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1300 (lem-comm-CCZ134-CX02 c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 1221 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 1003 c4
  q33 : Ws → Eqn
  q33 c4 = eqn (ℓ "不京") (ℓ "京不") (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q34 : Ws → Eqn
  q34 c4 = wlE 1206 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 1007 c4
  q36 : Ws → Eqn
  q36 c4 = wlE 220 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 1006 c4
  q38 : Ws → Eqn
  q38 c4 = sE 1361 (lem-comm-TOFF302-CX14 c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 1005 c4
  q40 : Ws → Eqn
  q40 c4 = wlE 1190 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 1008 c4
  q42 : Ws → Eqn
  q42 c4 = wlE 1222 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 1223 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wpE 261 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 1224 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wpE 1027 c4
  q47 : Ws → Eqn
  q47 c4 = sE 1332 (lem-box-perm-1324-at03243240 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 1125 (lem-box-cP-at033440 c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 1035 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 691 c4
  q51 : Ws → Eqn
  q51 c4 = sE 1357 (lem-comm-TOFF304-CX12 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1036 c4
  q53 : Ws → Eqn
  q53 c4 = wpE 1037 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 1038 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 758 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 1039 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 765 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = sE 1358 (lem-comm-CCZ123-CX04 c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 764 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 763 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 618 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 1040 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 301 c4
  q64 : Ws → Eqn
  q64 c4 = sE 1360 (lem-comm-TOFF302-CS14 c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1233 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 339 (lem-comm-TOFF302-CSd14 c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 1041 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 272 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 801 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = sE 1356 (lem-comm-CCZ134-CS02 c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 792 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = sE 1359 (lem-comm-CCZ134-CSd02 c4)
  q73 : Ws → Eqn
  q73 c4 = sE 1550 (lem-box-perm-4213-at03243240 c4)
  q74 : Ws → Eqn
  q74 c4 = sE 1340 (lem-box2-at0310243142 c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 1042 c4
  q76 : Ws → Eqn
  q76 c4 = wlE 263 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 161 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 1043 c4
  q79 : Ws → Eqn
  q79 c4 = sE 2146 (lem-nf-comm-CSu-CSat0 c4)

-- F1-comm-CSu-CS@0: 288 steps
lem-F1-comm-CSu-CSat0 : Ws → ⟪ (ℓ "侧俄") ⟫ʷ ≈ ⟪ (ℓ "俄侧") ⟫ʷ
lem-F1-comm-CSu-CSat0 c4 = derive (ℓ "侧俄") (ℓ "俄侧")
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   re 0 1 (ℓ "佯亝俗亝俛") ∷
   re 2 1 (ℓ "丨") ∷
   re 4 1 (ℓ "丩") ∷
   re 5 1 (ℓ "佨亪俑亪俕") ∷
   re 7 1 (ℓ "丯") ∷
   re 9 1 (ℓ "丰") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 8 (q13 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 12 (q16 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q8 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 11 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 9 (q19 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 14 (q11 c4) ∷
   rw 8 (q5 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 3 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 5 (q27 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 6 (q35 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q38 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw 10 (q38 c4) ∷
   rw⁻ 11 (q40 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q33 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 6 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw⁻ 10 (q50 c4) ∷
   rw 11 (q51 c4) ∷
   rw⁻ 12 (q52 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw⁻ 15 (q54 c4) ∷
   rw 9 (q5 c4) ∷
   rw 8 (q55 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 9 (q51 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw 11 (q51 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 13 (q54 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw 6 (q55 c4) ∷
   rw 9 (q14 c4) ∷
   rw 8 (q57 c4) ∷
   rw 9 (q58 c4) ∷
   rw 10 (q59 c4) ∷
   rw 11 (q58 c4) ∷
   rw 12 (q60 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q61 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 8 (q48 c4) ∷
   rw⁻ 8 (q47 c4) ∷
   rw 8 (q25 c4) ∷
   rw 12 (q63 c4) ∷
   rw 11 (q64 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw 13 (q66 c4) ∷
   rw⁻ 14 (q65 c4) ∷
   rw⁻ 15 (q67 c4) ∷
   rw⁻ 11 (q63 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw 10 (q63 c4) ∷
   rw 9 (q64 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw 11 (q66 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw⁻ 13 (q67 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 9 (q25 c4) ∷
   rw⁻ 12 (q69 c4) ∷
   rw 11 (q70 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 10 (q47 c4) ∷
   rw 10 (q48 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw⁻ 14 (q50 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q52 c4) ∷
   rw 17 (q51 c4) ∷
   rw⁻ 18 (q53 c4) ∷
   rw⁻ 19 (q54 c4) ∷
   rw 13 (q5 c4) ∷
   rw 12 (q55 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 12 (q50 c4) ∷
   rw 13 (q51 c4) ∷
   rw⁻ 14 (q52 c4) ∷
   rw 15 (q51 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 17 (q54 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 12 (q56 c4) ∷
   rw 10 (q55 c4) ∷
   rw 13 (q14 c4) ∷
   rw 12 (q57 c4) ∷
   rw 13 (q58 c4) ∷
   rw 14 (q59 c4) ∷
   rw 15 (q58 c4) ∷
   rw 16 (q60 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q61 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw 12 (q25 c4) ∷
   rw 16 (q63 c4) ∷
   rw 15 (q64 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw 17 (q66 c4) ∷
   rw⁻ 18 (q65 c4) ∷
   rw⁻ 19 (q67 c4) ∷
   rw⁻ 15 (q63 c4) ∷
   rw⁻ 14 (q68 c4) ∷
   rw 14 (q63 c4) ∷
   rw 13 (q64 c4) ∷
   rw⁻ 14 (q65 c4) ∷
   rw 15 (q66 c4) ∷
   rw⁻ 16 (q65 c4) ∷
   rw⁻ 17 (q67 c4) ∷
   rw⁻ 13 (q63 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw 13 (q25 c4) ∷
   rw⁻ 16 (q71 c4) ∷
   rw 15 (q72 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 13 (q72 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw 14 (q73 c4) ∷
   rw 14 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 3 (q76 c4) ∷
   rw 5 (q77 c4) ∷
   rw 7 (q77 c4) ∷
   rw 0 (q78 c4) ∷
   rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 2091 (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q81 : Ws → Eqn
  q81 c4 = wpE 1110 c4
  q82 : Ws → Eqn
  q82 c4 = sE 2144 (lem-box-perm-3421-at03243240 c4)
  q83 : Ws → Eqn
  q83 c4 = sE 2142 (lem-CKc-box-at0312203441 c4)
  q84 : Ws → Eqn
  q84 c4 = sE 2145 (lem-box-perm-4312-at0312203441 c4)
  q85 : Ws → Eqn
  q85 c4 = wpE 1111 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 1249 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 2143 (lem-CKc-box-at033440 c4)
  q88 : Ws → Eqn
  q88 c4 = sE 1333 (lem-box-perm-1324-at033440 c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 167 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 341 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 1269 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wpE 1112 c4
  q93 : Ws → Eqn
  q93 c4 = sE 2147 (lem-nf-rel-266at0 c4)

-- F1-rel-266@0: 166 steps
lem-F1-rel-266at0 : Ws → ⟪ (ℓ "亁俄俄亁丢亄俄俄亄丢侧亄俄俄亄丢亁俄俄亁丢") ⟫ʷ ≈ ⟪ (ℓ "亇侧侧亇丢亄侧侧亄丢俄亄侧侧亄丢亇侧侧亇丢") ⟫ʷ
lem-F1-rel-266at0 c4 = derive (ℓ "亁俄俄亁丢亄俄俄亄丢侧亄俄俄亄丢亁俄俄亁丢") (ℓ "亇侧侧亇丢亄侧侧亄丢俄亄侧侧亄丢亇侧侧亇丢")
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 12 (q2 c4) ∷
   rw 13 (q2 c4) ∷
   rw 17 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 1 (q80 c4) ∷
   rw 5 (q80 c4) ∷
   rw 10 (q80 c4) ∷
   rw 14 (q80 c4) ∷
   re 8 1 (ℓ "佯亝俗亝俛") ∷
   re 10 1 (ℓ "丨") ∷
   re 12 1 (ℓ "丩") ∷
   rw 0 (q81 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw 5 (q35 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 7 (q38 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw 9 (q38 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 11 (q30 c4) ∷
   rw 12 (q32 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw 7 (q27 c4) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 8 (q35 c4) ∷
   rw 10 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 10 (q38 c4) ∷
   rw⁻ 11 (q39 c4) ∷
   rw 12 (q38 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 10 (q45 c4) ∷
   rw 9 (q46 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 8 (q82 c4) ∷
   rw 8 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw 11 (q25 c4) ∷
   rw 15 (q63 c4) ∷
   rw 14 (q64 c4) ∷
   rw⁻ 15 (q65 c4) ∷
   rw 16 (q66 c4) ∷
   rw⁻ 17 (q65 c4) ∷
   rw⁻ 18 (q67 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw⁻ 13 (q68 c4) ∷
   rw 13 (q63 c4) ∷
   rw 12 (q64 c4) ∷
   rw⁻ 13 (q65 c4) ∷
   rw 14 (q66 c4) ∷
   rw⁻ 15 (q65 c4) ∷
   rw⁻ 16 (q67 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw 12 (q82 c4) ∷
   rw 12 (q83 c4) ∷
   rw 15 (q84 c4) ∷
   rw 15 (q25 c4) ∷
   rw⁻ 18 (q85 c4) ∷
   rw 17 (q86 c4) ∷
   rw⁻ 16 (q85 c4) ∷
   rw 15 (q86 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 16 (q47 c4) ∷
   rw 16 (q87 c4) ∷
   rw 19 (q88 c4) ∷
   rw 19 (q25 c4) ∷
   rw 23 (q63 c4) ∷
   rw 22 (q64 c4) ∷
   rw⁻ 23 (q65 c4) ∷
   rw 24 (q66 c4) ∷
   rw⁻ 25 (q65 c4) ∷
   rw⁻ 26 (q67 c4) ∷
   rw⁻ 22 (q63 c4) ∷
   rw⁻ 21 (q68 c4) ∷
   rw 21 (q63 c4) ∷
   rw 20 (q64 c4) ∷
   rw⁻ 21 (q65 c4) ∷
   rw 22 (q66 c4) ∷
   rw⁻ 23 (q65 c4) ∷
   rw⁻ 24 (q67 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 19 (q68 c4) ∷
   rw⁻ 20 (q25 c4) ∷
   rw 20 (q47 c4) ∷
   rw 20 (q87 c4) ∷
   rw 23 (q88 c4) ∷
   rw 23 (q25 c4) ∷
   rw⁻ 26 (q85 c4) ∷
   rw 25 (q86 c4) ∷
   rw⁻ 24 (q85 c4) ∷
   rw 23 (q86 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw 3 (q75 c4) ∷
   rw 5 (q76 c4) ∷
   rw 8 (q89 c4) ∷
   rw 9 (q90 c4) ∷
   rw 10 (q91 c4) ∷
   rw 11 (q90 c4) ∷
   rw 12 (q89 c4) ∷
   rw 13 (q90 c4) ∷
   rw 16 (q73 c4) ∷
   rw 0 (q92 c4) ∷
   rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = sE 2092 (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q95 : Ws → Eqn
  q95 c4 = wpE 1119 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 1120 c4
  q97 : Ws → Eqn
  q97 c4 = sE 2148 (lem-nf-rel-267at0 c4)

-- F1-rel-267@0: 18 steps
lem-F1-rel-267at0 : Ws → ⟪ (ℓ "亁俄俄亁丢亄俄俄亄丢侧侧亄俄俄亄丢亁俄俄亁丢") ⟫ʷ ≈ ⟪ (ℓ "亄俄俄亄丢侧侧亄俄俄亄丢侧侧") ⟫ʷ
lem-F1-rel-267at0 c4 = derive (ℓ "亁俄俄亁丢亄俄俄亄丢侧侧亄俄俄亄丢亁俄俄亁丢") (ℓ "亄俄俄亄丢侧侧亄俄俄亄丢侧侧")
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 13 (q2 c4) ∷
   rw 14 (q2 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q2 c4) ∷
   rw 1 (q80 c4) ∷
   rw 5 (q80 c4) ∷
   rw 8 (q94 c4) ∷
   rw 10 (q80 c4) ∷
   rw 14 (q80 c4) ∷
   rw⁻ 0 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw⁻ 0 (q97 c4) ∷ []) Eq.refl
