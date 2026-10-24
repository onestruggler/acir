{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD043 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D043 (Sᴰ : SD043) where

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
  lem-comm-CCZ134-CX02 : Ws → St 1300
  lem-comm-CCZ134-CX02 = pickᴰ 0 Sᴰ
  lem-comm-TOFF304-CX12 : Ws → St 1357
  lem-comm-TOFF304-CX12 = pickᴰ 1 Sᴰ
  lem-comm-CCZ123-CX04 : Ws → St 1358
  lem-comm-CCZ123-CX04 = pickᴰ 2 Sᴰ
  lem-comm-CCZ134-CSd02 : Ws → St 1359
  lem-comm-CCZ134-CSd02 = pickᴰ 3 Sᴰ
  lem-comm-TOFF302-CS14 : Ws → St 1360
  lem-comm-TOFF302-CS14 = pickᴰ 4 Sᴰ
  lem-comm-TOFF302-CSd14 : Ws → St 339
  lem-comm-TOFF302-CSd14 = pickᴰ 5 Sᴰ
  lem-comm-TOFF302-CX14 : Ws → St 1361
  lem-comm-TOFF302-CX14 = pickᴰ 6 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 7 Sᴰ
  lem-box-cP-at033440 : Ws → St 1125
  lem-box-cP-at033440 = pickᴰ 8 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1332
  lem-box-perm-1324-at03243240 = pickᴰ 9 Sᴰ
  lem-box2-at0310243142 : Ws → St 1340
  lem-box2-at0310243142 = pickᴰ 10 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 11 Sᴰ
  lem-box-perm-4213-at03243240 : Ws → St 1550
  lem-box-perm-4213-at03243240 = pickᴰ 12 Sᴰ
  lem-box-perm-4132-at03243240 : Ws → St 1551
  lem-box-perm-4132-at03243240 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1125 (lem-box-cP-at033440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1332 (lem-box-perm-1324-at03243240 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q4 : Ws → Eqn
  q4 c4 = wpE 301 c4
  q5 : Ws → Eqn
  q5 c4 = sE 1360 (lem-comm-TOFF302-CS14 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1233 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = sE 339 (lem-comm-TOFF302-CSd14 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 1041 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 272 c4
  q10 : Ws → Eqn
  q10 c4 = wlE 792 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1359 (lem-comm-CCZ134-CSd02 c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 888 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 1035 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 691 c4
  q15 : Ws → Eqn
  q15 c4 = sE 1357 (lem-comm-TOFF304-CX12 c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 1036 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 1037 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 1038 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 758 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 1039 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 41 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 765 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1358 (lem-comm-CCZ123-CX04 c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 764 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 763 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 618 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 1040 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 1313 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wlE 1252 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 1006 c4
  q31 : Ws → Eqn
  q31 c4 = sE 1361 (lem-comm-TOFF302-CX14 c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 1005 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 1190 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 1312 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 1314 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 1136 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 296 c4
  q38 : Ws → Eqn
  q38 c4 = wlE 1220 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1300 (lem-comm-CCZ134-CX02 c4)
  q40 : Ws → Eqn
  q40 c4 = wlE 1221 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 1003 c4
  q42 : Ws → Eqn
  q42 c4 = wlE 960 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 1137 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 1138 c4
  q45 : Ws → Eqn
  q45 c4 = sE 1550 (lem-box-perm-4213-at03243240 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1340 (lem-box2-at0310243142 c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 1025 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 1026 c4
  q49 : Ws → Eqn
  q49 c4 = eqn (ℓ "丌京") (ℓ "京丌") (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (ℓ "不京") (ℓ "京不") (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q51 : Ws → Eqn
  q51 c4 = wlE 1206 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1007 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 220 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 1008 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 1222 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 1223 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 261 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 1224 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 1027 c4
  q60 : Ws → Eqn
  q60 c4 = wpE 1132 c4
  q61 : Ws → Eqn
  q61 c4 = wpE 1133 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1134 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 103 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 1135 c4

-- L-CCZ-0 part1: 500 steps
lem-L-CCZ-0-part1 : Ws → ⟪ (ℓ "佯亝丨亝丩亖亨亝亨丨亝亨丩亖亜亪五亩亜亪五亪五五丯亪五交亢交亢五丰亪五亩亜亪五佨") ⟫ʷ ≈ ⟪ (ℓ "亝亨丨亝亨丩亖亜亨亝亨亨丨亝亨亨丩亖亜亜亪京乕乁交乖乁丨京亢交亢五亩亜亪五亪五五丯亪五五丰亪五五亩亜亜亪五五") ⟫ʷ
lem-L-CCZ-0-part1 c4 = derive (ℓ "佯亝丨亝丩亖亨亝亨丨亝亨丩亖亜亪五亩亜亪五亪五五丯亪五交亢交亢五丰亪五亩亜亪五佨") (ℓ "亝亨丨亝亨丩亖亜亨亝亨亨丨亝亨亨丩亖亜亜亪京乕乁交乖乁丨京亢交亢五亩亜亪五亪五五丯亪五五丰亪五五亩亜亜亪五五")
  (rw⁻ 27 (q1 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw 27 (q3 c4) ∷
   rw 31 (q4 c4) ∷
   rw 30 (q5 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw 32 (q7 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw 29 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw 30 (q7 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 31 (q10 c4) ∷
   rw 30 (q11 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw 28 (q11 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q2 c4) ∷
   rw 29 (q1 c4) ∷
   rw⁻ 33 (q12 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 33 (q14 c4) ∷
   rw 34 (q15 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw 36 (q15 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw 32 (q12 c4) ∷
   rw 31 (q19 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw 32 (q15 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw 34 (q15 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw 30 (q12 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw 29 (q19 c4) ∷
   rw 32 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 32 (q23 c4) ∷
   rw 33 (q24 c4) ∷
   rw 34 (q23 c4) ∷
   rw 35 (q25 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw 32 (q26 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 31 (q1 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw 31 (q3 c4) ∷
   rw 35 (q4 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw 33 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw 34 (q7 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q9 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw 32 (q3 c4) ∷
   rw⁻ 36 (q28 c4) ∷
   rw⁻ 35 (q29 c4) ∷
   rw⁻ 36 (q30 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q32 c4) ∷
   rw 39 (q31 c4) ∷
   rw⁻ 40 (q33 c4) ∷
   rw⁻ 41 (q34 c4) ∷
   rw 35 (q28 c4) ∷
   rw 34 (q35 c4) ∷
   rw⁻ 34 (q28 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw 35 (q31 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q33 c4) ∷
   rw⁻ 39 (q34 c4) ∷
   rw 33 (q28 c4) ∷
   rw⁻ 34 (q36 c4) ∷
   rw 32 (q35 c4) ∷
   rw 35 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 35 (q39 c4) ∷
   rw 36 (q40 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q41 c4) ∷
   rw⁻ 34 (q37 c4) ∷
   rw 35 (q42 c4) ∷
   rw⁻ 33 (q43 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw⁻ 37 (q44 c4) ∷
   rw 37 (q37 c4) ∷
   rw 36 (q38 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q40 c4) ∷
   rw 39 (q39 c4) ∷
   rw 40 (q41 c4) ∷
   rw⁻ 36 (q37 c4) ∷
   rw⁻ 35 (q44 c4) ∷
   rw 35 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 35 (q39 c4) ∷
   rw 36 (q40 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q41 c4) ∷
   rw⁻ 34 (q37 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw 35 (q2 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 39 (q14 c4) ∷
   rw 40 (q15 c4) ∷
   rw⁻ 41 (q16 c4) ∷
   rw 42 (q15 c4) ∷
   rw⁻ 43 (q17 c4) ∷
   rw⁻ 44 (q18 c4) ∷
   rw 38 (q12 c4) ∷
   rw 37 (q19 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 37 (q14 c4) ∷
   rw 38 (q15 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw 40 (q15 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 42 (q18 c4) ∷
   rw 36 (q12 c4) ∷
   rw⁻ 37 (q20 c4) ∷
   rw 35 (q19 c4) ∷
   rw 38 (q21 c4) ∷
   rw 37 (q22 c4) ∷
   rw 38 (q23 c4) ∷
   rw 39 (q24 c4) ∷
   rw 40 (q23 c4) ∷
   rw 41 (q25 c4) ∷
   rw⁻ 37 (q21 c4) ∷
   rw 38 (q26 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw 37 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw 40 (q5 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   rw 42 (q7 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw 39 (q4 c4) ∷
   rw 38 (q5 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw 40 (q7 c4) ∷
   rw⁻ 41 (q6 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw 38 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 3 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 6 (q38 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q39 c4) ∷
   rw 10 (q41 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 5 (q48 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 6 (q52 c4) ∷
   rw 8 (q53 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q39 c4) ∷
   rw 8 (q41 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 5 (q59 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 15 (q34 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 13 (q34 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q62 c4) ∷
   rw 6 (q61 c4) ∷
   rw 9 (q37 c4) ∷
   rw 8 (q38 c4) ∷
   rw 9 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q41 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw 8 (q3 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 15 (q33 c4) ∷
   rw⁻ 11 (q53 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw 10 (q53 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q33 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 12 (q47 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q39 c4) ∷
   rw 14 (q40 c4) ∷
   rw 15 (q39 c4) ∷
   rw 16 (q41 c4) ∷
   rw⁻ 17 (q50 c4) ∷
   rw 11 (q48 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 10 (q47 c4) ∷
   rw 12 (q52 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 17 (q33 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 10 (q48 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q39 c4) ∷
   rw 14 (q41 c4) ∷
   rw⁻ 15 (q50 c4) ∷
   rw 9 (q48 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw 11 (q3 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 17 (q31 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw⁻ 13 (q55 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 11 (q55 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q56 c4) ∷
   rw 14 (q57 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw 12 (q57 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q47 c4) ∷
   rw⁻ 16 (q48 c4) ∷
   rw⁻ 15 (q49 c4) ∷
   rw 16 (q38 c4) ∷
   rw 17 (q39 c4) ∷
   rw 18 (q40 c4) ∷
   rw 19 (q39 c4) ∷
   rw 20 (q41 c4) ∷
   rw⁻ 21 (q50 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q51 c4) ∷
   rw⁻ 14 (q47 c4) ∷
   rw 16 (q52 c4) ∷
   rw 18 (q53 c4) ∷
   rw⁻ 17 (q30 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 17 (q53 c4) ∷
   rw 14 (q54 c4) ∷
   rw⁻ 14 (q48 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw 14 (q38 c4) ∷
   rw 15 (q39 c4) ∷
   rw 16 (q40 c4) ∷
   rw 17 (q39 c4) ∷
   rw 18 (q41 c4) ∷
   rw⁻ 19 (q50 c4) ∷
   rw 13 (q48 c4) ∷
   rw⁻ 14 (q55 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw 19 (q53 c4) ∷
   rw⁻ 18 (q30 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw 21 (q31 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 18 (q53 c4) ∷
   rw⁻ 17 (q55 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 16 (q30 c4) ∷
   rw 17 (q31 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q33 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 15 (q55 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q3 c4) ∷
   rw⁻ 19 (q58 c4) ∷
   rw 18 (q59 c4) ∷
   rw⁻ 17 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw⁻ 17 (q3 c4) ∷
   rw 17 (q3 c4) ∷
   rw⁻ 21 (q60 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw 20 (q60 c4) ∷
   rw 19 (q61 c4) ∷
   rw⁻ 19 (q60 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw 18 (q60 c4) ∷
   rw⁻ 19 (q62 c4) ∷
   rw 17 (q61 c4) ∷
   rw 20 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw⁻ 20 (q63 c4) ∷
   rw⁻ 18 (q64 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 19 (q3 c4) ∷
   rw⁻ 22 (q44 c4) ∷
   rw 22 (q37 c4) ∷
   rw 21 (q38 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q40 c4) ∷
   rw 24 (q39 c4) ∷
   rw 25 (q41 c4) ∷
   rw⁻ 21 (q37 c4) ∷
   rw⁻ 20 (q44 c4) ∷
   rw 20 (q37 c4) ∷
   rw 19 (q38 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q40 c4) ∷
   rw 22 (q39 c4) ∷
   rw 23 (q41 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q2 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw 25 (q15 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 28 (q17 c4) ∷
   rw⁻ 29 (q18 c4) ∷
   rw 23 (q12 c4) ∷
   rw 22 (q19 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 23 (q15 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 25 (q15 c4) ∷
   rw⁻ 26 (q17 c4) ∷
   rw⁻ 27 (q18 c4) ∷
   rw 21 (q12 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw 20 (q19 c4) ∷
   rw 23 (q21 c4) ∷
   rw 22 (q22 c4) ∷
   rw 23 (q23 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wpE 1030 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 161 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 135 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 1140 c4
  q69 : Ws → Eqn
  q69 c4 = sE 1551 (lem-box-perm-4132-at03243240 c4)

-- L-CCZ-0 part3: 8 steps
lem-L-CCZ-0-part3 : Ws → ⟪ (ℓ "亝丨亝丩亖亝丨亝亨丩亖亜亪亩亪亪五丯亪五五五丰亪五五五亩亜亜亜亪五五五佯") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-L-CCZ-0-part3 c4 = derive (ℓ "亝丨亝丩亖亝丨亝亨丩亖亜亪亩亪亪五丯亪五五五丰亪五五五亩亜亜亜亪五五五佯") (ℓ "佤")
  (rw 16 (q65 c4) ∷
   rw 18 (q66 c4) ∷
   rw 18 (q66 c4) ∷
   rw 20 (q66 c4) ∷
   rw 22 (q67 c4) ∷
   rw 24 (q66 c4) ∷
   rw 0 (q68 c4) ∷
   rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 1315 (lit c4)

-- L-CX01-2: 2 steps
lem-L-CX01-2 : Ws → ⟪ (ℓ "亊侬侬亊丢") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
lem-L-CX01-2 c4 = derive (ℓ "亊侬侬亊丢") (ℓ "亲")
  (rw 1 (q70 c4) ∷
   rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = wlE 1316 (lit c4)

-- L-CX10-2: 2 steps
lem-L-CX10-2 : Ws → ⟪ (ℓ "亇侬侬亇丢") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
lem-L-CX10-2 c4 = derive (ℓ "亇侬侬亇丢") (ℓ "亱")
  (rw 1 (q70 c4) ∷
   rw 0 (q72 c4) ∷ []) Eq.refl
