{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD023 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D023 (Sᴰ : SD023) where

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
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 2 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 4 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 5 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 6 Sᴰ
  lem-comm-CCZ024-CX31 : Ws → St 1058
  lem-comm-CCZ024-CX31 = pickᴰ 7 Sᴰ
  lem-comm-CS24-TOFF301 : Ws → St 75
  lem-comm-CS24-TOFF301 = pickᴰ 8 Sᴰ
  lem-comm-TOFF213-CSd04 : Ws → St 296
  lem-comm-TOFF213-CSd04 = pickᴰ 9 Sᴰ
  lem-comm-CK02-TOFF413 : Ws → St 1172
  lem-comm-CK02-TOFF413 = pickᴰ 10 Sᴰ
  lem-comm-CX40-TOFF213 : Ws → St 1173
  lem-comm-CX40-TOFF213 = pickᴰ 11 Sᴰ
  lem-comm-TOFF213-CX40 : Ws → St 1174
  lem-comm-TOFF213-CX40 = pickᴰ 12 Sᴰ
  lem-comm-TOFF413-CK02 : Ws → St 1175
  lem-comm-TOFF413-CK02 = pickᴰ 13 Sᴰ
  lem-comm-CCZ124-CK03 : Ws → St 1176
  lem-comm-CCZ124-CK03 = pickᴰ 14 Sᴰ
  lem-comm-CK03-CCZ124 : Ws → St 1177
  lem-comm-CK03-CCZ124 = pickᴰ 15 Sᴰ
  lem-comm-CX20-TOFF413 : Ws → St 1178
  lem-comm-CX20-TOFF413 = pickᴰ 16 Sᴰ
  lem-comm-TOFF413-CX20 : Ws → St 1179
  lem-comm-TOFF413-CX20 = pickᴰ 17 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 1029
  lem-sym-ab-at0214203143 = pickᴰ 18 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 1031
  lem-sym-ab-at0314203142 = pickᴰ 19 Sᴰ
  lem-sym-ab-at04203243 : Ws → St 969
  lem-sym-ab-at04203243 = pickᴰ 20 Sᴰ
  lem-sym-ab-at0213243041 : Ws → St 730
  lem-sym-ab-at0213243041 = pickᴰ 21 Sᴰ
  lem-sym-ab-at0214233041 : Ws → St 1072
  lem-sym-ab-at0214233041 = pickᴰ 22 Sᴰ
  lem-box-tQ-at0410213243 : Ws → St 139
  lem-box-tQ-at0410213243 = pickᴰ 23 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 24 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 249
  lem-box-tQ-at0214203143 = pickᴰ 25 Sᴰ
  lem-box-tQ-at04122041 : Ws → St 403
  lem-box-tQ-at04122041 = pickᴰ 26 Sᴰ
  lem-box-tQ-at04233042 : Ws → St 1180
  lem-box-tQ-at04233042 = pickᴰ 27 Sᴰ
  lem-box-tQ-at0412213043 : Ws → St 1181
  lem-box-tQ-at0412213043 = pickᴰ 28 Sᴰ
  lem-box-tQ-at0413203142 : Ws → St 422
  lem-box-tQ-at0413203142 = pickᴰ 29 Sᴰ
  lem-box-tQ-at0413213240 : Ws → St 440
  lem-box-tQ-at0413213240 = pickᴰ 30 Sᴰ
  lem-box-tQ-at0440 : Ws → St 425
  lem-box-tQ-at0440 = pickᴰ 31 Sᴰ
  lem-P-box-at0410233241 : Ws → St 1182
  lem-P-box-at0410233241 = pickᴰ 32 Sᴰ
  lem-P-box-at04103143 : Ws → St 1183
  lem-P-box-at04103143 = pickᴰ 33 Sᴰ
  lem-P-box-at04122041 : Ws → St 1184
  lem-P-box-at04122041 = pickᴰ 34 Sᴰ
  lem-P-box-at0412233041 : Ws → St 1185
  lem-P-box-at0412233041 = pickᴰ 35 Sᴰ
  lem-P-box-at0413203142 : Ws → St 1186
  lem-P-box-at0413203142 = pickᴰ 36 Sᴰ
  lem-P-box-at0440 : Ws → St 1187
  lem-P-box-at0440 = pickᴰ 37 Sᴰ
  lem-P-box-at0413213240 : Ws → St 1188
  lem-P-box-at0413213240 = pickᴰ 38 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 39 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 40 Sᴰ
  lem-box-cP-at043043 : Ws → St 999
  lem-box-cP-at043043 = pickᴰ 41 Sᴰ
  lem-pairs-at0210213443 : Ws → St 1132
  lem-pairs-at0210213443 = pickᴰ 42 Sᴰ
  lem-pairs-at0214233041 : Ws → St 1134
  lem-pairs-at0214233041 = pickᴰ 43 Sᴰ
  lem-sym-bc-at0210243143 : Ws → St 1014
  lem-sym-bc-at0210243143 = pickᴰ 44 Sᴰ
  lem-sym-bc-at0310243142 : Ws → St 1144
  lem-sym-bc-at0310243142 = pickᴰ 45 Sᴰ
  lem-CSdu-box-3-at0310213442 : Ws → St 1189
  lem-CSdu-box-3-at0310213442 = pickᴰ 46 Sᴰ
  lem-box-cP-at0410233241 : Ws → St 1190
  lem-box-cP-at0410233241 = pickᴰ 47 Sᴰ
  lem-box-cP-at04103143 : Ws → St 1191
  lem-box-cP-at04103143 = pickᴰ 48 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1192
  lem-box-cP-at04122041 = pickᴰ 49 Sᴰ
  lem-box-cP-at0412233041 : Ws → St 1193
  lem-box-cP-at0412233041 = pickᴰ 50 Sᴰ
  lem-box-cP-at0413203142 : Ws → St 1194
  lem-box-cP-at0413203142 = pickᴰ 51 Sᴰ
  lem-box-cP-at0413213240 : Ws → St 1195
  lem-box-cP-at0413213240 = pickᴰ 52 Sᴰ
  lem-box-cP-at0440 : Ws → St 1196
  lem-box-cP-at0440 = pickᴰ 53 Sᴰ
  lem-box-perm-1324-at04203243 : Ws → St 1197
  lem-box-perm-1324-at04203243 = pickᴰ 54 Sᴰ
  lem-pairs-at0410213243 : Ws → St 1198
  lem-pairs-at0410213243 = pickᴰ 55 Sᴰ
  lem-sym-bc-at04122041 : Ws → St 1199
  lem-sym-bc-at04122041 = pickᴰ 56 Sᴰ
  lem-sym-bc-at0412233041 : Ws → St 1200
  lem-sym-bc-at0412233041 = pickᴰ 57 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1284 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1432 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (ℓ "与亦") (ℓ "亦与") (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q5 : Ws → Eqn
  q5 c4 = wlE 831 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 746 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 34 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 1285 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 1433 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 954 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 35 c4
  q14 : Ws → Eqn
  q14 c4 = wlE 807 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1380 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 33 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 21 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 179 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 39 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 37 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 1421 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 760 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 1143 c4
  q24 : Ws → Eqn
  q24 c4 = wlE 195 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1173 (lem-comm-CX40-TOFF213 c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1422 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 193 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 921 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 1275 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 808 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 1286 c4
  q32 : Ws → Eqn
  q32 c4 = wlE 321 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wpE 1276 c4
  q34 : Ws → Eqn
  q34 c4 = wpE 161 c4
  q35 : Ws → Eqn
  q35 c4 = wlE 1434 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 1287 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 746 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1435 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 653 c4
  q40 : Ws → Eqn
  q40 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 1288 c4
  q42 : Ws → Eqn
  q42 c4 = sE 1058 (lem-comm-CCZ024-CX31 c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 748 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1174 (lem-comm-TOFF213-CX40 c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 655 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 1289 c4
  q47 : Ws → Eqn
  q47 c4 = wlE 1436 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 1437 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 1290 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 1438 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 1291 c4

-- F4-CS2-CS2 @0213243140: 286 steps
lem-F4-CS2-CS2-at0213243140 : Ws → ⟪ (ℓ "与俊与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与俊与") ⟫ʷ
lem-F4-CS2-CS2-at0213243140 c4 = derive (ℓ "与俊与俊") (ℓ "俊与俊与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乺") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q27 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (ℓ "乹") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw 7 (q25 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   re 4 1 (ℓ "俈") ∷
   re 6 1 (ℓ "俉") ∷
   re 2 5 (ℓ "俊") ∷
   rw⁻ 3 (q35 c4) ∷
   re 2 1 (ℓ "佔亓俈亓俉") ∷
   re 4 1 (ℓ "乹") ∷
   re 6 1 (ℓ "乺") ∷
   rw⁻ 3 (q36 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q18 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q24 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (ℓ "俈") ∷
   re 8 1 (ℓ "俉") ∷
   re 4 5 (ℓ "俊") ∷
   rw⁻ 1 (q47 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw⁻ 4 (q49 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (ℓ "俈") ∷
   re 8 1 (ℓ "俉") ∷
   re 4 5 (ℓ "俊") ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 4 1 (ℓ "佔亓俈亓俉") ∷
   re 6 1 (ℓ "乹") ∷
   re 8 1 (ℓ "乺") ∷
   rw⁻ 5 (q36 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q18 c4) ∷
   rw 15 (q42 c4) ∷
   rw 16 (q17 c4) ∷
   rw 17 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw 13 (q44 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q42 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (ℓ "俈") ∷
   re 10 1 (ℓ "俉") ∷
   re 6 5 (ℓ "俊") ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   re 5 1 (ℓ "佔亓俈亓俉") ∷
   re 7 1 (ℓ "乹") ∷
   re 9 1 (ℓ "乺") ∷
   rw⁻ 6 (q51 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (ℓ "俈") ∷
   re 10 1 (ℓ "俉") ∷
   re 6 5 (ℓ "俊") ∷
   rw⁻ 4 (q50 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 1029 (lem-sym-ab-at0214203143 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1014 (lem-sym-bc-at0210243143 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1132 (lem-pairs-at0210213443 c4)

-- box-perm-1423 @0214203143: 3 steps
lem-box-perm-1423-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "佢") ⟫ʷ
lem-box-perm-1423-at0214203143 c4 = derive (ℓ "佔") (ℓ "佢")
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wpE 1297 c4
  q56 : Ws → Eqn
  q56 c4 = wpE 1283 c4
  q57 : Ws → Eqn
  q57 c4 = eqn (ℓ "亦丢") (ℓ "丢亦") (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q58 : Ws → Eqn
  q58 c4 = sE 296 (lem-comm-TOFF213-CSd04 c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 1282 c4
  q60 : Ws → Eqn
  q60 c4 = wpE 1298 c4

-- F4-CS2-S2 @0213243140: 17 steps
lem-F4-CS2-S2-at0213243140 : Ws → ⟪ (ℓ "与俊与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与俊与") ⟫ʷ
lem-F4-CS2-S2-at0213243140 c4 = derive (ℓ "与俊与丽") (ℓ "丽与俊与")
  (rw⁻ 2 (q55 c4) ∷
   re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   rw⁻ 2 (q56 c4) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q57 c4) ∷
   rw 5 (q58 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "俈") ∷
   re 7 1 (ℓ "俉") ∷
   re 3 5 (ℓ "俊") ∷
   rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 1446 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 1301 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 1447 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 1302 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 1448 (lit c4)

-- F4-CS2-I @0213243140: 15 steps
lem-F4-CS2-I-at0213243140 : Ws → ⟪ (ℓ "与俊与上") ⟫ʷ ≈ ⟪ (ℓ "上与俊与") ⟫ʷ
lem-F4-CS2-I-at0213243140 c4 = derive (ℓ "与俊与上") (ℓ "上与俊与")
  (rw 2 (q61 c4) ∷
   re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   rw 2 (q62 c4) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "俈") ∷
   re 7 1 (ℓ "俉") ∷
   re 3 5 (ℓ "俊") ∷
   rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 1451 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 1304 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 1452 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1305 c4
  q70 : Ws → Eqn
  q70 c4 = wlE 1453 (lit c4)

-- F4-CS2-S3 @0213243140: 15 steps
lem-F4-CS2-S3-at0213243140 : Ws → ⟪ (ℓ "与俊与丨") ⟫ʷ ≈ ⟪ (ℓ "丨与俊与") ⟫ʷ
lem-F4-CS2-S3-at0213243140 c4 = derive (ℓ "与俊与丨") (ℓ "丨与俊与")
  (rw⁻ 2 (q66 c4) ∷
   re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "俈") ∷
   re 7 1 (ℓ "俉") ∷
   re 3 5 (ℓ "俊") ∷
   rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = sE 1199 (lem-sym-bc-at04122041 c4)

-- box-perm-1324 @04122041: 1 steps
lem-box-perm-1324-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侚") ⟫ʷ
lem-box-perm-1324-at04122041 c4 = derive (ℓ "侗") (ℓ "侚")
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = sE 1192 (lem-box-cP-at04122041 c4)
  q73 : Ws → Eqn
  q73 c4 = wpE 1324 c4
  q74 : Ws → Eqn
  q74 c4 = eqn (ℓ "与亯") (ℓ "亯与") (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
  q75 : Ws → Eqn
  q75 c4 = sE 1172 (lem-comm-CK02-TOFF413 c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 1475 (lit c4)

-- F4-K2-CS2 @0440: 17 steps
lem-F4-K2-CS2-at0440 : Ws → ⟪ (ℓ "与临与俵") ⟫ʷ ≈ ⟪ (ℓ "俵与临与") ⟫ʷ
lem-F4-K2-CS2-at0440 c4 = derive (ℓ "与临与俵") (ℓ "俵与临与")
  (re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q72 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 1 (q74 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   re 2 1 (ℓ "俳") ∷
   re 4 1 (ℓ "俴") ∷
   re 0 5 (ℓ "俵") ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = sE 1183 (lem-P-box-at04103143 c4)
  q78 : Ws → Eqn
  q78 c4 = sE 1191 (lem-box-cP-at04103143 c4)
  q79 : Ws → Eqn
  q79 c4 = wlE 1474 (lit c4)
  q80 : Ws → Eqn
  q80 c4 = sE 1180 (lem-box-tQ-at04233042 c4)

-- pairs @04103143: 4 steps
lem-pairs-at04103143 : Ws → ⟪ (ℓ "侎") ⟫ʷ ≈ ⟪ (ℓ "侕") ⟫ʷ
lem-pairs-at04103143 c4 = derive (ℓ "侎") (ℓ "侕")
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = sE 969 (lem-sym-ab-at04203243 c4)
  q82 : Ws → Eqn
  q82 c4 = sE 1198 (lem-pairs-at0410213243 c4)
  q83 : Ws → Eqn
  q83 c4 = sE 1200 (lem-sym-bc-at0412233041 c4)

-- box-perm-3241 @04203243: 3 steps
lem-box-perm-3241-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-box-perm-3241-at04203243 c4 = derive (ℓ "侒") (ℓ "侗")
  (rw 0 (q81 c4) ∷
   rw 0 (q82 c4) ∷
   rw 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = sE 1185 (lem-P-box-at0412233041 c4)
  q85 : Ws → Eqn
  q85 c4 = sE 1193 (lem-box-cP-at0412233041 c4)
  q86 : Ws → Eqn
  q86 c4 = wpE 306 c4
  q87 : Ws → Eqn
  q87 c4 = sE 139 (lem-box-tQ-at0410213243 c4)

-- pairs @0412233041: 4 steps
lem-pairs-at0412233041 : Ws → ⟪ (ℓ "侚") ⟫ʷ ≈ ⟪ (ℓ "侍") ⟫ʷ
lem-pairs-at0412233041 c4 = derive (ℓ "侚") (ℓ "侍")
  (rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = wpE 1278 c4
  q89 : Ws → Eqn
  q89 c4 = wpE 1361 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 1535 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 1431 (lit c4)

-- F4-I-CS2 @0440: 15 steps
lem-F4-I-CS2-at0440 : Ws → ⟪ (ℓ "与上与俵") ⟫ʷ ≈ ⟪ (ℓ "俵与上与") ⟫ʷ
lem-F4-I-CS2-at0440 c4 = derive (ℓ "与上与俵") (ℓ "俵与上与")
  (re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q72 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   re 2 1 (ℓ "俳") ∷
   re 4 1 (ℓ "俴") ∷
   re 0 5 (ℓ "俵") ∷
   rw 1 (q91 c4) ∷
   rw⁻ 1 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = wlE 1536 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wpE 1362 c4

-- F4-CS2-I @0440: 15 steps
lem-F4-CS2-I-at0440 : Ws → ⟪ (ℓ "与俵与上") ⟫ʷ ≈ ⟪ (ℓ "上与俵与") ⟫ʷ
lem-F4-CS2-I-at0440 c4 = derive (ℓ "与俵与上") (ℓ "上与俵与")
  (rw 2 (q61 c4) ∷
   re 1 1 (ℓ "侗互俳互俴") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 2 (q92 c4) ∷
   rw 1 (q72 c4) ∷
   rw 4 (q93 c4) ∷
   rw 3 (q64 c4) ∷
   rw 2 (q93 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   re 5 1 (ℓ "俳") ∷
   re 7 1 (ℓ "俴") ∷
   re 3 5 (ℓ "俵") ∷
   rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = wlE 1487 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wlE 1537 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 1538 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = sE 1175 (lem-comm-TOFF413-CK02 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (ℓ "上亯") (ℓ "亯上") (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
  q99 : Ws → Eqn
  q99 c4 = wpE 1363 c4
  q100 : Ws → Eqn
  q100 c4 = wlE 1490 (lit c4)

-- F4-CS2-K2 @0440: 19 steps
lem-F4-CS2-K2-at0440 : Ws → ⟪ (ℓ "与俵与临") ⟫ʷ ≈ ⟪ (ℓ "临与俵与") ⟫ʷ
lem-F4-CS2-K2-at0440 c4 = derive (ℓ "与俵与临") (ℓ "临与俵与")
  (rw⁻ 2 (q94 c4) ∷
   re 1 1 (ℓ "侗互俳互俴") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw⁻ 2 (q95 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q97 c4) ∷
   rw⁻ 6 (q98 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 3 (q97 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = wlE 1498 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 242 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wpE 81 c4
  q104 : Ws → Eqn
  q104 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q105 : Ws → Eqn
  q105 c4 = wpE 91 c4
  q106 : Ws → Eqn
  q106 c4 = wpE 92 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1499 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wpE 87 c4
  q109 : Ws → Eqn
  q109 c4 = wlE 1544 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 1545 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wpE 88 c4
  q112 : Ws → Eqn
  q112 c4 = wpE 32 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 89 c4
  q114 : Ws → Eqn
  q114 c4 = wpE 1373 c4
  q115 : Ws → Eqn
  q115 c4 = wpE 1374 c4
  q116 : Ws → Eqn
  q116 c4 = wlE 1270 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wlE 1546 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = sE 1178 (lem-comm-CX20-TOFF413 c4)
  q119 : Ws → Eqn
  q119 c4 = wpE 1375 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 1376 c4
  q121 : Ws → Eqn
  q121 c4 = wpE 1377 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 1378 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 1547 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 1548 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 181 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = wlE 1549 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wlE 204 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 1505 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 1550 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 1551 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wpE 1379 c4
  q132 : Ws → Eqn
  q132 c4 = wpE 1380 c4
  q133 : Ws → Eqn
  q133 c4 = wpE 1381 c4
  q134 : Ws → Eqn
  q134 c4 = wlE 1552 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = sE 1179 (lem-comm-TOFF413-CX20 c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 1382 c4
  q137 : Ws → Eqn
  q137 c4 = wlE 1553 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 1510 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 1511 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wlE 1554 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 1513 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wlE 1555 (lit c4)

-- F4-CS2-CS2 @0440: 286 steps
lem-F4-CS2-CS2-at0440 : Ws → ⟪ (ℓ "与俵与俵") ⟫ʷ ≈ ⟪ (ℓ "俵与俵与") ⟫ʷ
lem-F4-CS2-CS2-at0440 c4 = derive (ℓ "与俵与俵") (ℓ "俵与俵与")
  (re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q72 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q74 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 10 (q103 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q105 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q106 c4) ∷
   rw⁻ 7 (q102 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q74 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   re 1 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "么") ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 8 (q104 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 5 (q110 c4) ∷
   rw 5 (q114 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 13 (q111 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw 11 (q104 c4) ∷
   rw⁻ 10 (q112 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   rw 8 (q110 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw 9 (q114 c4) ∷
   rw 8 (q116 c4) ∷
   rw 12 (q117 c4) ∷
   rw 11 (q118 c4) ∷
   rw 10 (q119 c4) ∷
   rw 9 (q118 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw 7 (q121 c4) ∷
   rw⁻ 8 (q122 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 3 1 (ℓ "乇") ∷
   rw 4 (q72 c4) ∷
   rw⁻ 3 (q103 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 6 (q123 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw 4 (q104 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 3 (q110 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw⁻ 11 (q111 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q112 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw 6 (q110 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 7 (q114 c4) ∷
   rw 6 (q116 c4) ∷
   rw 10 (q117 c4) ∷
   rw 9 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw 7 (q118 c4) ∷
   rw 6 (q120 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 5 (q121 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q74 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q102 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 2 (q106 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw 3 (q107 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw 5 (q107 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw⁻ 3 (q124 c4) ∷
   rw 10 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw 5 (q127 c4) ∷
   re 4 1 (ℓ "俳") ∷
   re 6 1 (ℓ "俴") ∷
   re 2 5 (ℓ "俵") ∷
   rw⁻ 3 (q128 c4) ∷
   re 2 1 (ℓ "侗互俳互俴") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   rw⁻ 3 (q129 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 4 (q132 c4) ∷
   rw 6 (q42 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 10 (q110 c4) ∷
   rw 9 (q113 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q40 c4) ∷
   rw 12 (q112 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q111 c4) ∷
   rw 9 (q110 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw 5 (q116 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw 5 (q135 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   rw 7 (q135 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw⁻ 7 (q121 c4) ∷
   rw 9 (q116 c4) ∷
   rw⁻ 8 (q120 c4) ∷
   rw 9 (q135 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   rw 11 (q135 c4) ∷
   rw⁻ 12 (q117 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   rw⁻ 9 (q131 c4) ∷
   rw⁻ 3 (q136 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   rw 3 (q137 c4) ∷
   rw 2 (q42 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q112 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 4 (q139 c4) ∷
   re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw⁻ 4 (q140 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw 5 (q103 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw 3 (q103 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 2 (q139 c4) ∷
   rw⁻ 5 (q128 c4) ∷
   re 4 1 (ℓ "侗互俳互俴") ∷
   re 6 1 (ℓ "乇") ∷
   re 8 1 (ℓ "么") ∷
   rw⁻ 5 (q129 c4) ∷
   rw 4 (q72 c4) ∷
   rw⁻ 7 (q130 c4) ∷
   rw⁻ 9 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q133 c4) ∷
   rw⁻ 12 (q110 c4) ∷
   rw 11 (q113 c4) ∷
   rw 12 (q17 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q112 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q111 c4) ∷
   rw 11 (q110 c4) ∷
   rw⁻ 5 (q134 c4) ∷
   rw 7 (q116 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw 7 (q135 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw 9 (q135 c4) ∷
   rw⁻ 10 (q117 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw⁻ 7 (q130 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw 11 (q116 c4) ∷
   rw⁻ 10 (q120 c4) ∷
   rw 11 (q135 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q135 c4) ∷
   rw⁻ 14 (q117 c4) ∷
   rw⁻ 10 (q116 c4) ∷
   rw⁻ 11 (q131 c4) ∷
   rw⁻ 5 (q136 c4) ∷
   rw⁻ 7 (q122 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   rw 5 (q113 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q112 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q111 c4) ∷
   rw 5 (q110 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   re 8 1 (ℓ "俳") ∷
   re 10 1 (ℓ "俴") ∷
   re 6 5 (ℓ "俵") ∷
   rw⁻ 3 (q138 c4) ∷
   rw⁻ 6 (q141 c4) ∷
   re 5 1 (ℓ "侗互俳互俴") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw⁻ 6 (q142 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 8 (q109 c4) ∷
   rw 7 (q108 c4) ∷
   rw⁻ 6 (q109 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   re 8 1 (ℓ "俳") ∷
   re 10 1 (ℓ "俴") ∷
   re 6 5 (ℓ "俵") ∷
   rw⁻ 4 (q141 c4) ∷
   re 2 1 (ℓ "俳") ∷
   re 4 1 (ℓ "俴") ∷
   re 0 5 (ℓ "俵") ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = sE 1197 (lem-box-perm-1324-at04203243 c4)
  q144 : Ws → Eqn
  q144 c4 = sE 999 (lem-box-cP-at043043 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (ℓ "与亨") (ℓ "亨与") (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q146 : Ws → Eqn
  q146 c4 = sE 1177 (lem-comm-CK03-CCZ124 c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 1384 c4
  q148 : Ws → Eqn
  q148 c4 = wlE 1561 (lit c4)

-- F4-K3-CS1 @0440: 19 steps
lem-F4-K3-CS1-at0440 : Ws → ⟪ (ℓ "与主与俭") ⟫ʷ ≈ ⟪ (ℓ "俭与主与") ⟫ʷ
lem-F4-K3-CS1-at0440 c4 = derive (ℓ "与主与俭") (ℓ "俭与主与")
  (re 3 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw 3 (q143 c4) ∷
   rw 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 4 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   re 2 1 (ℓ "俫") ∷
   re 4 1 (ℓ "俬") ∷
   re 0 5 (ℓ "俭") ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = sE 1182 (lem-P-box-at0410233241 c4)
  q150 : Ws → Eqn
  q150 c4 = sE 1190 (lem-box-cP-at0410233241 c4)
  q151 : Ws → Eqn
  q151 c4 = wlE 470 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = sE 1181 (lem-box-tQ-at0412213043 c4)

-- pairs @0410233241: 4 steps
lem-pairs-at0410233241 : Ws → ⟪ (ℓ "侑") ⟫ʷ ≈ ⟪ (ℓ "侘") ⟫ʷ
lem-pairs-at0410233241 c4 = derive (ℓ "侑") (ℓ "侘")
  (rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = wlE 1574 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 1581 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wpE 1393 c4
  q156 : Ws → Eqn
  q156 c4 = wlE 1576 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = sE 1176 (lem-comm-CCZ124-CK03 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (ℓ "上亨") (ℓ "亨上") (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q159 : Ws → Eqn
  q159 c4 = wlE 1577 (lit c4)

-- F4-CS1-K3 @0440: 21 steps
lem-F4-CS1-K3-at0440 : Ws → ⟪ (ℓ "与俭与主") ⟫ʷ ≈ ⟪ (ℓ "主与俭与") ⟫ʷ
lem-F4-CS1-K3-at0440 c4 = derive (ℓ "与俭与主") (ℓ "主与俭与")
  (rw⁻ 2 (q153 c4) ∷
   re 1 1 (ℓ "侒些俫些俬") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw⁻ 2 (q154 c4) ∷
   rw 1 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw⁻ 4 (q155 c4) ∷
   rw 3 (q156 c4) ∷
   rw 4 (q157 c4) ∷
   rw⁻ 5 (q158 c4) ∷
   rw⁻ 2 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw⁻ 3 (q158 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw⁻ 4 (q143 c4) ∷
   re 6 1 (ℓ "俫") ∷
   re 8 1 (ℓ "俬") ∷
   re 4 5 (ℓ "俭") ∷
   rw⁻ 0 (q159 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = wlE 968 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 326 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wpE 749 c4
  q163 : Ws → Eqn
  q163 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q164 : Ws → Eqn
  q164 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q165 : Ws → Eqn
  q165 c4 = wlE 965 (lit c4)
  q166 : Ws → Eqn
  q166 c4 = wlE 969 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wlE 970 (lit c4)

-- CSdu-box-3 @0214203143: 17 steps
lem-CSdu-box-3-at0214203143 : Ws → ⟪ (ℓ "么佔") ⟫ʷ ≈ ⟪ (ℓ "佔么") ⟫ʷ
lem-CSdu-box-3-at0214203143 c4 = derive (ℓ "么佔") (ℓ "佔么")
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q160 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 8 (q106 c4) ∷
   rw⁻ 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw 5 (q165 c4) ∷
   rw 4 (q166 c4) ∷
   rw 3 (q160 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = wlE 964 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wlE 966 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = wlE 967 (lit c4)

-- CSu-box-3 @0214203143: 17 steps
lem-CSu-box-3-at0214203143 : Ws → ⟪ (ℓ "乇佔") ⟫ʷ ≈ ⟪ (ℓ "佔乇") ⟫ʷ
lem-CSu-box-3-at0214203143 c4 = derive (ℓ "乇佔") (ℓ "佔乇")
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q168 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 8 (q106 c4) ∷
   rw⁻ 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 2 (q103 c4) ∷
   rw 5 (q165 c4) ∷
   rw 4 (q169 c4) ∷
   rw 3 (q168 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = sE 1184 (lem-P-box-at04122041 c4)
  q172 : Ws → Eqn
  q172 c4 = sE 440 (lem-box-tQ-at0413213240 c4)

-- pairs @04122041: 4 steps
lem-pairs-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侟") ⟫ʷ
lem-pairs-at04122041 c4 = derive (ℓ "侗") (ℓ "侟")
  (rw⁻ 0 (q171 c4) ∷
   rw 1 (q72 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q172 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = sE 1187 (lem-P-box-at0440 c4)
  q174 : Ws → Eqn
  q174 c4 = sE 1196 (lem-box-cP-at0440 c4)
  q175 : Ws → Eqn
  q175 c4 = wpE 317 c4
  q176 : Ws → Eqn
  q176 c4 = sE 422 (lem-box-tQ-at0413203142 c4)

-- pairs @0440: 4 steps
lem-pairs-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侜") ⟫ʷ
lem-pairs-at0440 c4 = derive (ℓ "侔") (ℓ "侜")
  (rw⁻ 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 4 (q175 c4) ∷
   rw⁻ 0 (q176 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = sE 1186 (lem-P-box-at0413203142 c4)
  q178 : Ws → Eqn
  q178 c4 = sE 1194 (lem-box-cP-at0413203142 c4)
  q179 : Ws → Eqn
  q179 c4 = sE 425 (lem-box-tQ-at0440 c4)

-- pairs @0413203142: 4 steps
lem-pairs-at0413203142 : Ws → ⟪ (ℓ "侜") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-pairs-at0413203142 c4 = derive (ℓ "侜") (ℓ "侔")
  (rw⁻ 0 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 0 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = sE 1188 (lem-P-box-at0413213240 c4)
  q181 : Ws → Eqn
  q181 c4 = sE 1195 (lem-box-cP-at0413213240 c4)
  q182 : Ws → Eqn
  q182 c4 = wpE 1323 c4
  q183 : Ws → Eqn
  q183 c4 = sE 403 (lem-box-tQ-at04122041 c4)

-- pairs @0413213240: 4 steps
lem-pairs-at0413213240 : Ws → ⟪ (ℓ "侟") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-pairs-at0413213240 c4 = derive (ℓ "侟") (ℓ "侗")
  (rw⁻ 0 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw⁻ 0 (q183 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = wlE 1615 (lit c4)
  q185 : Ws → Eqn
  q185 c4 = wlE 707 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = wpE 914 c4
  q187 : Ws → Eqn
  q187 c4 = wlE 1616 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = wlE 1502 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = wlE 1617 (lit c4)

-- CSu-box-3 @04122041: 17 steps
lem-CSu-box-3-at04122041 : Ws → ⟪ (ℓ "乹侗") ⟫ʷ ≈ ⟪ (ℓ "侗乹") ⟫ʷ
lem-CSu-box-3-at04122041 c4 = derive (ℓ "乹侗") (ℓ "侗乹")
  (rw 1 (q72 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 1 (q184 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q186 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 5 (q187 c4) ∷
   rw 4 (q188 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = wlE 1618 (lit c4)
  q191 : Ws → Eqn
  q191 c4 = wlE 1500 (lit c4)
  q192 : Ws → Eqn
  q192 c4 = wlE 1619 (lit c4)

-- CSdu-box-3 @04122041: 17 steps
lem-CSdu-box-3-at04122041 : Ws → ⟪ (ℓ "乺侗") ⟫ʷ ≈ ⟪ (ℓ "侗乺") ⟫ʷ
lem-CSdu-box-3-at04122041 c4 = derive (ℓ "乺侗") (ℓ "侗乺")
  (rw 1 (q72 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw 1 (q190 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q186 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 5 (q187 c4) ∷
   rw 4 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = sE 249 (lem-box-tQ-at0214203143 c4)
  q194 : Ws → Eqn
  q194 c4 = wpE 536 c4
  q195 : Ws → Eqn
  q195 c4 = wlE 662 (lit c4)

-- Ku-box @0214203143: 6 steps
lem-Ku-box-at0214203143 : Ws → ⟪ (ℓ "丘佔") ⟫ʷ ≈ ⟪ (ℓ "佔丘") ⟫ʷ
lem-Ku-box-at0214203143 c4 = derive (ℓ "丘佔") (ℓ "佔丘")
  (rw 1 (q193 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = wpE 537 c4
  q197 : Ws → Eqn
  q197 c4 = wlE 663 (lit c4)

-- Kdu-box @0214203143: 6 steps
lem-Kdu-box-at0214203143 : Ws → ⟪ (ℓ "丙佔") ⟫ʷ ≈ ⟪ (ℓ "佔丙") ⟫ʷ
lem-Kdu-box-at0214203143 c4 = derive (ℓ "丙佔") (ℓ "佔丙")
  (rw 1 (q193 c4) ∷
   rw⁻ 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 3 (q197 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

-- box-perm-2314 @0214203143: 2 steps
lem-box-perm-2314-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "伮") ⟫ʷ
lem-box-perm-2314-at0214203143 c4 = derive (ℓ "佔") (ℓ "伮")
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = sE 1072 (lem-sym-ab-at0214233041 c4)

-- box-perm-4312 @0210213443: 2 steps
lem-box-perm-4312-at0210213443 : Ws → ⟪ (ℓ "伮") ⟫ʷ ≈ ⟪ (ℓ "佋") ⟫ʷ
lem-box-perm-4312-at0210213443 c4 = derive (ℓ "伮") (ℓ "佋")
  (rw 0 (q54 c4) ∷
   rw 0 (q198 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = sE 730 (lem-sym-ab-at0213243041 c4)
  q200 : Ws → Eqn
  q200 c4 = sE 1134 (lem-pairs-at0214233041 c4)

-- box-perm-3421 @0213243041: 2 steps
lem-box-perm-3421-at0213243041 : Ws → ⟪ (ℓ "佋") ⟫ʷ ≈ ⟪ (ℓ "伮") ⟫ʷ
lem-box-perm-3421-at0213243041 c4 = derive (ℓ "佋") (ℓ "伮")
  (rw 0 (q199 c4) ∷
   rw 0 (q200 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = sE 1031 (lem-sym-ab-at0314203142 c4)
  q202 : Ws → Eqn
  q202 c4 = sE 1144 (lem-sym-bc-at0310243142 c4)

-- box-perm-2314 @0314203142: 2 steps
lem-box-perm-2314-at0314203142 : Ws → ⟪ (ℓ "佹") ⟫ʷ ≈ ⟪ (ℓ "佥") ⟫ʷ
lem-box-perm-2314-at0314203142 c4 = derive (ℓ "佹") (ℓ "佥")
  (rw 0 (q201 c4) ∷
   rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = wlE 1646 (lit c4)
  q204 : Ws → Eqn
  q204 c4 = wlE 1647 (lit c4)
  q205 : Ws → Eqn
  q205 c4 = wlE 1648 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = wlE 1649 (lit c4)
  q207 : Ws → Eqn
  q207 c4 = sE 75 (lem-comm-CS24-TOFF301 c4)
  q208 : Ws → Eqn
  q208 c4 = wlE 1650 (lit c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 443 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 1651 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = sE 149 (lem-box-tQ-at0310213442 c4)
  q212 : Ws → Eqn
  q212 c4 = sE 1189 (lem-CSdu-box-3-at0310213442 c4)

-- F0-R @0410213243: 11 steps
lem-F0-R-at0410213243 : Ws → ⟪ (ℓ "书亓乹亓乺") ⟫ʷ ≈ ⟪ (ℓ "亓乹亓乺佥书") ⟫ʷ
lem-F0-R-at0410213243 c4 = derive (ℓ "书亓乹亓乺") (ℓ "亓乹亓乺佥书")
  (rw 0 (q203 c4) ∷
   rw⁻ 1 (q204 c4) ∷
   rw 4 (q203 c4) ∷
   rw⁻ 5 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw 3 (q207 c4) ∷
   rw 4 (q208 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 6 (q210 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 3 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = wpE 717 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 320 c4
  q215 : Ws → Eqn
  q215 c4 = wlE 191 (lit c4)
  q216 : Ws → Eqn
  q216 c4 = wlE 196 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = wlE 809 (lit c4)
  q218 : Ws → Eqn
  q218 c4 = wpE 109 c4
  q219 : Ws → Eqn
  q219 c4 = wpE 718 c4

-- CXu-box-4 @0214203143: 15 steps
lem-CXu-box-4-at0214203143 : Ws → ⟪ (ℓ "乶佔") ⟫ʷ ≈ ⟪ (ℓ "佔乶") ⟫ʷ
lem-CXu-box-4-at0214203143 c4 = derive (ℓ "乶佔") (ℓ "佔乶")
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 6 (q30 c4) ∷
   rw 5 (q25 c4) ∷
   rw 4 (q215 c4) ∷
   rw 3 (q25 c4) ∷
   rw 2 (q216 c4) ∷
   rw⁻ 3 (q214 c4) ∷
   rw 1 (q217 c4) ∷
   rw⁻ 3 (q218 c4) ∷
   rw⁻ 2 (q213 c4) ∷
   rw 3 (q219 c4) ∷
   rw 3 (q217 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q221 : Ws → Eqn
  q221 c4 = wpE 734 c4
  q222 : Ws → Eqn
  q222 c4 = wlE 885 (lit c4)
  q223 : Ws → Eqn
  q223 c4 = wlE 297 (lit c4)
  q224 : Ws → Eqn
  q224 c4 = wpE 314 c4
  q225 : Ws → Eqn
  q225 c4 = wpE 127 c4
  q226 : Ws → Eqn
  q226 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q227 : Ws → Eqn
  q227 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q228 : Ws → Eqn
  q228 c4 = wlE 882 (lit c4)
  q229 : Ws → Eqn
  q229 c4 = wlE 886 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = wlE 887 (lit c4)

-- CSdu-box-3 @0314203142: 17 steps
lem-CSdu-box-3-at0314203142 : Ws → ⟪ (ℓ "乏佹") ⟫ʷ ≈ ⟪ (ℓ "佹乏") ⟫ʷ
lem-CSdu-box-3-at0314203142 c4 = derive (ℓ "乏佹") (ℓ "佹乏")
  (rw 1 (q220 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw 4 (q223 c4) ∷
   rw⁻ 8 (q224 c4) ∷
   rw⁻ 7 (q225 c4) ∷
   rw 6 (q226 c4) ∷
   rw⁻ 5 (q225 c4) ∷
   rw 4 (q227 c4) ∷
   rw⁻ 5 (q223 c4) ∷
   rw 3 (q226 c4) ∷
   rw⁻ 2 (q221 c4) ∷
   rw 5 (q228 c4) ∷
   rw 4 (q229 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q230 c4) ∷
   rw⁻ 0 (q220 c4) ∷ []) Eq.refl
