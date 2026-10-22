{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD024 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D024 (Sᴰ : SD024) where

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
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CSd04-TOFF213 : Ws → St 198
  lem-comm-CSd04-TOFF213 = pickᴰ 2 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 3 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 4 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 5 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 6 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 7 Sᴰ
  lem-comm-CS04-TOFF213 : Ws → St 284
  lem-comm-CS04-TOFF213 = pickᴰ 8 Sᴰ
  lem-comm-CX40-TOFF312 : Ws → St 965
  lem-comm-CX40-TOFF312 = pickᴰ 9 Sᴰ
  lem-comm-CX40-TOFF213 : Ws → St 1173
  lem-comm-CX40-TOFF213 = pickᴰ 10 Sᴰ
  lem-comm-TOFF213-CX40 : Ws → St 1174
  lem-comm-TOFF213-CX40 = pickᴰ 11 Sᴰ
  lem-sym-ab-at04122140 : Ws → St 1201
  lem-sym-ab-at04122140 = pickᴰ 12 Sᴰ
  lem-sym-ab-at0412233140 : Ws → St 1202
  lem-sym-ab-at0412233140 = pickᴰ 13 Sᴰ
  lem-box-tQ-at04203243 : Ws → St 84
  lem-box-tQ-at04203243 = pickᴰ 14 Sᴰ
  lem-box-tQ-at043043 : Ws → St 253
  lem-box-tQ-at043043 = pickᴰ 15 Sᴰ
  lem-box-tQ-at02132031 : Ws → St 396
  lem-box-tQ-at02132031 = pickᴰ 16 Sᴰ
  lem-box-tQ-at022440 : Ws → St 331
  lem-box-tQ-at022440 = pickᴰ 17 Sᴰ
  lem-box-tQ-at03243240 : Ws → St 358
  lem-box-tQ-at03243240 = pickᴰ 18 Sᴰ
  lem-box-tQ-at04122041 : Ws → St 403
  lem-box-tQ-at04122041 = pickᴰ 19 Sᴰ
  lem-box-tQ-at0410233142 : Ws → St 436
  lem-box-tQ-at0410233142 = pickᴰ 20 Sᴰ
  lem-box-tQ-at04122140 : Ws → St 437
  lem-box-tQ-at04122140 = pickᴰ 21 Sᴰ
  lem-box-tQ-at0440 : Ws → St 425
  lem-box-tQ-at0440 = pickᴰ 22 Sᴰ
  lem-P-box-at02132031 : Ws → St 1203
  lem-P-box-at02132031 = pickᴰ 23 Sᴰ
  lem-P-box-at022440 : Ws → St 1204
  lem-P-box-at022440 = pickᴰ 24 Sᴰ
  lem-P-box-at03122031 : Ws → St 1205
  lem-P-box-at03122031 = pickᴰ 25 Sᴰ
  lem-P-box-at0410233142 : Ws → St 1206
  lem-P-box-at0410233142 = pickᴰ 26 Sᴰ
  lem-P-box-at0412233140 : Ws → St 1207
  lem-P-box-at0412233140 = pickᴰ 27 Sᴰ
  lem-P-box-at0413203241 : Ws → St 1208
  lem-P-box-at0413203241 = pickᴰ 28 Sᴰ
  lem-P-box-at043043 : Ws → St 1209
  lem-P-box-at043043 = pickᴰ 29 Sᴰ
  lem-t-cP-at04122041 : Ws → St 1210
  lem-t-cP-at04122041 = pickᴰ 30 Sᴰ
  lem-t-cP-at0440 : Ws → St 1211
  lem-t-cP-at0440 = pickᴰ 31 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 32 Sᴰ
  lem-box-cP-at02132031 : Ws → St 1212
  lem-box-cP-at02132031 = pickᴰ 33 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 34 Sᴰ
  lem-box-cP-at022440 : Ws → St 1114
  lem-box-cP-at022440 = pickᴰ 35 Sᴰ
  lem-box-cP-at03122031 : Ws → St 1213
  lem-box-cP-at03122031 = pickᴰ 36 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 37 Sᴰ
  lem-box-cP-at043043 : Ws → St 999
  lem-box-cP-at043043 = pickᴰ 38 Sᴰ
  lem-sym-bc-at0214203143 : Ws → St 1051
  lem-sym-bc-at0214203143 = pickᴰ 39 Sᴰ
  lem-box-cP-at0410233142 : Ws → St 1214
  lem-box-cP-at0410233142 = pickᴰ 40 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1192
  lem-box-cP-at04122041 = pickᴰ 41 Sᴰ
  lem-box-cP-at0412233140 : Ws → St 1215
  lem-box-cP-at0412233140 = pickᴰ 42 Sᴰ
  lem-box-cP-at0413203241 : Ws → St 1216
  lem-box-cP-at0413203241 = pickᴰ 43 Sᴰ
  lem-box-cP-at0440 : Ws → St 1196
  lem-box-cP-at0440 = pickᴰ 44 Sᴰ
  lem-box2-at04203243 : Ws → St 1217
  lem-box2-at04203243 = pickᴰ 45 Sᴰ
  lem-pairs-at04203243 : Ws → St 1218
  lem-pairs-at04203243 = pickᴰ 46 Sᴰ
  lem-sym-bc-at0412233140 : Ws → St 1219
  lem-sym-bc-at0412233140 = pickᴰ 47 Sᴰ
  lem-sym-bc-at04133140 : Ws → St 1220
  lem-sym-bc-at04133140 = pickᴰ 48 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 312 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 881 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 297 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 314 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 127 c4
  q7 : Ws → Eqn
  q7 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 882 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 883 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 884 (lit c4)

-- CSu-box-3 @0314203142: 17 steps
lem-CSu-box-3-at0314203142 : Ws → ⟪ (CS13 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314203142 c4 = derive (CS13 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CS13 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = sE 1218 (lem-pairs-at04203243 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1219 (lem-sym-bc-at0412233140 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1201 (lem-sym-ab-at04122140 c4)

-- box-perm-1342 @04203243: 3 steps
lem-box-perm-1342-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1342-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-1230 ∷ [])
  (rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 1206 (lem-P-box-at0410233142 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1214 (lem-box-cP-at0410233142 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 470 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 253 (lem-box-tQ-at043043 c4)

-- pairs @0410233142: 4 steps
lem-pairs-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-pairs-at0410233142 c4 = derive (Bx4-0312 ∷ []) (Bx4-1203 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 1209 (lem-P-box-at043043 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 999 (lem-box-cP-at043043 c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 317 c4
  q22 : Ws → Eqn
  q22 c4 = sE 436 (lem-box-tQ-at0410233142 c4)

-- pairs @043043: 4 steps
lem-pairs-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-pairs-at043043 c4 = derive (Bx4-1203 ∷ []) (Bx4-0312 ∷ [])
  (rw⁻ 0 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = sE 1207 (lem-P-box-at0412233140 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1215 (lem-box-cP-at0412233140 c4)
  q25 : Ws → Eqn
  q25 c4 = wpE 306 c4
  q26 : Ws → Eqn
  q26 c4 = sE 84 (lem-box-tQ-at04203243 c4)

-- pairs @0412233140: 4 steps
lem-pairs-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-pairs-at0412233140 c4 = derive (Bx4-2310 ∷ []) (Bx4-1023 ∷ [])
  (rw⁻ 0 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 1278 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 1430 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 1279 c4
  q31 : Ws → Eqn
  q31 c4 = wlE 1431 (lit c4)

-- F4-I-CS0 @0440: 15 steps
lem-F4-I-CS0-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS0-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷
   rw 1 (q31 c4) ∷
   rw⁻ 1 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = sE 1051 (lem-sym-bc-at0214203143 c4)

-- box-perm-1324 @0214203143: 1 steps
lem-box-perm-1324-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-1324-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  (rw 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 60 c4
  q35 : Ws → Eqn
  q35 c4 = wlE 1517 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 1501 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 61 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 155 c4
  q39 : Ws → Eqn
  q39 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 156 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 157 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 65 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 1354 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 1335 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 929 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 461 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CX10 ∷ Toff423 ∷ []) (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ))
  q48 : Ws → Eqn
  q48 c4 = wpE 1355 c4
  q49 : Ws → Eqn
  q49 c4 = wpE 311 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 1318 c4
  q51 : Ws → Eqn
  q51 c4 = wpE 1356 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 53 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 1509 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1217 (lem-box2-at04203243 c4)
  q55 : Ws → Eqn
  q55 c4 = wlE 1519 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 341 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 1703 (lit c4)

-- S2-SBOX(0;1;42;3) @0440: 86 steps
lem-S2-SBOX⟨0·1·42·3⟩-at0440 : Ws → ⟪ (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4 = derive (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) (CCZ012 ∷ [])
  (re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   re 0 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 4 (q36 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw 10 (q39 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw 8 (q43 c4) ∷
   rw 7 (q45 c4) ∷
   rw 11 (q46 c4) ∷
   rw 10 (q47 c4) ∷
   rw 9 (q48 c4) ∷
   rw 8 (q47 c4) ∷
   rw 7 (q49 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 6 (q50 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q39 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q36 c4) ∷
   rw 2 (q43 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 6 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   rw 9 (q46 c4) ∷
   rw 8 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw 6 (q47 c4) ∷
   rw 5 (q49 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = sE 403 (lem-box-tQ-at04122041 c4)
  q59 : Ws → Eqn
  q59 c4 = sE 1192 (lem-box-cP-at04122041 c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 1323 c4
  q61 : Ws → Eqn
  q61 c4 = sE 1210 (lem-t-cP-at04122041 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 321 (lit c4)

-- box2 @04122041: 11 steps
lem-box2-at04122041 : Ws → ⟪ (Bx4-2031 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04122041 c4 = derive (Bx4-2031 ∷ Bx4-2031 ∷ []) []
  (rw 0 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 5 (q58 c4) ∷
   rw 4 (q60 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q60 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 425 (lem-box-tQ-at0440 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 1196 (lem-box-cP-at0440 c4)
  q65 : Ws → Eqn
  q65 c4 = sE 1211 (lem-t-cP-at0440 c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 7 c4

-- box2 @0440: 11 steps
lem-box2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0440 c4 = derive (Bx4-1230 ∷ Bx4-1230 ∷ []) []
  (rw 0 (q63 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q65 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 5 (q63 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q66 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q17 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = sE 1208 (lem-P-box-at0413203241 c4)
  q68 : Ws → Eqn
  q68 c4 = sE 1216 (lem-box-cP-at0413203241 c4)
  q69 : Ws → Eqn
  q69 c4 = sE 437 (lem-box-tQ-at04122140 c4)

-- pairs @0413203241: 4 steps
lem-pairs-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-pairs-at0413203241 c4 = derive (Bx4-3021 ∷ []) (Bx4-2130 ∷ [])
  (rw⁻ 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = sE 1204 (lem-P-box-at022440 c4)
  q71 : Ws → Eqn
  q71 c4 = sE 1114 (lem-box-cP-at022440 c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 635 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = sE 396 (lem-box-tQ-at02132031 c4)

-- pairs @022440: 4 steps
lem-pairs-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-pairs-at022440 c4 = derive (Bx2-1430 ∷ []) (Bx2-3014 ∷ [])
  (rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw⁻ 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = sE 1203 (lem-P-box-at02132031 c4)
  q75 : Ws → Eqn
  q75 c4 = sE 1212 (lem-box-cP-at02132031 c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 636 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = sE 331 (lem-box-tQ-at022440 c4)

-- pairs @02132031: 4 steps
lem-pairs-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-pairs-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-1430 ∷ [])
  (rw⁻ 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = sE 1202 (lem-sym-ab-at0412233140 c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1220 (lem-sym-bc-at04133140 c4)

-- box-perm-4132 @04203243: 3 steps
lem-box-perm-4132-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-box-perm-4132-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-3120 ∷ [])
  (rw 0 (q12 c4) ∷
   rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 1205 (lem-P-box-at03122031 c4)
  q81 : Ws → Eqn
  q81 c4 = sE 1213 (lem-box-cP-at03122031 c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 788 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = sE 358 (lem-box-tQ-at03243240 c4)

-- pairs @03122031: 4 steps
lem-pairs-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-pairs-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-1420 ∷ [])
  (rw⁻ 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wpE 104 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 496 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 879 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 965 (lem-comm-CX40-TOFF312 c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 1226 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 861 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wlE 880 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wpE 109 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 110 c4

-- CXu-box-4 @0314203142: 15 steps
lem-CXu-box-4-at0314203142 : Ws → ⟪ (CX23 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0314203142 c4 = derive (CX23 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CX23 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 6 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 2 (q89 c4) ∷
   rw⁻ 3 (q85 c4) ∷
   rw 1 (q90 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q92 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = wlE 1446 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 1301 c4
  q95 : Ws → Eqn
  q95 c4 = wlE 1447 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wpE 1302 c4
  q97 : Ws → Eqn
  q97 c4 = wlE 1448 (lit c4)

-- F4-CS0-I @0440: 15 steps
lem-F4-CS0-I-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-I-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw 2 (q93 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 2 (q94 c4) ∷
   rw 1 (q27 c4) ∷
   rw 4 (q95 c4) ∷
   rw 3 (q96 c4) ∷
   rw 2 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 5 1 (Sb2-4-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 3 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = wpE 1280 c4
  q99 : Ws → Eqn
  q99 c4 = eqn (X0 ∷ Toff213 ∷ []) (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q100 : Ws → Eqn
  q100 c4 = sE 284 (lem-comm-CS04-TOFF213 c4)
  q101 : Ws → Eqn
  q101 c4 = wpE 1281 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 1282 c4
  q103 : Ws → Eqn
  q103 c4 = sE 198 (lem-comm-CSd04-TOFF213 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q105 : Ws → Eqn
  q105 c4 = wpE 1283 c4

-- F4-S0-CS0 @0440: 18 steps
lem-F4-S0-CS0-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS0-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 0 (q98 c4) ∷
   rw 3 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw 1 (q105 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷
   rw 1 (q101 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = wpE 1284 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1432 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 617 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wpE 36 c4
  q110 : Ws → Eqn
  q110 c4 = wpE 285 c4
  q111 : Ws → Eqn
  q111 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q112 : Ws → Eqn
  q112 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q113 : Ws → Eqn
  q113 c4 = wpE 1285 c4
  q114 : Ws → Eqn
  q114 c4 = wlE 1433 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 954 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wpE 35 c4
  q117 : Ws → Eqn
  q117 c4 = wlE 807 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wlE 1625 (lit c4)
  q119 : Ws → Eqn
  q119 c4 = wpE 33 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 39 c4
  q121 : Ws → Eqn
  q121 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q122 : Ws → Eqn
  q122 c4 = wpE 32 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 21 c4
  q124 : Ws → Eqn
  q124 c4 = wpE 37 c4
  q125 : Ws → Eqn
  q125 c4 = wlE 1421 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = wpE 760 c4
  q127 : Ws → Eqn
  q127 c4 = wpE 1143 c4
  q128 : Ws → Eqn
  q128 c4 = wlE 195 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = sE 1173 (lem-comm-CX40-TOFF213 c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 1422 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wlE 193 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = wlE 921 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = wpE 1275 c4
  q134 : Ws → Eqn
  q134 c4 = wlE 808 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 1286 c4
  q136 : Ws → Eqn
  q136 c4 = wpE 1276 c4
  q137 : Ws → Eqn
  q137 c4 = wpE 161 c4
  q138 : Ws → Eqn
  q138 c4 = wlE 1434 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wpE 1287 c4
  q140 : Ws → Eqn
  q140 c4 = wlE 746 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 1435 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wpE 653 c4
  q143 : Ws → Eqn
  q143 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q144 : Ws → Eqn
  q144 c4 = wpE 1288 c4
  q145 : Ws → Eqn
  q145 c4 = wlE 748 (lit c4)
  q146 : Ws → Eqn
  q146 c4 = sE 1174 (lem-comm-TOFF213-CX40 c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 655 c4
  q148 : Ws → Eqn
  q148 c4 = wpE 1289 c4
  q149 : Ws → Eqn
  q149 c4 = wlE 1436 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 1437 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = wpE 1290 c4
  q152 : Ws → Eqn
  q152 c4 = wlE 1438 (lit c4)
  q153 : Ws → Eqn
  q153 c4 = wpE 1291 c4

-- F4-CS0-CS0 @0440: 286 steps
lem-F4-CS0-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS0-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 2 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q99 c4) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 10 (q109 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 6 (q112 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw 5 (q114 c4) ∷
   rw 6 (q115 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 6 (q117 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 8 (q117 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 8 (q121 c4) ∷
   rw⁻ 7 (q122 c4) ∷
   rw 6 (q121 c4) ∷
   rw⁻ 5 (q123 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q118 c4) ∷
   rw⁻ 5 (q125 c4) ∷
   rw⁻ 7 (q118 c4) ∷
   rw⁻ 13 (q119 c4) ∷
   rw⁻ 12 (q120 c4) ∷
   rw 11 (q121 c4) ∷
   rw⁻ 10 (q122 c4) ∷
   rw 9 (q121 c4) ∷
   rw⁻ 8 (q123 c4) ∷
   rw⁻ 7 (q124 c4) ∷
   rw 8 (q118 c4) ∷
   rw⁻ 6 (q126 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   rw 8 (q127 c4) ∷
   rw 12 (q128 c4) ∷
   rw 11 (q129 c4) ∷
   rw 10 (q130 c4) ∷
   rw 9 (q129 c4) ∷
   rw 8 (q131 c4) ∷
   rw⁻ 9 (q127 c4) ∷
   rw 7 (q132 c4) ∷
   rw⁻ 8 (q133 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   re 3 1 (CS34 ∷ []) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw 6 (q134 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   rw 6 (q121 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   rw 4 (q121 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw⁻ 2 (q124 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 3 (q125 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   rw⁻ 11 (q119 c4) ∷
   rw⁻ 10 (q120 c4) ∷
   rw 9 (q121 c4) ∷
   rw⁻ 8 (q122 c4) ∷
   rw 7 (q121 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 5 (q124 c4) ∷
   rw 6 (q118 c4) ∷
   rw⁻ 4 (q126 c4) ∷
   rw⁻ 7 (q125 c4) ∷
   rw 6 (q127 c4) ∷
   rw 10 (q128 c4) ∷
   rw 9 (q129 c4) ∷
   rw 8 (q130 c4) ∷
   rw 7 (q129 c4) ∷
   rw 6 (q131 c4) ∷
   rw⁻ 7 (q127 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 0 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 1 (q99 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q109 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 4 (q112 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 2 (q106 c4) ∷
   rw 3 (q114 c4) ∷
   rw 4 (q115 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 6 (q109 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 3 (q110 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q109 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 4 (q112 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 5 (q115 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw 10 (q62 c4) ∷
   rw 3 (q136 c4) ∷
   rw 5 (q137 c4) ∷
   re 4 1 (Sb2-4-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 2 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q138 c4) ∷
   re 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 4 1 (CS34 ∷ []) ∷
   re 6 1 (CS34⁻ ∷ []) ∷
   rw⁻ 3 (q139 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 7 (q141 c4) ∷
   rw 4 (q142 c4) ∷
   rw 6 (q143 c4) ∷
   rw 7 (q144 c4) ∷
   rw⁻ 10 (q118 c4) ∷
   rw 9 (q124 c4) ∷
   rw 10 (q123 c4) ∷
   rw 11 (q143 c4) ∷
   rw 12 (q122 c4) ∷
   rw 13 (q143 c4) ∷
   rw 14 (q120 c4) ∷
   rw 15 (q119 c4) ∷
   rw 9 (q118 c4) ∷
   rw⁻ 3 (q145 c4) ∷
   rw 5 (q127 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 5 (q146 c4) ∷
   rw⁻ 6 (q130 c4) ∷
   rw 7 (q146 c4) ∷
   rw⁻ 8 (q128 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 7 (q132 c4) ∷
   rw 9 (q127 c4) ∷
   rw⁻ 8 (q131 c4) ∷
   rw 9 (q146 c4) ∷
   rw⁻ 10 (q130 c4) ∷
   rw 11 (q146 c4) ∷
   rw⁻ 12 (q128 c4) ∷
   rw⁻ 8 (q127 c4) ∷
   rw⁻ 9 (q141 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw⁻ 5 (q133 c4) ∷
   rw 3 (q148 c4) ∷
   rw 2 (q143 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q123 c4) ∷
   rw 5 (q143 c4) ∷
   rw 6 (q122 c4) ∷
   rw 7 (q143 c4) ∷
   rw 8 (q120 c4) ∷
   rw 9 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 1 (q149 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 6 (q134 c4) ∷
   rw 5 (q109 c4) ∷
   rw⁻ 4 (q134 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 2 (q150 c4) ∷
   rw⁻ 5 (q138 c4) ∷
   re 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 6 1 (CS34 ∷ []) ∷
   re 8 1 (CS34⁻ ∷ []) ∷
   rw⁻ 5 (q139 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw⁻ 9 (q141 c4) ∷
   rw 6 (q142 c4) ∷
   rw 8 (q143 c4) ∷
   rw 9 (q144 c4) ∷
   rw⁻ 12 (q118 c4) ∷
   rw 11 (q124 c4) ∷
   rw 12 (q123 c4) ∷
   rw 13 (q143 c4) ∷
   rw 14 (q122 c4) ∷
   rw 15 (q143 c4) ∷
   rw 16 (q120 c4) ∷
   rw 17 (q119 c4) ∷
   rw 11 (q118 c4) ∷
   rw⁻ 5 (q145 c4) ∷
   rw 7 (q127 c4) ∷
   rw⁻ 6 (q131 c4) ∷
   rw 7 (q146 c4) ∷
   rw⁻ 8 (q130 c4) ∷
   rw 9 (q146 c4) ∷
   rw⁻ 10 (q128 c4) ∷
   rw⁻ 6 (q127 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw⁻ 9 (q132 c4) ∷
   rw 11 (q127 c4) ∷
   rw⁻ 10 (q131 c4) ∷
   rw 11 (q146 c4) ∷
   rw⁻ 12 (q130 c4) ∷
   rw 13 (q146 c4) ∷
   rw⁻ 14 (q128 c4) ∷
   rw⁻ 10 (q127 c4) ∷
   rw⁻ 11 (q141 c4) ∷
   rw⁻ 5 (q147 c4) ∷
   rw⁻ 7 (q133 c4) ∷
   rw 5 (q148 c4) ∷
   rw 4 (q143 c4) ∷
   rw⁻ 6 (q118 c4) ∷
   rw 5 (q124 c4) ∷
   rw 6 (q123 c4) ∷
   rw 7 (q143 c4) ∷
   rw 8 (q122 c4) ∷
   rw 9 (q143 c4) ∷
   rw 10 (q120 c4) ∷
   rw 11 (q119 c4) ∷
   rw 5 (q118 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q149 c4) ∷
   rw⁻ 6 (q152 c4) ∷
   re 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 7 1 (CS34 ∷ []) ∷
   re 9 1 (CS34⁻ ∷ []) ∷
   rw⁻ 6 (q153 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw 7 (q116 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw 5 (q116 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 4 (q152 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl
