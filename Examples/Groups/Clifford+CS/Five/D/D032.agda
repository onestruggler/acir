{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD032 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D032 (Sᴰ : SD032) where

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
  lem-comm-CX04-TOFF213 : Ws → St 1023
  lem-comm-CX04-TOFF213 = pickᴰ 0 Sᴰ
  lem-comm-CX14-TOFF023 : Ws → St 1056
  lem-comm-CX14-TOFF023 = pickᴰ 1 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 2 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 3 Sᴰ
  lem-comm-CX40-TOFF213 : Ws → St 1173
  lem-comm-CX40-TOFF213 = pickᴰ 4 Sᴰ
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 5 Sᴰ
  lem-F4-I-K0 : Ws → St 1387
  lem-F4-I-K0 = pickᴰ 6 Sᴰ
  lem-F4-I-S0 : Ws → St 1388
  lem-F4-I-S0 = pickᴰ 7 Sᴰ
  lem-F4-K0-I : Ws → St 1389
  lem-F4-K0-I = pickᴰ 8 Sᴰ
  lem-F4-K0-K0 : Ws → St 1390
  lem-F4-K0-K0 = pickᴰ 9 Sᴰ
  lem-F4-K0-S0 : Ws → St 1391
  lem-F4-K0-S0 = pickᴰ 10 Sᴰ
  lem-F4-S0-I : Ws → St 1392
  lem-F4-S0-I = pickᴰ 11 Sᴰ
  lem-F4-S0-K0 : Ws → St 1393
  lem-F4-S0-K0 = pickᴰ 12 Sᴰ
  lem-F4-S0-S0 : Ws → St 1394
  lem-F4-S0-S0 = pickᴰ 13 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 40
  lem-sym-ab-at03102132 = pickᴰ 14 Sᴰ
  lem-sym-ab-at032032 : Ws → St 54
  lem-sym-ab-at032032 = pickᴰ 15 Sᴰ
  lem-sym-ab-at14233142 : Ws → St 1070
  lem-sym-ab-at14233142 = pickᴰ 16 Sᴰ
  lem-sym-ab-at03122130 : Ws → St 1074
  lem-sym-ab-at03122130 = pickᴰ 17 Sᴰ
  lem-sym-ab-at0330 : Ws → St 897
  lem-sym-ab-at0330 = pickᴰ 18 Sᴰ
  lem-sym-ab-at14213243 : Ws → St 1079
  lem-sym-ab-at14213243 = pickᴰ 19 Sᴰ
  lem-sym-ab-at0310213442 : Ws → St 1395
  lem-sym-ab-at0310213442 = pickᴰ 20 Sᴰ
  lem-sym-ab-at0314213042 : Ws → St 1396
  lem-sym-ab-at0314213042 = pickᴰ 21 Sᴰ
  lem-sym-ab-at03203442 : Ws → St 1397
  lem-sym-ab-at03203442 = pickᴰ 22 Sᴰ
  lem-sym-ab-at03243042 : Ws → St 1398
  lem-sym-ab-at03243042 = pickᴰ 23 Sᴰ
  lem-sym-ab-at142142 : Ws → St 1399
  lem-sym-ab-at142142 = pickᴰ 24 Sᴰ
  lem-sym-ab-at2442 : Ws → St 1400
  lem-sym-ab-at2442 = pickᴰ 25 Sᴰ
  lem-sym-bc-at03102132 : Ws → St 874
  lem-sym-bc-at03102132 = pickᴰ 26 Sᴰ
  lem-sym-bc-at0310213442 : Ws → St 875
  lem-sym-bc-at0310213442 = pickᴰ 27 Sᴰ
  lem-box-cP-at0214233041 : Ws → St 890
  lem-box-cP-at0214233041 = pickᴰ 28 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 29 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 30 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 31 Sᴰ
  lem-sym-bc-at0310243142 : Ws → St 1144
  lem-sym-bc-at0310243142 = pickᴰ 32 Sᴰ
  lem-sym-bc-at031031 : Ws → St 1146
  lem-sym-bc-at031031 = pickᴰ 33 Sᴰ
  lem-sym-bc-at132132 : Ws → St 1236
  lem-sym-bc-at132132 = pickᴰ 34 Sᴰ
  lem-sym-bc-at1331 : Ws → St 1237
  lem-sym-bc-at1331 = pickᴰ 35 Sᴰ
  lem-sym-bc-at243243 : Ws → St 1022
  lem-sym-bc-at243243 = pickᴰ 36 Sᴰ
  lem-F4-I-CS0 : Ws → St 1401
  lem-F4-I-CS0 = pickᴰ 37 Sᴰ
  lem-F4-K0-CS0 : Ws → St 1402
  lem-F4-K0-CS0 = pickᴰ 38 Sᴰ
  lem-F4-S0-CS0 : Ws → St 1403
  lem-F4-S0-CS0 = pickᴰ 39 Sᴰ
  lem-Xb-box-at0210243143 : Ws → St 1251
  lem-Xb-box-at0210243143 = pickᴰ 40 Sᴰ
  lem-Xb-box-at243243 : Ws → St 1253
  lem-Xb-box-at243243 = pickᴰ 41 Sᴰ
  lem-box2-at0210243143 : Ws → St 1258
  lem-box2-at0210243143 = pickᴰ 42 Sᴰ
  lem-box2-at243243 : Ws → St 1260
  lem-box2-at243243 = pickᴰ 43 Sᴰ
  lem-pairs-at0310243142 : Ws → St 1263
  lem-pairs-at0310243142 = pickᴰ 44 Sᴰ
  lem-pairs-at0330 : Ws → St 1264
  lem-pairs-at0330 = pickᴰ 45 Sᴰ
  lem-pairs-at1331 : Ws → St 1269
  lem-pairs-at1331 = pickᴰ 46 Sᴰ
  lem-pairs-at3443 : Ws → St 1272
  lem-pairs-at3443 = pickᴰ 47 Sᴰ
  lem-pairs-at031031 : Ws → St 1404
  lem-pairs-at031031 = pickᴰ 48 Sᴰ
  lem-pairs-at03243042 : Ws → St 1405
  lem-pairs-at03243042 = pickᴰ 49 Sᴰ
  lem-pairs-at2442 : Ws → St 1406
  lem-pairs-at2442 = pickᴰ 50 Sᴰ
  lem-box2-at0214203143 : Ws → St 1407
  lem-box2-at0214203143 = pickᴰ 51 Sᴰ
  lem-box-perm-1423-at0214203143 : Ws → St 1408
  lem-box-perm-1423-at0214203143 = pickᴰ 52 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1074 (lem-sym-ab-at03122130 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1264 (lem-pairs-at0330 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1144 (lem-sym-bc-at0310243142 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1395 (lem-sym-ab-at0310213442 c4)

-- box-perm-2341 @03122130: 4 steps
lem-box-perm-2341-at03122130 : Ws → ⟪ (ℓ "佲") ⟫ʷ ≈ ⟪ (ℓ "佫") ⟫ʷ
lem-box-perm-2341-at03122130 c4 = derive (ℓ "佲") (ℓ "佫")
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = sE 1397 (lem-sym-ab-at03203442 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 875 (lem-sym-bc-at0310213442 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1263 (lem-pairs-at0310243142 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 897 (lem-sym-ab-at0330 c4)

-- box-perm-4123 @03203442: 4 steps
lem-box-perm-4123-at03203442 : Ws → ⟪ (ℓ "佫") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-box-perm-4123-at03203442 c4 = derive (ℓ "佫") (ℓ "佲")
  (rw 0 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 0 (q7 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = sE 54 (lem-sym-ab-at032032 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 874 (lem-sym-bc-at03102132 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1404 (lem-pairs-at031031 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1398 (lem-sym-ab-at03243042 c4)

-- box-perm-4123 @032032: 4 steps
lem-box-perm-4123-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "侂") ⟫ʷ
lem-box-perm-4123-at032032 c4 = derive (ℓ "佪") (ℓ "侂")
  (rw 0 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = sE 1079 (lem-sym-ab-at14213243 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1022 (lem-sym-bc-at243243 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1272 (lem-pairs-at3443 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1070 (lem-sym-ab-at14233142 c4)

-- box-perm-4123 @14213243: 4 steps
lem-box-perm-4123-at14213243 : Ws → ⟪ (ℓ "仼") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-box-perm-4123-at14213243 c4 = derive (ℓ "仼") (ℓ "仳")
  (rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 1396 (lem-sym-ab-at0314213042 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1405 (lem-pairs-at03243042 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1146 (lem-sym-bc-at031031 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 40 (lem-sym-ab-at03102132 c4)

-- box-perm-2341 @0314213042: 4 steps
lem-box-perm-2341-at0314213042 : Ws → ⟪ (ℓ "侂") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-box-perm-2341-at0314213042 c4 = derive (ℓ "侂") (ℓ "佪")
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = sE 1399 (lem-sym-ab-at142142 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1406 (lem-pairs-at2442 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1237 (lem-sym-bc-at1331 c4)

-- box-perm-3241 @142142: 3 steps
lem-box-perm-3241-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "令") ⟫ʷ
lem-box-perm-3241-at142142 c4 = derive (ℓ "企") (ℓ "令")
  (rw 0 (q21 c4) ∷
   rw 0 (q22 c4) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = sE 1236 (lem-sym-bc-at132132 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1269 (lem-pairs-at1331 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1400 (lem-sym-ab-at2442 c4)

-- box-perm-4213 @132132: 3 steps
lem-box-perm-4213-at132132 : Ws → ⟪ (ℓ "令") ⟫ʷ ≈ ⟪ (ℓ "企") ⟫ʷ
lem-box-perm-4213-at132132 c4 = derive (ℓ "令") (ℓ "企")
  (rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 32 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 191 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1182 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 33 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 36 c4
  q33 : Ws → Eqn
  q33 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 746 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 34 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 37 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 192 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 42 c4
  q39 : Ws → Eqn
  q39 c4 = wpE 41 c4
  q40 : Ws → Eqn
  q40 c4 = wlE 193 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1023 (lem-comm-CX04-TOFF213 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 194 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 195 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 197 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 44 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 21 c4
  q47 : Ws → Eqn
  q47 c4 = wlE 196 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = sE 1258 (lem-box2-at0210243143 c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 651 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 161 c4
  q51 : Ws → Eqn
  q51 c4 = wpE 905 c4

-- S2-SBOX(0;2;43;1) @02132031: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 : Ws → ⟪ (ℓ "俄俄") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4 = derive (ℓ "俄俄") (ℓ "五")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   re 0 1 (ℓ "伱亮係亮促") ∷
   re 2 1 (ℓ "丶") ∷
   re 4 1 (ℓ "丷") ∷
   rw 5 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q30 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw 7 (q39 c4) ∷
   rw 11 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q30 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q30 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (ℓ "促並") (ℓ "並促") (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X))
  q53 : Ws → Eqn
  q53 c4 = wlE 187 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (ℓ "係並") (ℓ "並係") (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X))
  q55 : Ws → Eqn
  q55 c4 = wlE 188 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 189 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 29 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 30 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 31 c4
  q60 : Ws → Eqn
  q60 c4 = sE 1251 (lem-Xb-box-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 38 c4
  q62 : Ws → Eqn
  q62 c4 = wlE 323 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 179 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 39 c4
  q65 : Ws → Eqn
  q65 c4 = wpE 1259 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 1260 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 1261 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 198 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1262 c4

-- F5-23 @02132031: 112 steps
lem-F5-23-at02132031 : Ws → ⟪ (ℓ "並俄並俄") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
lem-F5-23-at02132031 c4 = derive (ℓ "並俄並俄") (ℓ "丨")
  (re 3 1 (ℓ "伱亮係亮促") ∷
   re 1 1 (ℓ "伱亮係亮促") ∷
   rw 5 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (ℓ "丶") ∷
   rw 4 (q55 c4) ∷
   re 7 1 (ℓ "係") ∷
   rw 2 (q53 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 9 (q27 c4) ∷
   re 8 1 (ℓ "丷") ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw⁻ 10 (q34 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 8 (q30 c4) ∷
   re 6 1 (ℓ "丶") ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 6 (q30 c4) ∷
   rw 4 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 2 (q65 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 11 (q33 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 10 (q30 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 7 (q61 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q30 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 5 (q66 c4) ∷
   rw 11 (q29 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw 9 (q39 c4) ∷
   rw 13 (q40 c4) ∷
   rw 12 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 10 (q41 c4) ∷
   rw 9 (q43 c4) ∷
   rw⁻ 10 (q39 c4) ∷
   rw⁻ 8 (q44 c4) ∷
   rw 7 (q40 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q48 c4) ∷
   re 7 1 (ℓ "丶") ∷
   re 9 1 (ℓ "丷") ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 60 c4
  q72 : Ws → Eqn
  q72 c4 = wlE 219 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 1413 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 61 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 64 c4
  q76 : Ws → Eqn
  q76 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 722 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 62 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 65 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 68 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 71 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 220 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 221 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = sE 1056 (lem-comm-CX14-TOFF023 c4)
  q85 : Ws → Eqn
  q85 c4 = wpE 69 c4
  q86 : Ws → Eqn
  q86 c4 = wpE 70 c4
  q87 : Ws → Eqn
  q87 c4 = wpE 72 c4
  q88 : Ws → Eqn
  q88 c4 = wpE 74 c4
  q89 : Ws → Eqn
  q89 c4 = wpE 53 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 222 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = sE 1260 (lem-box2-at243243 c4)
  q92 : Ws → Eqn
  q92 c4 = wlE 1000 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 263 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 1113 (lit c4)

-- S2-SBOX(0;2;43;1) @132132: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at132132 : Ws → ⟪ (ℓ "侧侧") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at132132 c4 = derive (ℓ "侧侧") (ℓ "亨")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   re 0 1 (ℓ "仄亲侥亲侦") ∷
   re 2 1 (ℓ "乎") ∷
   re 4 1 (ℓ "乏") ∷
   rw 5 (q70 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q72 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 3 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 8 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw 5 (q76 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 12 (q74 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   rw 10 (q76 c4) ∷
   rw⁻ 9 (q77 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 6 (q79 c4) ∷
   rw 7 (q73 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw 7 (q82 c4) ∷
   rw 11 (q83 c4) ∷
   rw 10 (q84 c4) ∷
   rw 9 (q85 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 8 (q82 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   rw 5 (q76 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   rw 3 (q76 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   rw 9 (q83 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw 0 (q91 c4) ∷
   rw 0 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (ℓ "侦並") (ℓ "並侦") (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X))
  q96 : Ws → Eqn
  q96 c4 = wlE 211 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (ℓ "侥並") (ℓ "並侥") (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q98 : Ws → Eqn
  q98 c4 = wlE 212 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 213 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wlE 214 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = wlE 215 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 216 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = sE 1253 (lem-Xb-box-at243243 c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 66 c4
  q105 : Ws → Eqn
  q105 c4 = wlE 314 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wpE 265 c4
  q107 : Ws → Eqn
  q107 c4 = wpE 67 c4
  q108 : Ws → Eqn
  q108 c4 = wlE 1414 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 1415 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wpE 1265 c4
  q111 : Ws → Eqn
  q111 c4 = wpE 73 c4
  q112 : Ws → Eqn
  q112 c4 = wlE 1416 (lit c4)

-- F5-23 @132132: 112 steps
lem-F5-23-at132132 : Ws → ⟪ (ℓ "並侧並侧") ⟫ʷ ≈ ⟪ (ℓ "乇") ⟫ʷ
lem-F5-23-at132132 c4 = derive (ℓ "並侧並侧") (ℓ "乇")
  (re 3 1 (ℓ "仄亲侥亲侦") ∷
   re 1 1 (ℓ "仄亲侥亲侦") ∷
   rw 5 (q95 c4) ∷
   rw 4 (q96 c4) ∷
   rw 3 (q97 c4) ∷
   re 4 1 (ℓ "乎") ∷
   rw 4 (q98 c4) ∷
   re 7 1 (ℓ "侥") ∷
   rw 2 (q96 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw⁻ 5 (q100 c4) ∷
   rw⁻ 6 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 9 (q70 c4) ∷
   re 8 1 (ℓ "乏") ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw⁻ 13 (q74 c4) ∷
   rw⁻ 12 (q75 c4) ∷
   rw 11 (q76 c4) ∷
   rw⁻ 10 (q77 c4) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw 8 (q73 c4) ∷
   re 6 1 (ℓ "乎") ∷
   rw⁻ 6 (q89 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 11 (q74 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q76 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 7 (q89 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 1 (q105 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 2 (q76 c4) ∷
   rw⁻ 1 (q107 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 2 (q108 c4) ∷
   rw 7 (q72 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   rw 9 (q83 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 9 (q73 c4) ∷
   rw⁻ 15 (q74 c4) ∷
   rw⁻ 14 (q75 c4) ∷
   rw 13 (q76 c4) ∷
   rw⁻ 12 (q77 c4) ∷
   rw 11 (q76 c4) ∷
   rw⁻ 10 (q78 c4) ∷
   rw⁻ 9 (q79 c4) ∷
   rw 10 (q73 c4) ∷
   rw⁻ 8 (q81 c4) ∷
   rw⁻ 7 (q104 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 5 (q109 c4) ∷
   rw 11 (q72 c4) ∷
   rw⁻ 10 (q80 c4) ∷
   rw 9 (q82 c4) ∷
   rw 13 (q83 c4) ∷
   rw 12 (q84 c4) ∷
   rw 11 (q85 c4) ∷
   rw 10 (q84 c4) ∷
   rw 9 (q86 c4) ∷
   rw⁻ 10 (q82 c4) ∷
   rw⁻ 8 (q87 c4) ∷
   rw 7 (q83 c4) ∷
   rw 6 (q90 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw 0 (q91 c4) ∷
   re 7 1 (ℓ "乎") ∷
   re 9 1 (ℓ "乏") ∷
   rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = wlE 1420 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 1263 c4
  q115 : Ws → Eqn
  q115 c4 = wpE 1267 c4
  q116 : Ws → Eqn
  q116 c4 = sE 1393 (lem-F4-S0-K0 c4)
  q117 : Ws → Eqn
  q117 c4 = sE 1394 (lem-F4-S0-S0 c4)
  q118 : Ws → Eqn
  q118 c4 = sE 1391 (lem-F4-K0-S0 c4)
  q119 : Ws → Eqn
  q119 c4 = sE 1390 (lem-F4-K0-K0 c4)
  q120 : Ws → Eqn
  q120 c4 = wlE 1411 (lit c4)
  q121 : Ws → Eqn
  q121 c4 = sE 1387 (lem-F4-I-K0 c4)
  q122 : Ws → Eqn
  q122 c4 = sE 1388 (lem-F4-I-S0 c4)
  q123 : Ws → Eqn
  q123 c4 = sE 1386 (lem-F4-I-I c4)
  q124 : Ws → Eqn
  q124 c4 = sE 1389 (lem-F4-K0-I c4)
  q125 : Ws → Eqn
  q125 c4 = sE 1392 (lem-F4-S0-I c4)
  q126 : Ws → Eqn
  q126 c4 = sE 1401 (lem-F4-I-CS0 c4)
  q127 : Ws → Eqn
  q127 c4 = sE 1402 (lem-F4-K0-CS0 c4)
  q128 : Ws → Eqn
  q128 c4 = sE 1403 (lem-F4-S0-CS0 c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 1274 c4

-- ckt-Dinv: 73 steps
lem-ckt-Dinv : Ws → ⟪ (ℓ "与俄俄俄与") ⟫ʷ ≈ ⟪ (ℓ "亁丽丽亁丢俄俄俄亁丽丽亁丢") ⟫ʷ
lem-ckt-Dinv c4 = derive (ℓ "与俄俄俄与") (ℓ "亁丽丽亁丢俄俄俄亁丽丽亁丢")
  (rw⁻ 0 (q113 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 4 (q115 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw 8 (q115 c4) ∷
   rw⁻ 7 (q117 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw 12 (q114 c4) ∷
   rw⁻ 11 (q118 c4) ∷
   rw⁻ 10 (q118 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   rw⁻ 16 (q120 c4) ∷
   rw⁻ 15 (q121 c4) ∷
   rw⁻ 14 (q122 c4) ∷
   rw⁻ 13 (q122 c4) ∷
   rw⁻ 12 (q121 c4) ∷
   rw 23 (q114 c4) ∷
   rw 27 (q115 c4) ∷
   rw⁻ 26 (q116 c4) ∷
   rw 31 (q115 c4) ∷
   rw⁻ 30 (q117 c4) ∷
   rw⁻ 29 (q116 c4) ∷
   rw 35 (q114 c4) ∷
   rw⁻ 34 (q118 c4) ∷
   rw⁻ 33 (q118 c4) ∷
   rw⁻ 32 (q119 c4) ∷
   rw⁻ 39 (q120 c4) ∷
   rw⁻ 38 (q121 c4) ∷
   rw⁻ 37 (q122 c4) ∷
   rw⁻ 36 (q122 c4) ∷
   rw⁻ 35 (q121 c4) ∷
   rw 12 (q121 c4) ∷
   rw 9 (q119 c4) ∷
   rw 6 (q116 c4) ∷
   rw 3 (q116 c4) ∷
   rw 0 (q119 c4) ∷
   rw 13 (q122 c4) ∷
   rw 10 (q118 c4) ∷
   rw 7 (q117 c4) ∷
   rw 4 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 14 (q122 c4) ∷
   rw 11 (q118 c4) ∷
   rw 8 (q117 c4) ∷
   rw 5 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw 15 (q121 c4) ∷
   rw 12 (q119 c4) ∷
   rw 9 (q116 c4) ∷
   rw 6 (q116 c4) ∷
   rw 3 (q119 c4) ∷
   rw 16 (q123 c4) ∷
   rw 13 (q124 c4) ∷
   rw 10 (q125 c4) ∷
   rw 7 (q125 c4) ∷
   rw 4 (q124 c4) ∷
   rw 17 (q126 c4) ∷
   rw 14 (q127 c4) ∷
   rw 11 (q128 c4) ∷
   rw 8 (q128 c4) ∷
   rw 5 (q127 c4) ∷
   rw 18 (q126 c4) ∷
   rw 15 (q127 c4) ∷
   rw 12 (q128 c4) ∷
   rw 9 (q128 c4) ∷
   rw 6 (q127 c4) ∷
   rw 19 (q126 c4) ∷
   rw 16 (q127 c4) ∷
   rw 13 (q128 c4) ∷
   rw 10 (q128 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q129 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q131 : Ws → Eqn
  q131 c4 = wpE 35 c4
  q132 : Ws → Eqn
  q132 c4 = wlE 807 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = wlE 1380 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 1421 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 760 c4
  q136 : Ws → Eqn
  q136 c4 = wpE 1143 c4
  q137 : Ws → Eqn
  q137 c4 = sE 1173 (lem-comm-CX40-TOFF213 c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 1422 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 921 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wpE 1275 c4
  q141 : Ws → Eqn
  q141 c4 = wlE 808 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = sE 1407 (lem-box2-at0214203143 c4)
  q143 : Ws → Eqn
  q143 c4 = wpE 1276 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 1277 c4

-- S2-SBOX(0;2;43;1) @0213243140: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 : Ws → ⟪ (ℓ "俊俊") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 c4 = derive (ℓ "俊俊") (ℓ "五")
  (re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   re 0 1 (ℓ "佔亓俈亓俉") ∷
   re 2 1 (ℓ "乹") ∷
   re 4 1 (ℓ "乺") ∷
   rw 5 (q130 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 6 (q131 c4) ∷
   rw 7 (q132 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 4 (q134 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 11 (q46 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 5 (q135 c4) ∷
   rw⁻ 8 (q134 c4) ∷
   rw 7 (q136 c4) ∷
   rw 11 (q43 c4) ∷
   rw 10 (q137 c4) ∷
   rw 9 (q138 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 8 (q136 c4) ∷
   rw 6 (q139 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 3 (q130 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q141 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q141 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 2 (q130 c4) ∷
   rw⁻ 1 (q133 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q133 c4) ∷
   rw⁻ 2 (q134 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q133 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw⁻ 6 (q134 c4) ∷
   rw 5 (q136 c4) ∷
   rw 9 (q43 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q138 c4) ∷
   rw 6 (q137 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 6 (q136 c4) ∷
   rw 4 (q139 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 0 (q142 c4) ∷
   rw 0 (q143 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 0 (q144 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = sE 1408 (lem-box-perm-1423-at0214203143 c4)
  q146 : Ws → Eqn
  q146 c4 = sE 890 (lem-box-cP-at0214233041 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (ℓ "与亰") (ℓ "亰与") (c₁ (X) (CCZ ↑))
  q148 : Ws → Eqn
  q148 c4 = eqn (ℓ "中亰") (ℓ "亰中") (c₂ (CK₀₁) (CCZ))
  q149 : Ws → Eqn
  q149 c4 = wlE 1439 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wpE 1292 c4

-- F4-K3-CS2 @0213243140: 19 steps
lem-F4-K3-CS2-at0213243140 : Ws → ⟪ (ℓ "与中与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与中与") ⟫ʷ
lem-F4-K3-CS2-at0213243140 c4 = derive (ℓ "与中与俊") (ℓ "俊与中与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 3 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 0 (q147 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 4 (q147 c4) ∷
   rw 3 (q148 c4) ∷
   rw 2 (q147 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw⁻ 0 (q146 c4) ∷
   rw⁻ 0 (q145 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wlE 1441 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = wpE 1294 c4
  q153 : Ws → Eqn
  q153 c4 = wlE 1442 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (ℓ "丒亰") (ℓ "亰丒") (c₂ (K ↑) (CCZ))
  q155 : Ws → Eqn
  q155 c4 = eqn (ℓ "上亰") (ℓ "亰上") (c₁ (S) (CCZ ↑))
  q156 : Ws → Eqn
  q156 c4 = wlE 1443 (lit c4)

-- F4-CS2-K3 @0213243140: 21 steps
lem-F4-CS2-K3-at0213243140 : Ws → ⟪ (ℓ "与俊与中") ⟫ʷ ≈ ⟪ (ℓ "中与俊与") ⟫ʷ
lem-F4-CS2-K3-at0213243140 c4 = derive (ℓ "与俊与中") (ℓ "中与俊与")
  (rw⁻ 2 (q151 c4) ∷
   re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   rw⁻ 2 (q152 c4) ∷
   rw 1 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 4 (q153 c4) ∷
   rw⁻ 3 (q154 c4) ∷
   rw⁻ 4 (q148 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw⁻ 2 (q148 c4) ∷
   rw⁻ 3 (q155 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw⁻ 4 (q145 c4) ∷
   re 6 1 (ℓ "俈") ∷
   re 8 1 (ℓ "俉") ∷
   re 4 5 (ℓ "俊") ∷
   rw⁻ 0 (q156 c4) ∷ []) Eq.refl
