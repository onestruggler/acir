{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD775 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D775 (W : Ws) (Sᴰ : SD775) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 3346
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-MBi-a0 : St 3347
  lem-MBi-a0 = pickᴰ 1 Sᴰ
  lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2249
  lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 2 Sᴰ
  lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2251
  lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 3 Sᴰ
  lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2253
  lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 4 Sᴰ
  lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2255
  lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 5 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 : St 2485
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 = pickᴰ 6 Sᴰ
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2500
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 7 Sᴰ
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3348
  lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 8 Sᴰ
  lem-CI-MB-MA : St 3349
  lem-CI-MB-MA = pickᴰ 9 Sᴰ
  lem-merge-R0 : St 3093
  lem-merge-R0 = pickᴰ 10 Sᴰ
  lem-split-R : St 3350
  lem-split-R = pickᴰ 11 Sᴰ
  lem-a0-Ri-≡-Ri-a0ᵖ-1 : St 3351
  lem-a0-Ri-≡-Ri-a0ᵖ-1 = pickᴰ 12 Sᴰ
  lem-pass-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-MBi : St 3352
  lem-pass-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-MBi = pickᴰ 13 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 3353
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 14 Sᴰ
  lem-split-b : St 3354
  lem-split-b = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = sE 3354 lem-split-b
  q2 : Eqn
  q2 = sE 3350 lem-split-R
  q3 : Eqn
  q3 = sE 3349 lem-CI-MB-MA
  q4 : Eqn
  q4 = sE 3093 lem-merge-R0
  q5 : Eqn
  q5 = sE 3352 lem-pass-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-MBi
  q6 : Eqn
  q6 = sE 3348 lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q7 : Eqn
  q7 = wE 390 W
  q8 : Eqn
  q8 = wE 2487 W
  q9 : Eqn
  q9 = wE 1339 W
  q10 : Eqn
  q10 = wE 227 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 1358 W
  q14 : Eqn
  q14 = wE 1342 W
  q15 : Eqn
  q15 = wE 1846 W
  q16 : Eqn
  q16 = wE 1728 W
  q17 : Eqn
  q17 = sE 3347 lem-MBi-a0
  q18 : Eqn
  q18 = sE 2500 lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q19 : Eqn
  q19 = sE 3346 lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q20 : Eqn
  q20 = sE 3354 lem-split-b

-- F7a gad: 32 steps
lem-F7a-gad : ⟪ (ℓ "丽习举习丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三九中九丮丽习举习") ⟫ʷ
lem-F7a-gad = derive (ℓ "丽习举习丈上中九丮九下三") (ℓ "丈上中九丮九下三九中九丮丽习举习")
  (rw 0 q1 ∷
   rw 8 q2 ∷
   rw 6 q3 ∷
   rw⁻ 6 q4 ∷
   rw 14 q5 ∷
   rw 16 q6 ∷
   rw 29 q7 ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 27 q11 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q12 ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw 27 q12 ∷
   rw 26 q13 ∷
   rw 25 q12 ∷
   rw 24 q10 ∷
   rw 25 q11 ∷
   re 24 1 (ℓ "乏丨乏") ∷
   rw 26 q12 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q12 ∷
   rw 24 q14 ∷
   rw 23 q12 ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   rw 20 q7 ∷
   rw 14 q17 ∷
   rw 0 q18 ∷
   rw 8 q19 ∷
   rw⁻ 12 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 5 W
  q22 : Eqn
  q22 = wE 2549 W
  q23 : Eqn
  q23 = wE 1731 W
  q24 : Eqn
  q24 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = wE 9 W
  q26 : Eqn
  q26 = wE 127 W
  q27 : Eqn
  q27 = wE 271 W
  q28 : Eqn
  q28 = wE 7 W
  q29 : Eqn
  q29 = wE 8 W
  q30 : Eqn
  q30 = wE 10 W
  q31 : Eqn
  q31 = wE 272 W
  q32 : Eqn
  q32 = wE 1207 W
  q33 : Eqn
  q33 = sE 3351 lem-a0-Ri-≡-Ri-a0ᵖ-1
  q34 : Eqn
  q34 = wE 311 W
  q35 : Eqn
  q35 = wE 123 W
  q36 : Eqn
  q36 = wE 27 W
  q37 : Eqn
  q37 = wE 28 W
  q38 : Eqn
  q38 = wE 29 W
  q39 : Eqn
  q39 = wE 25 W
  q40 : Eqn
  q40 = wE 124 W
  q41 : Eqn
  q41 = wE 274 W
  q42 : Eqn
  q42 = wE 322 W
  q43 : Eqn
  q43 = wE 313 W
  q44 : Eqn
  q44 = wE 312 W
  q45 : Eqn
  q45 = wE 31 W

-- a0 Ri = Ri a0^-1 @1023: 139 steps
lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 : ⟪ (ℓ "习丽习举与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丽习举习") ⟫ʷ
lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 = derive (ℓ "习丽习举与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丽习举习")
  (rw 12 q21 ∷
   rw 11 q22 ∷
   rw 10 q23 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw⁻ 11 q24 ∷
   rw 10 q25 ∷
   rw⁻ 9 q24 ∷
   re 10 3 (ℓ "丮") ∷
   re 8 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 15 q26 ∷
   rw 14 q27 ∷
   rw 13 q28 ∷
   rw 12 q29 ∷
   rw 11 q25 ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   rw 8 q27 ∷
   rw 9 q31 ∷
   re 9 8 (ℓ "九") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q24 ∷
   rw 8 q30 ∷
   rw⁻ 7 q24 ∷
   re 8 3 (ℓ "中") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 13 q26 ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   rw 10 q29 ∷
   rw 9 q25 ∷
   rw 8 q29 ∷
   rw 7 q30 ∷
   rw 6 q27 ∷
   rw 7 q31 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q27 ∷
   rw 4 q32 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw⁻ 5 q24 ∷
   rw 4 q25 ∷
   rw⁻ 3 q24 ∷
   re 4 3 (ℓ "丮") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 5 q25 ∷
   rw 4 q29 ∷
   rw 3 q30 ∷
   rw 2 q27 ∷
   rw 3 q31 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q24 ∷
   rw 2 q30 ∷
   rw⁻ 1 q24 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 7 q26 ∷
   rw 6 q27 ∷
   rw 5 q28 ∷
   rw 4 q29 ∷
   rw 3 q25 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 0 q27 ∷
   rw 1 q31 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q33 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 2 q35 ∷
   rw 3 q36 ∷
   rw 4 q37 ∷
   rw 5 q38 ∷
   rw 6 q37 ∷
   rw 7 q39 ∷
   rw 8 q35 ∷
   rw 9 q40 ∷
   rw 2 q41 ∷
   re 2 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q24 ∷
   rw 4 q39 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q37 ∷
   rw 7 q38 ∷
   rw 8 q37 ∷
   rw 9 q39 ∷
   rw 10 q35 ∷
   rw 11 q40 ∷
   rw 4 q41 ∷
   re 4 8 (ℓ "习") ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q24 ∷
   rw 6 q42 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "举") ∷
   rw 6 q43 ∷
   rw 7 q44 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q24 ∷
   rw 9 q39 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "丽") ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 9 q35 ∷
   rw 10 q36 ∷
   rw 11 q37 ∷
   rw 12 q38 ∷
   rw 13 q37 ∷
   rw 14 q39 ∷
   rw 15 q35 ∷
   rw 16 q40 ∷
   rw 9 q41 ∷
   re 9 8 (ℓ "习") ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 10 q24 ∷
   rw 11 q42 ∷
   rw 12 q24 ∷
   re 10 3 (ℓ "举") ∷
   re 12 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 11 q35 ∷
   rw 12 q36 ∷
   rw 13 q37 ∷
   rw 14 q38 ∷
   rw 15 q37 ∷
   rw 16 q39 ∷
   rw 17 q35 ∷
   rw 18 q40 ∷
   rw 11 q41 ∷
   re 11 8 (ℓ "习") ∷
   rw 12 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = sE 2485 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3
  q47 : Eqn
  q47 = sE 2255 lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q48 : Eqn
  q48 = sE 2251 lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q49 : Eqn
  q49 = sE 3353 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q50 : Eqn
  q50 = sE 2249 lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q51 : Eqn
  q51 = sE 2253 lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q52 : Eqn
  q52 = sE 2485 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3

-- pass [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丞与丐习丽习举丑丏丞丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丞与丐习丽习举丑丏丞") ⟫ʷ
lem-pass-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丞与丐习丽习举丑丏丞丈上中九丮九下三") (ℓ "丈上中九丮九下三丞与丐习丽习举丑丏丞")
  (rw 0 q46 ∷
   rw 15 q47 ∷
   rw 12 q48 ∷
   rw 6 q49 ∷
   rw 3 q50 ∷
   rw 0 q51 ∷
   rw⁻ 8 q52 ∷ []) Eq.refl
