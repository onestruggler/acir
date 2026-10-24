{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD624 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D624 (W : Ws) (Sᴰ : SD624) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-Sd0 : St 1428
  lem-pass-CS13-vs-Sd0 = pickᴰ 3 Sᴰ
  lem-pass-CS13-vs-S3 : St 1462
  lem-pass-CS13-vs-S3 = pickᴰ 4 Sᴰ
  lem-pass-CS13-vs-Sd3 : St 1463
  lem-pass-CS13-vs-Sd3 = pickᴰ 5 Sᴰ
  lem-pass-CS13-vs-iI : St 1464
  lem-pass-CS13-vs-iI = pickᴰ 6 Sᴰ
  lem-pass-CS13-vs-TOFF012 : St 1434
  lem-pass-CS13-vs-TOFF012 = pickᴰ 7 Sᴰ
  lem-pass-CCZ123-vs-TOFF013 : St 1465
  lem-pass-CCZ123-vs-TOFF013 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 1362 W
  q9 : Eqn
  q9 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q10 : Eqn
  q10 = wE 69 W
  q11 : Eqn
  q11 = wE 12 W
  q12 : Eqn
  q12 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q13 : Eqn
  q13 = wE 30 W
  q14 : Eqn
  q14 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 22 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = wE 23 W
  q21 : Eqn
  q21 = wE 14 W
  q22 : Eqn
  q22 = wE 47 W
  q23 : Eqn
  q23 = wE 48 W
  q24 : Eqn
  q24 = wE 43 W
  q25 : Eqn
  q25 = wE 5 W
  q26 : Eqn
  q26 = wE 6 W
  q27 : Eqn
  q27 = wE 7 W
  q28 : Eqn
  q28 = wE 8 W
  q29 : Eqn
  q29 = wE 9 W
  q30 : Eqn
  q30 = wE 10 W
  q31 : Eqn
  q31 = wE 11 W
  q32 : Eqn
  q32 = wE 13 W
  q33 : Eqn
  q33 = wE 15 W
  q34 : Eqn
  q34 = wE 16 W
  q35 : Eqn
  q35 = wE 17 W
  q36 : Eqn
  q36 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q37 : Eqn
  q37 = wE 18 W
  q38 : Eqn
  q38 = wE 19 W
  q39 : Eqn
  q39 = wE 20 W
  q40 : Eqn
  q40 = wE 21 W
  q41 : Eqn
  q41 = wE 24 W
  q42 : Eqn
  q42 = wE 25 W
  q43 : Eqn
  q43 = wE 26 W
  q44 : Eqn
  q44 = wE 28 W
  q45 : Eqn
  q45 = wE 29 W
  q46 : Eqn
  q46 = wE 71 W
  q47 : Eqn
  q47 = wE 72 W
  q48 : Eqn
  q48 = wE 73 W
  q49 : Eqn
  q49 = wE 49 W
  q50 : Eqn
  q50 = wE 50 W
  q51 : Eqn
  q51 = wE 51 W
  q52 : Eqn
  q52 = wE 52 W
  q53 : Eqn
  q53 = sE 1465 lem-pass-CCZ123-vs-TOFF013
  q54 : Eqn
  q54 = wE 45 W
  q55 : Eqn
  q55 = wE 1882 W
  q56 : Eqn
  q56 = wE 1883 W
  q57 : Eqn
  q57 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q58 : Eqn
  q58 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q59 : Eqn
  q59 = wE 46 W
  q60 : Eqn
  q60 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)
  q61 : Eqn
  q61 = wE 1364 W
  q62 : Eqn
  q62 = wE 175 W
  q63 : Eqn
  q63 = wE 33 W

-- pass [CCZ023] [X3 TOFF013 X3]: 686 steps
lem-pass-CCZ023-vs-X3-TOFF013-X3 : ⟪ (ℓ "乛丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞乛") ⟫ʷ
lem-pass-CCZ023-vs-X3-TOFF013-X3 = derive (ℓ "乛丞乞丞") (ℓ "丞乞丞乛")
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q9 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q6 ∷
   rw 0 q10 ∷
   rw 4 q11 ∷
   rw 3 q11 ∷
   re 4 3 (ℓ "乃") ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q12 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷
   rw 5 q13 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q17 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q18 ∷
   rw 8 q19 ∷
   rw 6 q20 ∷
   re 7 5 (ℓ "中") ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 5 q21 ∷
   rw 2 q23 ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 4 q24 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 1 q11 ∷
   re 2 3 (ℓ "乃") ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "乐") ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 4 q24 ∷
   re 4 5 (ℓ "乙") ∷
   rw 2 q1 ∷
   re 3 3 (ℓ "乐") ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw⁻ 7 q15 ∷
   rw 6 q26 ∷
   rw⁻ 5 q15 ∷
   re 6 3 (ℓ "乓") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q27 ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 5 q28 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   re 5 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw⁻ 5 q15 ∷
   rw 4 q26 ∷
   rw⁻ 3 q15 ∷
   re 4 3 (ℓ "乓") ∷
   rw 7 q11 ∷
   rw 6 q32 ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 11 q21 ∷
   rw 8 q11 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q33 ∷
   rw 6 q11 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q34 ∷
   rw 6 q35 ∷
   re 6 5 (ℓ "乙") ∷
   rw 4 q32 ∷
   rw 5 q36 ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q37 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q38 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 8 q21 ∷
   rw 4 q35 ∷
   re 4 5 (ℓ "乙") ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q6 ∷
   rw 5 q39 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 7 q40 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "个") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q18 ∷
   rw⁻ 11 q19 ∷
   rw 12 q20 ∷
   re 9 5 (ℓ "中") ∷
   rw 5 q25 ∷
   rw 6 q12 ∷
   rw 7 q41 ∷
   rw 8 q14 ∷
   rw 9 q41 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q15 ∷
   rw 11 q42 ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q43 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   rw 6 q21 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q16 ∷
   rw 4 q44 ∷
   rw 5 q45 ∷
   rw 6 q44 ∷
   rw 7 q42 ∷
   rw 3 q31 ∷
   re 3 5 (ℓ "乙") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q13 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q15 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q17 ∷
   rw 4 q12 ∷
   rw 5 q41 ∷
   rw 6 q14 ∷
   rw 7 q41 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q15 ∷
   rw 9 q42 ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q43 ∷
   re 4 5 (ℓ "乜") ∷
   rw 5 q17 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q1 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 3 q24 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q46 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乀") ∷
   rw 5 q47 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 3 q48 ∷
   re 3 5 (ℓ "乜") ∷
   rw 4 q6 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q6 ∷
   rw 1 q39 ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q40 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q18 ∷
   rw⁻ 7 q19 ∷
   rw 8 q20 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q25 ∷
   rw 2 q12 ∷
   rw 3 q41 ∷
   rw 4 q14 ∷
   rw 5 q41 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q15 ∷
   rw 7 q42 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q43 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q49 ∷
   rw 3 q50 ∷
   rw 4 q51 ∷
   rw 5 q50 ∷
   rw 6 q39 ∷
   rw 2 q52 ∷
   re 2 5 (ℓ "乜") ∷
   rw 3 q21 ∷
   rw 2 q53 ∷
   rw 1 q1 ∷
   rw 2 q54 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q6 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 12 q6 ∷
   rw 11 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 4 q3 ∷
   rw 5 q7 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q13 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q17 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "丰") ∷
   rw 5 q55 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "丰") ∷
   rw 3 q56 ∷
   rw 4 q25 ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw 6 q15 ∷
   rw 7 q41 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "乀") ∷
   rw 7 q14 ∷
   re 9 1 (ℓ "乏个乏") ∷
   rw 8 q15 ∷
   rw 9 q41 ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乀") ∷
   rw 9 q42 ∷
   rw 5 q48 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   rw 6 q11 ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 12 q57 ∷
   rw 11 q58 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q21 ∷
   rw 9 q11 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q33 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q34 ∷
   rw 5 q58 ∷
   rw 6 q59 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q12 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 7 q13 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q17 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   rw 8 q20 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q21 ∷
   rw 4 q23 ∷
   rw 5 q1 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 6 q24 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 10 q57 ∷
   rw 9 q58 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q21 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q33 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q34 ∷
   rw 3 q58 ∷
   rw 4 q59 ∷
   re 4 8 (ℓ "九") ∷
   rw 4 q60 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   rw 3 q39 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q40 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q18 ∷
   rw⁻ 9 q19 ∷
   rw 10 q20 ∷
   re 7 5 (ℓ "中") ∷
   rw 3 q25 ∷
   rw 4 q12 ∷
   rw 5 q41 ∷
   rw 6 q14 ∷
   rw 7 q41 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q15 ∷
   rw 9 q42 ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q43 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q49 ∷
   rw 5 q50 ∷
   rw 6 q51 ∷
   rw 7 q50 ∷
   rw 8 q39 ∷
   rw 4 q52 ∷
   re 4 5 (ℓ "乜") ∷
   rw 5 q21 ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q13 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q17 ∷
   rw 2 q46 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丰") ∷
   rw 4 q47 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丰") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 2 q25 ∷
   rw 3 q12 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw 4 q15 ∷
   rw 5 q41 ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "乀") ∷
   rw 5 q14 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw 6 q15 ∷
   rw 7 q41 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "乀") ∷
   rw 7 q42 ∷
   rw 3 q48 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q46 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乀") ∷
   rw 5 q47 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 3 q48 ∷
   re 3 5 (ℓ "乜") ∷
   rw 4 q6 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q9 ∷
   rw 1 q61 ∷
   rw 0 q62 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q62 ∷
   rw 3 q6 ∷
   rw 4 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 1434 lem-pass-CS13-vs-TOFF012
  q65 : Eqn
  q65 = sE 1464 lem-pass-CS13-vs-iI
  q66 : Eqn
  q66 = sE 1428 lem-pass-CS13-vs-Sd0
  q67 : Eqn
  q67 = sE 1463 lem-pass-CS13-vs-Sd3
  q68 : Eqn
  q68 = sE 1092 lem-pass-CS13-vs-CS03
  q69 : Eqn
  q69 = sE 63 lem-pass-CS13-vs-S0
  q70 : Eqn
  q70 = sE 1462 lem-pass-CS13-vs-S3
  q71 : Eqn
  q71 = sE 1093 lem-pass-CS13-vs-CSd03

-- pass [CS13] [TOFF012 iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03]: 12 steps
lem-pass-CS13-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 : ⟪ (ℓ "丽九一三丛中九一一一丈业丮") ⟫ʷ ≈ ⟪ (ℓ "九一三丛中九一一一丈业丮丽") ⟫ʷ
lem-pass-CS13-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 = derive (ℓ "丽九一三丛中九一一一丈业丮") (ℓ "九一三丛中九一一一丈业丮丽")
  (rw 0 q64 ∷
   rw 1 q65 ∷
   rw 2 q66 ∷
   rw 3 q67 ∷
   rw 4 q68 ∷
   rw 5 q64 ∷
   rw 6 q65 ∷
   rw 7 q65 ∷
   rw 8 q65 ∷
   rw 9 q69 ∷
   rw 10 q70 ∷
   rw 11 q71 ∷ []) Eq.refl
