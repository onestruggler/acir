{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD540 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D540 (W : Ws) (Sᴰ : SD540) where

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
  lem-pass-CCZ023-vs-CS23 : St 854
  lem-pass-CCZ023-vs-CS23 = pickᴰ 0 Sᴰ
  lem-pass-CCZ023-vs-CZ23 : St 855
  lem-pass-CCZ023-vs-CZ23 = pickᴰ 1 Sᴰ
  lem-pass-CS23-vs-CS01 : St 151
  lem-pass-CS23-vs-CS01 = pickᴰ 2 Sᴰ
  lem-pass-S0-vs-CS01 : St 86
  lem-pass-S0-vs-CS01 = pickᴰ 3 Sᴰ
  lem-pass-S0-vs-CSd01 : St 87
  lem-pass-S0-vs-CSd01 = pickᴰ 4 Sᴰ
  lem-pass-CCZ023-vs-CS01 : St 856
  lem-pass-CCZ023-vs-CS01 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 121 W
  q3 : Eqn
  q3 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = wE 30 W
  q5 : Eqn
  q5 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 122 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 127 W
  q11 : Eqn
  q11 = wE 118 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 125 W
  q15 : Eqn
  q15 = wE 481 W
  q16 : Eqn
  q16 = wE 1468 W
  q17 : Eqn
  q17 = wE 123 W
  q18 : Eqn
  q18 = wE 24 W
  q19 : Eqn
  q19 = wE 25 W
  q20 : Eqn
  q20 = wE 124 W
  q21 : Eqn
  q21 = wE 315 W
  q22 : Eqn
  q22 = wE 26 W
  q23 : Eqn
  q23 = sE 856 lem-pass-CCZ023-vs-CS01
  q24 : Eqn
  q24 = sE 151 lem-pass-CS23-vs-CS01
  q25 : Eqn
  q25 = sE 86 lem-pass-S0-vs-CS01
  q26 : Eqn
  q26 = wE 1469 W
  q27 : Eqn
  q27 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q28 : Eqn
  q28 = wE 1374 W
  q29 : Eqn
  q29 = sE 854 lem-pass-CCZ023-vs-CS23
  q30 : Eqn
  q30 = sE 855 lem-pass-CCZ023-vs-CZ23
  q31 : Eqn
  q31 = wE 1470 W
  q32 : Eqn
  q32 = wE 33 W
  q33 : Eqn
  q33 = sE 87 lem-pass-S0-vs-CSd01

-- pass [S0] [TOFF023 CS01 TOFF023 CSd01]: 401 steps
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丈也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丈") ⟫ʷ
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丈也丠也両") (ℓ "也丠也両丈")
  (rw 2 q1 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q2 ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q6 ∷
   rw 7 q12 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q13 ∷
   rw⁻ 4 q5 ∷
   rw 3 q13 ∷
   rw⁻ 2 q3 ∷
   rw 1 q11 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乢") ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q17 ∷
   rw 2 q3 ∷
   rw 3 q18 ∷
   rw 4 q5 ∷
   rw 5 q18 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q17 ∷
   rw 8 q20 ∷
   rw 1 q14 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q21 ∷
   rw 2 q3 ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q22 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q9 ∷
   rw 3 q23 ∷
   rw 2 q24 ∷
   rw 1 q25 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "並乢並") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q2 ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q12 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q13 ∷
   rw⁻ 8 q5 ∷
   rw 7 q13 ∷
   rw⁻ 6 q3 ∷
   rw 5 q11 ∷
   rw 6 q14 ∷
   re 6 8 (ℓ "乢") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (ℓ "乜") ∷
   rw 5 q26 ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 4 q1 ∷
   rw 5 q17 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q17 ∷
   rw 12 q20 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "乢") ∷
   re 4 3 (ℓ "也") ∷
   rw 5 q27 ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   rw 7 q3 ∷
   rw 8 q18 ∷
   rw 9 q5 ∷
   rw 10 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 12 q19 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q22 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   rw 7 q9 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "並乢並") ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 4 q11 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "乢") ∷
   rw⁻ 3 q3 ∷
   rw 4 q28 ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 3 q1 ∷
   rw 4 q17 ∷
   rw 5 q3 ∷
   rw 6 q18 ∷
   rw 7 q5 ∷
   rw 8 q18 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q17 ∷
   rw 11 q20 ∷
   rw 4 q14 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 3 q11 ∷
   rw 4 q14 ∷
   re 4 8 (ℓ "乢") ∷
   rw 2 q15 ∷
   rw 3 q16 ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 2 q1 ∷
   rw 3 q17 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q17 ∷
   rw 10 q20 ∷
   rw 3 q14 ∷
   re 3 8 (ℓ "乢") ∷
   re 2 3 (ℓ "也") ∷
   rw 3 q21 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q1 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q22 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   rw 6 q9 ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 4 q31 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q9 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 6 q22 ∷
   re 6 5 (ℓ "乜") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (ℓ "乜") ∷
   rw 5 q32 ∷
   rw 4 q9 ∷
   rw 3 q33 ∷ []) Eq.refl
