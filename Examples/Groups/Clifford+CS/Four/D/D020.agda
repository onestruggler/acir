{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D020 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 12 W
  q2 : Eqn
  q2 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q3 : Eqn
  q3 = wE 398 W
  q4 : Eqn
  q4 = wE 14 W
  q5 : Eqn
  q5 = wE 15 W
  q6 : Eqn
  q6 = wE 16 W
  q7 : Eqn
  q7 = wE 366 W
  q8 : Eqn
  q8 = wE 48 W
  q9 : Eqn
  q9 = eqn (ℓ "丼丞") (ℓ "丞丼") (low₃-comm ((Swap ↑)) (X))
  q10 : Eqn
  q10 = wE 280 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = wE 196 W
  q17 : Eqn
  q17 = wE 173 W
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = wE 127 W
  q20 : Eqn
  q20 = wE 271 W
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 8 W
  q24 : Eqn
  q24 = wE 9 W
  q25 : Eqn
  q25 = wE 10 W
  q26 : Eqn
  q26 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q28 : Eqn
  q28 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q29 : Eqn
  q29 = wE 272 W
  q30 : Eqn
  q30 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q31 : Eqn
  q31 = wE 273 W
  q32 : Eqn
  q32 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q33 : Eqn
  q33 = wE 22 W
  q34 : Eqn
  q34 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q35 : Eqn
  q35 = wE 23 W
  q36 : Eqn
  q36 = wE 84 W
  q37 : Eqn
  q37 = wE 65 W
  q38 : Eqn
  q38 = wE 123 W
  q39 : Eqn
  q39 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q40 : Eqn
  q40 = wE 24 W
  q41 : Eqn
  q41 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q42 : Eqn
  q42 = wE 25 W
  q43 : Eqn
  q43 = wE 124 W
  q44 : Eqn
  q44 = wE 125 W
  q45 : Eqn
  q45 = wE 215 W
  q46 : Eqn
  q46 = wE 121 W
  q47 : Eqn
  q47 = wE 30 W
  q48 : Eqn
  q48 = wE 27 W
  q49 : Eqn
  q49 = wE 122 W
  q50 : Eqn
  q50 = wE 31 W
  q51 : Eqn
  q51 = wE 118 W
  q52 : Eqn
  q52 = wE 74 W
  q53 : Eqn
  q53 = wE 216 W
  q54 : Eqn
  q54 = wE 217 W
  q55 : Eqn
  q55 = wE 218 W
  q56 : Eqn
  q56 = eqn (ℓ "丌两丌乢丠乢") (ℓ "乢丠乢丌两丌") (ax ck-tct)
  q57 : Eqn
  q57 = wE 219 W
  q58 : Eqn
  q58 = wE 220 W
  q59 : Eqn
  q59 = wE 221 W
  q60 : Eqn
  q60 = wE 49 W
  q61 : Eqn
  q61 = wE 51 W
  q62 : Eqn
  q62 = wE 56 W
  q63 : Eqn
  q63 = wE 222 W
  q64 : Eqn
  q64 = wE 28 W
  q65 : Eqn
  q65 = wE 29 W
  q66 : Eqn
  q66 = wE 274 W
  q67 : Eqn
  q67 = wE 275 W
  q68 : Eqn
  q68 = wE 175 W
  q69 : Eqn
  q69 = wE 340 W
  q70 : Eqn
  q70 = wE 18 W
  q71 : Eqn
  q71 = wE 19 W
  q72 : Eqn
  q72 = wE 363 W
  q73 : Eqn
  q73 = wE 20 W
  q74 : Eqn
  q74 = wE 359 W
  q75 : Eqn
  q75 = wE 399 W

-- pass [X3 CK32 X3] [TOFF201 CS23 TOFF201 CSd23]: 712 steps
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丞乗丞乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丞乗丞乣义乣乊") (ℓ "乣义乣乊丞乗丞")
  (rw 6 q1 ∷
   re 5 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q4 ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q5 ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "习") ∷
   rw 4 q8 ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q4 ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q5 ∷
   rw 5 q1 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "习") ∷
   rw⁻ 2 q9 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 13 q12 ∷
   rw 12 q13 ∷
   rw 11 q11 ∷
   re 12 3 (ℓ "中") ∷
   rw 10 q14 ∷
   rw 9 q11 ∷
   re 10 3 (ℓ "举") ∷
   rw 8 q14 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q13 ∷
   rw 7 q11 ∷
   rw⁻ 8 q13 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q15 ∷
   rw⁻ 12 q14 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q15 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q12 ∷
   rw 8 q16 ∷
   re 8 8 (ℓ "习") ∷
   re 7 3 (ℓ "乡") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q12 ∷
   rw 10 q13 ∷
   rw 9 q11 ∷
   re 10 3 (ℓ "中") ∷
   rw 8 q14 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "举") ∷
   rw 6 q14 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q13 ∷
   rw 5 q11 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q15 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 13 q12 ∷
   rw 6 q16 ∷
   re 6 8 (ℓ "习") ∷
   re 5 3 (ℓ "乡") ∷
   rw 3 q17 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 4 q15 ∷
   rw 1 q17 ∷
   rw 8 q18 ∷
   re 7 1 (ℓ "乏习乏") ∷
   re 8 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 7 q13 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q14 ∷
   rw 14 q11 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q13 ∷
   rw⁻ 14 q12 ∷
   rw 15 q15 ∷
   rw 14 q19 ∷
   rw 13 q20 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q21 ∷
   rw 13 q22 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q23 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw⁻ 12 q21 ∷
   rw 11 q24 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (ℓ "丮") ∷
   rw 9 q23 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw⁻ 10 q21 ∷
   rw 9 q25 ∷
   rw⁻ 8 q21 ∷
   re 9 3 (ℓ "中") ∷
   rw 7 q20 ∷
   rw 8 q11 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q15 ∷
   rw⁻ 11 q27 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw 12 q15 ∷
   rw⁻ 13 q27 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q15 ∷
   rw⁻ 15 q26 ∷
   rw⁻ 16 q28 ∷
   rw 9 q29 ∷
   re 9 8 (ℓ "九") ∷
   re 8 3 (ℓ "乞") ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏习乏") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 5 q13 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q13 ∷
   rw⁻ 12 q12 ∷
   rw 13 q15 ∷
   rw 12 q19 ∷
   rw 11 q20 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q21 ∷
   rw 11 q22 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q23 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw⁻ 10 q21 ∷
   rw 9 q24 ∷
   rw⁻ 8 q21 ∷
   re 9 3 (ℓ "丮") ∷
   rw 7 q23 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw⁻ 8 q21 ∷
   rw 7 q25 ∷
   rw⁻ 6 q21 ∷
   re 7 3 (ℓ "中") ∷
   rw 5 q20 ∷
   rw 6 q11 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q15 ∷
   rw⁻ 9 q27 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 10 q15 ∷
   rw⁻ 11 q27 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q15 ∷
   rw⁻ 13 q26 ∷
   rw⁻ 14 q28 ∷
   rw 7 q29 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw⁻ 4 q30 ∷
   rw 3 q31 ∷
   rw⁻ 2 q30 ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q26 ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q14 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q14 ∷
   rw 15 q11 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q26 ∷
   rw⁻ 15 q12 ∷
   rw 16 q15 ∷
   rw 15 q2 ∷
   rw 14 q32 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q33 ∷
   rw 15 q34 ∷
   rw 13 q35 ∷
   re 14 5 (ℓ "中") ∷
   rw 12 q1 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q36 ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q37 ∷
   rw 8 q32 ∷
   rw 9 q18 ∷
   rw 10 q38 ∷
   rw 11 q39 ∷
   rw 12 q40 ∷
   rw 13 q41 ∷
   rw 14 q40 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q21 ∷
   rw 16 q42 ∷
   rw 17 q21 ∷
   re 15 3 (ℓ "丽") ∷
   rw 16 q38 ∷
   rw 17 q43 ∷
   rw 10 q44 ∷
   re 10 8 (ℓ "乢") ∷
   re 9 3 (ℓ "也") ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q4 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q26 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q14 ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q14 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q26 ∷
   rw⁻ 13 q12 ∷
   rw 14 q15 ∷
   rw 13 q2 ∷
   rw 12 q32 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q33 ∷
   rw 13 q34 ∷
   rw 11 q35 ∷
   re 12 5 (ℓ "中") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q36 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q37 ∷
   rw 6 q32 ∷
   rw 7 q18 ∷
   rw 8 q38 ∷
   rw 9 q39 ∷
   rw 10 q40 ∷
   rw 11 q41 ∷
   rw 12 q40 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q21 ∷
   rw 14 q42 ∷
   rw 15 q21 ∷
   re 13 3 (ℓ "丽") ∷
   rw 14 q38 ∷
   rw 15 q43 ∷
   rw 8 q44 ∷
   re 8 8 (ℓ "乢") ∷
   re 7 3 (ℓ "也") ∷
   rw 5 q45 ∷
   re 4 1 (ℓ "丼临丼") ∷
   rw 6 q4 ∷
   rw 3 q45 ∷
   rw 10 q18 ∷
   re 9 1 (ℓ "並乢並") ∷
   re 10 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 9 q46 ∷
   rw 10 q39 ∷
   rw 11 q47 ∷
   rw 12 q41 ∷
   rw 13 q47 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q21 ∷
   rw 15 q48 ∷
   rw 16 q21 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q46 ∷
   rw 16 q49 ∷
   rw 17 q50 ∷
   rw 16 q19 ∷
   rw 15 q51 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q21 ∷
   rw 15 q22 ∷
   rw⁻ 14 q21 ∷
   re 15 3 (ℓ "丽") ∷
   rw 13 q52 ∷
   rw⁻ 12 q41 ∷
   rw 11 q52 ∷
   rw⁻ 10 q39 ∷
   rw 9 q51 ∷
   rw 10 q44 ∷
   re 10 8 (ℓ "乢") ∷
   rw 8 q53 ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q46 ∷
   rw 8 q39 ∷
   rw 9 q47 ∷
   rw 10 q41 ∷
   rw 11 q47 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q21 ∷
   rw 13 q48 ∷
   rw 14 q21 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q46 ∷
   rw 14 q49 ∷
   rw 15 q50 ∷
   rw 14 q19 ∷
   rw 13 q51 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q21 ∷
   rw 13 q22 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q52 ∷
   rw⁻ 10 q41 ∷
   rw 9 q52 ∷
   rw⁻ 8 q39 ∷
   rw 7 q51 ∷
   rw 8 q44 ∷
   re 8 8 (ℓ "乢") ∷
   rw 6 q54 ∷
   rw 5 q55 ∷
   rw 4 q54 ∷
   rw 5 q56 ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q46 ∷
   rw 5 q39 ∷
   rw 6 q47 ∷
   rw 7 q41 ∷
   rw 8 q47 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q21 ∷
   rw 10 q48 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q46 ∷
   rw 11 q49 ∷
   rw 4 q18 ∷
   rw 5 q38 ∷
   rw 6 q39 ∷
   rw 7 q40 ∷
   rw 8 q41 ∷
   rw 9 q40 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q21 ∷
   rw 11 q42 ∷
   rw 12 q21 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q38 ∷
   rw 12 q43 ∷
   rw 5 q44 ∷
   re 5 8 (ℓ "乢") ∷
   re 4 3 (ℓ "也") ∷
   rw 5 q57 ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q46 ∷
   rw 7 q39 ∷
   rw 8 q47 ∷
   rw 9 q41 ∷
   rw 10 q47 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q21 ∷
   rw 12 q48 ∷
   rw 13 q21 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q46 ∷
   rw 13 q49 ∷
   rw 6 q18 ∷
   rw 7 q38 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 10 q41 ∷
   rw 11 q40 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q21 ∷
   rw 13 q42 ∷
   rw 14 q21 ∷
   re 12 3 (ℓ "丽") ∷
   rw 13 q38 ∷
   rw 14 q43 ∷
   rw 7 q44 ∷
   re 7 8 (ℓ "乢") ∷
   re 6 3 (ℓ "也") ∷
   rw 7 q58 ∷
   rw 8 q59 ∷
   rw 9 q58 ∷
   rw 10 q50 ∷
   re 4 1 (ℓ "並乢並") ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q46 ∷
   rw 5 q39 ∷
   rw 6 q47 ∷
   rw 7 q41 ∷
   rw 8 q47 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q21 ∷
   rw 10 q48 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q46 ∷
   rw 11 q49 ∷
   rw 12 q50 ∷
   rw⁻ 3 q32 ∷
   rw 4 q60 ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 5 q4 ∷
   rw 6 q61 ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q33 ∷
   rw⁻ 10 q34 ∷
   rw 11 q35 ∷
   re 8 5 (ℓ "中") ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q2 ∷
   rw 3 q11 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q15 ∷
   rw⁻ 6 q14 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q15 ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q12 ∷
   rw 4 q62 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丧") ∷
   re 6 1 (ℓ "並乢並") ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q46 ∷
   rw 7 q39 ∷
   rw 8 q47 ∷
   rw 9 q41 ∷
   rw 10 q47 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q21 ∷
   rw 12 q48 ∷
   rw 13 q21 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q46 ∷
   rw 13 q49 ∷
   rw 14 q50 ∷
   rw⁻ 5 q32 ∷
   rw 6 q60 ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 7 q4 ∷
   rw 8 q61 ∷
   re 10 1 (ℓ "丼丣丼") ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q33 ∷
   rw⁻ 12 q34 ∷
   rw 13 q35 ∷
   re 10 5 (ℓ "中") ∷
   rw⁻ 11 q32 ∷
   rw⁻ 12 q2 ∷
   rw 5 q11 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q15 ∷
   rw⁻ 12 q26 ∷
   rw⁻ 13 q12 ∷
   rw 6 q62 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw 6 q63 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乄") ∷
   rw 8 q63 ∷
   rw 9 q4 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q26 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q14 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q26 ∷
   rw⁻ 10 q12 ∷
   rw 11 q15 ∷
   rw 2 q38 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw 4 q48 ∷
   rw 5 q21 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q64 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q21 ∷
   rw 6 q65 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q64 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q21 ∷
   rw 8 q42 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q38 ∷
   rw 9 q43 ∷
   rw 2 q11 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q15 ∷
   rw⁻ 5 q27 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q15 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q15 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 10 q28 ∷
   rw 3 q66 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 3 q42 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q26 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q26 ∷
   rw⁻ 12 q12 ∷
   rw 13 q15 ∷
   rw 4 q38 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw 6 q48 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q64 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q21 ∷
   rw 8 q65 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q64 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw 10 q42 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q38 ∷
   rw 11 q43 ∷
   rw 4 q11 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q15 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 8 q15 ∷
   rw⁻ 9 q27 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q15 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 12 q28 ∷
   rw 5 q66 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 5 q30 ∷
   rw 6 q67 ∷
   rw 7 q30 ∷
   rw 8 q50 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q13 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q14 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q14 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q13 ∷
   rw⁻ 9 q12 ∷
   rw 10 q15 ∷
   rw⁻ 1 q13 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q15 ∷
   rw⁻ 3 q14 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q15 ∷
   rw⁻ 5 q14 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q15 ∷
   rw⁻ 7 q13 ∷
   rw⁻ 8 q12 ∷
   rw 1 q16 ∷
   re 1 8 (ℓ "习") ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q13 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q14 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q14 ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q12 ∷
   rw 12 q15 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q15 ∷
   rw⁻ 5 q14 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q15 ∷
   rw⁻ 7 q14 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q15 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 10 q12 ∷
   rw 3 q16 ∷
   re 3 8 (ℓ "习") ∷
   rw 4 q68 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "乔") ∷
   rw 6 q68 ∷
   rw 7 q15 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 0 q69 ∷
   rw 1 q70 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q71 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q4 ∷
   rw 6 q69 ∷
   rw⁻ 7 q2 ∷
   rw 0 q72 ∷
   re 0 8 (ℓ "乣") ∷
   rw 1 q73 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 2 q69 ∷
   rw 3 q70 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q71 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q4 ∷
   rw 8 q69 ∷
   rw⁻ 9 q2 ∷
   rw 2 q72 ∷
   re 2 8 (ℓ "乣") ∷
   rw 3 q9 ∷
   rw 4 q74 ∷
   rw 5 q9 ∷
   rw 6 q4 ∷
   rw 3 q75 ∷ []) Eq.refl
