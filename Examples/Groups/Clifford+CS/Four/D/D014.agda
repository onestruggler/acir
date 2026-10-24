{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D014 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 196 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = wE 127 W
  q10 : Eqn
  q10 = wE 271 W
  q11 : Eqn
  q11 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 8 W
  q14 : Eqn
  q14 = wE 9 W
  q15 : Eqn
  q15 = wE 10 W
  q16 : Eqn
  q16 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q19 : Eqn
  q19 = wE 272 W
  q20 : Eqn
  q20 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q21 : Eqn
  q21 = wE 273 W
  q22 : Eqn
  q22 = wE 12 W
  q23 : Eqn
  q23 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q24 : Eqn
  q24 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q25 : Eqn
  q25 = wE 22 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = wE 23 W
  q28 : Eqn
  q28 = wE 84 W
  q29 : Eqn
  q29 = wE 65 W
  q30 : Eqn
  q30 = wE 123 W
  q31 : Eqn
  q31 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q32 : Eqn
  q32 = wE 24 W
  q33 : Eqn
  q33 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q34 : Eqn
  q34 = wE 25 W
  q35 : Eqn
  q35 = wE 124 W
  q36 : Eqn
  q36 = wE 125 W
  q37 : Eqn
  q37 = wE 14 W
  q38 : Eqn
  q38 = wE 215 W
  q39 : Eqn
  q39 = wE 121 W
  q40 : Eqn
  q40 = wE 30 W
  q41 : Eqn
  q41 = wE 27 W
  q42 : Eqn
  q42 = wE 122 W
  q43 : Eqn
  q43 = wE 31 W
  q44 : Eqn
  q44 = wE 118 W
  q45 : Eqn
  q45 = wE 74 W
  q46 : Eqn
  q46 = wE 216 W
  q47 : Eqn
  q47 = wE 217 W
  q48 : Eqn
  q48 = wE 218 W
  q49 : Eqn
  q49 = eqn (ℓ "丌两丌乢丠乢") (ℓ "乢丠乢丌两丌") (ax ck-tct)
  q50 : Eqn
  q50 = wE 219 W
  q51 : Eqn
  q51 = wE 220 W
  q52 : Eqn
  q52 = wE 221 W
  q53 : Eqn
  q53 = wE 49 W
  q54 : Eqn
  q54 = wE 51 W
  q55 : Eqn
  q55 = wE 56 W
  q56 : Eqn
  q56 = wE 222 W
  q57 : Eqn
  q57 = wE 28 W
  q58 : Eqn
  q58 = wE 29 W
  q59 : Eqn
  q59 = wE 274 W
  q60 : Eqn
  q60 = wE 275 W
  q61 : Eqn
  q61 = wE 175 W
  q62 : Eqn
  q62 = wE 276 W

-- pass [X3 CK31 X3] [TOFF102 CS13 TOFF102 CSd13]: 646 steps
lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乔丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乔丞习丽习举") (ℓ "习丽习举丞乔丞")
  (rw 6 q1 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 9 q4 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q3 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q2 ∷
   rw 7 q6 ∷
   re 7 8 (ℓ "习") ∷
   re 6 3 (ℓ "乡") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 7 q4 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw 5 q4 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q3 ∷
   rw 4 q1 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q2 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 7 q8 ∷
   re 6 1 (ℓ "乏习乏") ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q2 ∷
   rw 14 q5 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q13 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw⁻ 11 q11 ∷
   rw 10 q14 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (ℓ "丮") ∷
   rw 8 q13 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q11 ∷
   rw 8 q15 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (ℓ "中") ∷
   rw 6 q10 ∷
   rw 7 q1 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q17 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 11 q5 ∷
   rw⁻ 12 q17 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 15 q18 ∷
   rw 8 q19 ∷
   re 8 8 (ℓ "九") ∷
   re 7 3 (ℓ "乞") ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
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
   rw⁻ 11 q2 ∷
   rw 12 q5 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q11 ∷
   rw 10 q12 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q13 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw⁻ 9 q11 ∷
   rw 8 q14 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (ℓ "丮") ∷
   rw 6 q13 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw⁻ 7 q11 ∷
   rw 6 q15 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (ℓ "中") ∷
   rw 4 q10 ∷
   rw 5 q1 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q17 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q17 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   rw⁻ 12 q16 ∷
   rw⁻ 13 q18 ∷
   rw 6 q19 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q20 ∷
   rw 8 q22 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q16 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q16 ∷
   rw⁻ 14 q2 ∷
   rw 15 q5 ∷
   rw 14 q23 ∷
   rw 13 q24 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q25 ∷
   rw 14 q26 ∷
   rw 12 q27 ∷
   re 13 5 (ℓ "中") ∷
   rw 11 q22 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q28 ∷
   rw 9 q22 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q29 ∷
   rw 7 q24 ∷
   rw 8 q8 ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q32 ∷
   rw 12 q33 ∷
   rw 13 q32 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q11 ∷
   rw 15 q34 ∷
   rw 16 q11 ∷
   re 14 3 (ℓ "丽") ∷
   rw 15 q30 ∷
   rw 16 q35 ∷
   rw 9 q36 ∷
   re 9 8 (ℓ "乢") ∷
   re 8 3 (ℓ "也") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q37 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q16 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q2 ∷
   rw 13 q5 ∷
   rw 12 q23 ∷
   rw 11 q24 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q25 ∷
   rw 12 q26 ∷
   rw 10 q27 ∷
   re 11 5 (ℓ "中") ∷
   rw 9 q22 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q28 ∷
   rw 7 q22 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q29 ∷
   rw 5 q24 ∷
   rw 6 q8 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   rw 10 q33 ∷
   rw 11 q32 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q11 ∷
   rw 13 q34 ∷
   rw 14 q11 ∷
   re 12 3 (ℓ "丽") ∷
   rw 13 q30 ∷
   rw 14 q35 ∷
   rw 7 q36 ∷
   re 7 8 (ℓ "乢") ∷
   re 6 3 (ℓ "也") ∷
   rw 4 q38 ∷
   re 3 1 (ℓ "丼临丼") ∷
   rw 5 q37 ∷
   rw 2 q38 ∷
   rw 9 q8 ∷
   re 8 1 (ℓ "並乢並") ∷
   re 9 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 8 q39 ∷
   rw 9 q31 ∷
   rw 10 q40 ∷
   rw 11 q33 ∷
   rw 12 q40 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   rw 14 q41 ∷
   rw 15 q11 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q39 ∷
   rw 15 q42 ∷
   rw 16 q43 ∷
   rw 15 q9 ∷
   rw 14 q44 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q11 ∷
   rw 14 q12 ∷
   rw⁻ 13 q11 ∷
   re 14 3 (ℓ "丽") ∷
   rw 12 q45 ∷
   rw⁻ 11 q33 ∷
   rw 10 q45 ∷
   rw⁻ 9 q31 ∷
   rw 8 q44 ∷
   rw 9 q36 ∷
   re 9 8 (ℓ "乢") ∷
   rw 7 q46 ∷
   re 6 1 (ℓ "並乢並") ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q39 ∷
   rw 7 q31 ∷
   rw 8 q40 ∷
   rw 9 q33 ∷
   rw 10 q40 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   rw 12 q41 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q39 ∷
   rw 13 q42 ∷
   rw 14 q43 ∷
   rw 13 q9 ∷
   rw 12 q44 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q45 ∷
   rw⁻ 9 q33 ∷
   rw 8 q45 ∷
   rw⁻ 7 q31 ∷
   rw 6 q44 ∷
   rw 7 q36 ∷
   re 7 8 (ℓ "乢") ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   rw 3 q47 ∷
   rw 4 q49 ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q39 ∷
   rw 4 q31 ∷
   rw 5 q40 ∷
   rw 6 q33 ∷
   rw 7 q40 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q11 ∷
   rw 9 q41 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q39 ∷
   rw 10 q42 ∷
   rw 3 q8 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q33 ∷
   rw 8 q32 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q11 ∷
   rw 10 q34 ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q30 ∷
   rw 11 q35 ∷
   rw 4 q36 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   rw 4 q50 ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q39 ∷
   rw 6 q31 ∷
   rw 7 q40 ∷
   rw 8 q33 ∷
   rw 9 q40 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   rw 11 q41 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q39 ∷
   rw 12 q42 ∷
   rw 5 q8 ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   rw 8 q32 ∷
   rw 9 q33 ∷
   rw 10 q32 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q11 ∷
   rw 12 q34 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "丽") ∷
   rw 12 q30 ∷
   rw 13 q35 ∷
   rw 6 q36 ∷
   re 6 8 (ℓ "乢") ∷
   re 5 3 (ℓ "也") ∷
   rw 6 q51 ∷
   rw 7 q52 ∷
   rw 8 q51 ∷
   rw 9 q43 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q39 ∷
   rw 4 q31 ∷
   rw 5 q40 ∷
   rw 6 q33 ∷
   rw 7 q40 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q11 ∷
   rw 9 q41 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q39 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷
   rw⁻ 2 q24 ∷
   rw 3 q53 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q37 ∷
   rw 5 q54 ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 6 q37 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q25 ∷
   rw⁻ 9 q26 ∷
   rw 10 q27 ∷
   re 7 5 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q23 ∷
   rw 2 q1 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 10 q2 ∷
   rw 3 q55 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 5 q22 ∷
   re 3 3 (ℓ "丧") ∷
   re 5 1 (ℓ "並乢並") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q39 ∷
   rw 6 q31 ∷
   rw 7 q40 ∷
   rw 8 q33 ∷
   rw 9 q40 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   rw 11 q41 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q39 ∷
   rw 12 q42 ∷
   rw 13 q43 ∷
   rw⁻ 4 q24 ∷
   rw 5 q53 ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 6 q37 ∷
   rw 7 q54 ∷
   re 9 1 (ℓ "丼丣丼") ∷
   rw 8 q37 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q25 ∷
   rw⁻ 11 q26 ∷
   rw 12 q27 ∷
   re 9 5 (ℓ "中") ∷
   rw⁻ 10 q24 ∷
   rw⁻ 11 q23 ∷
   rw 4 q1 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q2 ∷
   rw 5 q55 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw 5 q56 ∷
   rw 8 q22 ∷
   re 6 3 (ℓ "乄") ∷
   rw 7 q56 ∷
   rw 8 q37 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q16 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q16 ∷
   rw⁻ 9 q2 ∷
   rw 10 q5 ∷
   rw 1 q30 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q11 ∷
   rw 3 q41 ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q57 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q11 ∷
   rw 5 q58 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "丮") ∷
   rw 5 q57 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q11 ∷
   rw 7 q34 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q30 ∷
   rw 8 q35 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q17 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q17 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q18 ∷
   rw 2 q59 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q34 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q16 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q2 ∷
   rw 12 q5 ∷
   rw 3 q30 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw 5 q41 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q57 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q11 ∷
   rw 7 q58 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q57 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q11 ∷
   rw 9 q34 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q30 ∷
   rw 10 q35 ∷
   rw 3 q1 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q17 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q17 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q18 ∷
   rw 4 q59 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 4 q20 ∷
   rw 5 q60 ∷
   rw 6 q20 ∷
   rw 7 q43 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
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
   rw⁻ 8 q2 ∷
   rw 9 q5 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw 0 q6 ∷
   re 0 8 (ℓ "习") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q2 ∷
   rw 11 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q2 ∷
   rw 2 q6 ∷
   re 2 8 (ℓ "习") ∷
   rw 3 q61 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乔") ∷
   rw 5 q61 ∷
   rw 6 q5 ∷
   rw 3 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 277 W

-- pass [X3 CS31 X3] [TOFF103]: 65 steps
lem-pass-X3-CS31-X3-vs-TOFF103 : ⟪ (ℓ "丞丽丞乡") ⟫ʷ ≈ ⟪ (ℓ "乡丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF103 = derive (ℓ "丞丽丞乡") (ℓ "乡丞丽丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "习") ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q63 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q3 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw 0 q1 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q2 ∷
   rw 1 q6 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q61 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q61 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 234 W

-- pass [X3 CS31 X3] [CS12]: 1 steps
lem-pass-X3-CS31-X3-vs-CS12 : ⟪ (ℓ "丞丽丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS12 = derive (ℓ "丞丽丞丶") (ℓ "丶丞丽丞")
  (rw 0 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 235 W

-- pass [X3 CS31 X3] [CSd12]: 1 steps
lem-pass-X3-CS31-X3-vs-CSd12 : ⟪ (ℓ "丞丽丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CSd12 = derive (ℓ "丞丽丞丷") (ℓ "丷丞丽丞")
  (rw 0 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q67 : Eqn
  q67 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q68 : Eqn
  q68 = wE 48 W

-- pass [X3 CS31 X3] [CS02]: 7 steps
lem-pass-X3-CS31-X3-vs-CS02 : ⟪ (ℓ "丞丽丞丧") ⟫ʷ ≈ ⟪ (ℓ "丧丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS02 = derive (ℓ "丞丽丞丧") (ℓ "丧丞丽丞")
  (rw⁻ 2 q66 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q29 ∷
   rw⁻ 2 q67 ∷
   rw 3 q68 ∷
   re 1 3 (ℓ "丧") ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
