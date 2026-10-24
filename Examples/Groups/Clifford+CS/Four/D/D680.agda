{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD680 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D680 (W : Ws) (Sᴰ : SD680) where

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
  lem-S2 : St 1778
  lem-S2 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q3 : Eqn
  q3 = wE 335 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 127 W
  q9 : Eqn
  q9 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 8 W
  q13 : Eqn
  q13 = wE 9 W
  q14 : Eqn
  q14 = wE 10 W
  q15 : Eqn
  q15 = wE 336 W
  q16 : Eqn
  q16 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q18 : Eqn
  q18 = wE 333 W
  q19 : Eqn
  q19 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q20 : Eqn
  q20 = wE 1882 W
  q21 : Eqn
  q21 = wE 1294 W
  q22 : Eqn
  q22 = wE 368 W
  q23 : Eqn
  q23 = wE 1883 W
  q24 : Eqn
  q24 = wE 12 W
  q25 : Eqn
  q25 = wE 47 W
  q26 : Eqn
  q26 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q27 : Eqn
  q27 = wE 398 W
  q28 : Eqn
  q28 = wE 14 W
  q29 : Eqn
  q29 = wE 15 W
  q30 : Eqn
  q30 = wE 16 W
  q31 : Eqn
  q31 = wE 366 W
  q32 : Eqn
  q32 = wE 48 W
  q33 : Eqn
  q33 = wE 271 W
  q34 : Eqn
  q34 = wE 272 W
  q35 : Eqn
  q35 = sE 1778 lem-S2
  q36 : Eqn
  q36 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q37 : Eqn
  q37 = wE 123 W
  q38 : Eqn
  q38 = wE 27 W
  q39 : Eqn
  q39 = wE 28 W
  q40 : Eqn
  q40 = wE 29 W
  q41 : Eqn
  q41 = wE 25 W
  q42 : Eqn
  q42 = wE 124 W
  q43 : Eqn
  q43 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q44 : Eqn
  q44 = wE 274 W
  q45 : Eqn
  q45 = wE 322 W
  q46 : Eqn
  q46 = wE 31 W
  q47 : Eqn
  q47 = wE 340 W
  q48 : Eqn
  q48 = wE 20 W
  q49 : Eqn
  q49 = wE 21 W
  q50 : Eqn
  q50 = wE 22 W
  q51 : Eqn
  q51 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q52 : Eqn
  q52 = wE 23 W
  q53 : Eqn
  q53 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q54 : Eqn
  q54 = wE 24 W
  q55 : Eqn
  q55 = wE 334 W
  q56 : Eqn
  q56 = wE 18 W
  q57 : Eqn
  q57 = wE 19 W
  q58 : Eqn
  q58 = wE 30 W
  q59 : Eqn
  q59 = wE 122 W
  q60 : Eqn
  q60 = wE 71 W
  q61 : Eqn
  q61 = wE 72 W
  q62 : Eqn
  q62 = wE 385 W
  q63 : Eqn
  q63 = wE 337 W

-- S2 @3102: 581 steps
lem-S2-at3102 : ⟪ (ℓ "书义书乊") ⟫ʷ ≈ ⟪ (ℓ "乨中乨丮") ⟫ʷ
lem-S2-at3102 = derive (ℓ "书义书乊") (ℓ "乨中乨丮")
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (ℓ "乏乣乏") ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 2 q3 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q5 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q5 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw⁻ 9 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q12 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw⁻ 7 q10 ∷
   rw 6 q13 ∷
   rw⁻ 5 q10 ∷
   re 6 3 (ℓ "丮") ∷
   rw 4 q12 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q10 ∷
   rw 4 q14 ∷
   rw⁻ 3 q10 ∷
   re 4 3 (ℓ "中") ∷
   rw⁻ 2 q9 ∷
   rw 3 q4 ∷
   rw 4 q15 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 7 q7 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q7 ∷
   rw 10 q15 ∷
   rw⁻ 11 q17 ∷
   rw 4 q18 ∷
   re 4 8 (ℓ "乣") ∷
   re 3 3 (ℓ "书") ∷
   rw⁻ 1 q19 ∷
   re 0 1 (ℓ "乏乣乏") ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q3 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q5 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q5 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q3 ∷
   rw⁻ 7 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q10 ∷
   rw 6 q11 ∷
   rw⁻ 5 q10 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q12 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw⁻ 5 q10 ∷
   rw 4 q13 ∷
   rw⁻ 3 q10 ∷
   re 4 3 (ℓ "丮") ∷
   rw 2 q12 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q10 ∷
   rw 2 q14 ∷
   rw⁻ 1 q10 ∷
   re 2 3 (ℓ "中") ∷
   rw⁻ 0 q9 ∷
   rw 1 q4 ∷
   rw 2 q15 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q7 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q15 ∷
   rw⁻ 9 q17 ∷
   rw 2 q18 ∷
   re 2 8 (ℓ "乣") ∷
   re 1 3 (ℓ "书") ∷
   rw 5 q4 ∷
   rw 4 q20 ∷
   re 3 1 (ℓ "乏乣乏") ∷
   re 4 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 3 q3 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   rw 7 q5 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q7 ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   re 4 8 (ℓ "乣") ∷
   rw 2 q23 ∷
   re 1 1 (ℓ "乏乣乏") ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q3 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q5 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw⁻ 8 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q7 ∷
   rw 3 q5 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   re 2 8 (ℓ "乣") ∷
   rw 6 q24 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 11 q28 ∷
   rw 8 q24 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q29 ∷
   rw 6 q24 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q30 ∷
   rw 4 q27 ∷
   rw 5 q31 ∷
   re 5 8 (ℓ "习") ∷
   rw 3 q32 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q28 ∷
   rw 6 q24 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q29 ∷
   rw 4 q24 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q30 ∷
   rw 2 q27 ∷
   rw 3 q31 ∷
   re 3 8 (ℓ "习") ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw⁻ 8 q10 ∷
   rw 7 q13 ∷
   rw⁻ 6 q10 ∷
   re 7 3 (ℓ "丮") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q8 ∷
   rw 11 q33 ∷
   rw 10 q11 ∷
   rw 9 q12 ∷
   rw 8 q13 ∷
   rw 7 q12 ∷
   rw 6 q14 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw⁻ 6 q10 ∷
   rw 5 q14 ∷
   rw⁻ 4 q10 ∷
   re 5 3 (ℓ "中") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q8 ∷
   rw 9 q33 ∷
   rw 8 q11 ∷
   rw 7 q12 ∷
   rw 6 q13 ∷
   rw 5 q12 ∷
   rw 4 q14 ∷
   rw 3 q33 ∷
   rw 4 q34 ∷
   re 4 8 (ℓ "九") ∷
   rw 4 q35 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q36 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q5 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q5 ∷
   rw 11 q4 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q36 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   rw 3 q37 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q10 ∷
   rw 5 q38 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q39 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q10 ∷
   rw 7 q40 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q39 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q10 ∷
   rw 9 q41 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q37 ∷
   rw 10 q42 ∷
   rw 3 q4 ∷
   rw⁻ 4 q43 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 7 q7 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q7 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q17 ∷
   rw 4 q44 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 4 q41 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q36 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q5 ∷
   rw 11 q4 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q5 ∷
   rw 13 q4 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q36 ∷
   rw⁻ 13 q6 ∷
   rw 14 q7 ∷
   rw 5 q37 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q10 ∷
   rw 7 q38 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q39 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q10 ∷
   rw 9 q40 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q39 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   rw 11 q41 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q37 ∷
   rw 12 q42 ∷
   rw 5 q4 ∷
   rw⁻ 6 q43 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 9 q7 ∷
   rw⁻ 10 q16 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q7 ∷
   rw⁻ 12 q43 ∷
   rw⁻ 13 q17 ∷
   rw 6 q44 ∷
   re 6 8 (ℓ "习") ∷
   re 5 3 (ℓ "乡") ∷
   rw 6 q45 ∷
   rw 7 q46 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q43 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q43 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 2 q47 ∷
   rw 3 q48 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q49 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q50 ∷
   rw⁻ 9 q51 ∷
   rw 10 q52 ∷
   re 7 5 (ℓ "中") ∷
   rw 8 q47 ∷
   rw⁻ 9 q26 ∷
   rw 2 q1 ∷
   rw 3 q53 ∷
   rw 4 q19 ∷
   rw 5 q54 ∷
   rw 6 q2 ∷
   rw 7 q54 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q10 ∷
   rw 9 q41 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q53 ∷
   rw 10 q42 ∷
   rw 3 q55 ∷
   re 3 8 (ℓ "乥") ∷
   re 2 3 (ℓ "乤") ∷
   rw 3 q56 ∷
   re 5 1 (ℓ "乏习乏") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 5 q43 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q5 ∷
   rw 12 q4 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q43 ∷
   rw⁻ 12 q6 ∷
   rw 13 q7 ∷
   rw 4 q47 ∷
   rw 5 q48 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "个") ∷
   rw 7 q49 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "个") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q50 ∷
   rw⁻ 11 q51 ∷
   rw 12 q52 ∷
   re 9 5 (ℓ "中") ∷
   rw 10 q47 ∷
   rw⁻ 11 q26 ∷
   rw 4 q1 ∷
   rw 5 q53 ∷
   rw 6 q19 ∷
   rw 7 q54 ∷
   rw 8 q2 ∷
   rw 9 q54 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   rw 11 q41 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q53 ∷
   rw 12 q42 ∷
   rw 5 q55 ∷
   re 5 8 (ℓ "乥") ∷
   re 4 3 (ℓ "乤") ∷
   rw 5 q57 ∷
   rw 6 q28 ∷
   re 2 1 (ℓ "並乥並") ∷
   re 3 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 2 q53 ∷
   rw 3 q19 ∷
   rw 4 q58 ∷
   rw 5 q2 ∷
   rw 6 q58 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q10 ∷
   rw 8 q38 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q53 ∷
   rw 9 q59 ∷
   rw 10 q46 ∷
   rw 1 q3 ∷
   rw 2 q60 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "丰") ∷
   rw 4 q61 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "丰") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 7 q3 ∷
   rw⁻ 8 q6 ∷
   rw 1 q1 ∷
   rw 2 q9 ∷
   rw 3 q19 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw 4 q10 ∷
   rw 5 q54 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "乀") ∷
   rw 5 q2 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw 6 q10 ∷
   rw 7 q54 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "乀") ∷
   rw 7 q41 ∷
   rw 8 q9 ∷
   rw 9 q42 ∷
   rw 2 q62 ∷
   re 2 8 (ℓ "乨") ∷
   re 1 3 (ℓ "乧") ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "並乥並") ∷
   re 5 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 4 q53 ∷
   rw 5 q19 ∷
   rw 6 q58 ∷
   rw 7 q2 ∷
   rw 8 q58 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q10 ∷
   rw 10 q38 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q53 ∷
   rw 11 q59 ∷
   rw 12 q46 ∷
   rw 3 q3 ∷
   rw 4 q60 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "丰") ∷
   rw 6 q61 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "丰") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw 9 q3 ∷
   rw⁻ 10 q6 ∷
   rw 3 q1 ∷
   rw 4 q9 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw 6 q10 ∷
   rw 7 q54 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "乀") ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏个乏") ∷
   rw 8 q10 ∷
   rw 9 q54 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "乀") ∷
   rw 9 q41 ∷
   rw 10 q9 ∷
   rw 11 q42 ∷
   rw 4 q62 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "举") ∷
   rw 5 q7 ∷
   re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q9 ∷
   rw 2 q19 ∷
   rw 3 q58 ∷
   rw 4 q2 ∷
   rw 5 q58 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q10 ∷
   rw 7 q38 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q9 ∷
   rw 8 q59 ∷
   rw 9 q46 ∷
   rw 0 q9 ∷
   rw 1 q19 ∷
   rw 2 q54 ∷
   rw 3 q2 ∷
   rw 4 q54 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q10 ∷
   rw 6 q41 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q9 ∷
   rw 7 q42 ∷
   rw 0 q63 ∷
   re 0 8 (ℓ "乨") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q10 ∷
   rw 2 q38 ∷
   rw 3 q10 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "並乨並") ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q9 ∷
   rw 4 q19 ∷
   rw 5 q58 ∷
   rw 6 q2 ∷
   rw 7 q58 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q10 ∷
   rw 9 q38 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q9 ∷
   rw 10 q59 ∷
   rw 11 q46 ∷
   rw 2 q9 ∷
   rw 3 q19 ∷
   rw 4 q54 ∷
   rw 5 q2 ∷
   rw 6 q54 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q10 ∷
   rw 8 q41 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q9 ∷
   rw 9 q42 ∷
   rw 2 q63 ∷
   re 2 8 (ℓ "乨") ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q10 ∷
   rw 4 q40 ∷
   rw 5 q10 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q46 ∷ []) Eq.refl
