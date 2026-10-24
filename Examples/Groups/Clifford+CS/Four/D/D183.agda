{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D183 (W : Ws) where

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
  q2 = wE 378 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 372 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 25 W
  q7 : Eqn
  q7 = wE 275 W
  q8 : Eqn
  q8 = wE 39 W
  q9 : Eqn
  q9 = wE 327 W
  q10 : Eqn
  q10 = wE 315 W
  q11 : Eqn
  q11 = wE 219 W
  q12 : Eqn
  q12 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q13 : Eqn
  q13 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 122 W
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 124 W
  q21 : Eqn
  q21 = wE 334 W
  q22 : Eqn
  q22 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = wE 20 W
  q26 : Eqn
  q26 = wE 359 W
  q27 : Eqn
  q27 = wE 22 W
  q28 : Eqn
  q28 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q29 : Eqn
  q29 = wE 23 W
  q30 : Eqn
  q30 = wE 12 W
  q31 : Eqn
  q31 = eqn (ℓ "丈丼") (ℓ "丼丈") (low₁-comm (S) (Swap))
  q32 : Eqn
  q32 = wE 345 W
  q33 : Eqn
  q33 = wE 49 W
  q34 : Eqn
  q34 = wE 14 W
  q35 : Eqn
  q35 = wE 51 W
  q36 : Eqn
  q36 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q37 : Eqn
  q37 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q38 : Eqn
  q38 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q39 : Eqn
  q39 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q40 : Eqn
  q40 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q41 : Eqn
  q41 = wE 196 W
  q42 : Eqn
  q42 = wE 114 W
  q43 : Eqn
  q43 = wE 18 W
  q44 : Eqn
  q44 = wE 355 W
  q45 : Eqn
  q45 = wE 343 W

-- AXIOM LF @2301 part2: 477 steps
lem-AXIOM-LF-at2301-part2 : ⟪ (ℓ "丼並中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乏乄乏乏乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑乏並丼") ⟫ʷ ≈ ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为") ⟫ʷ
lem-AXIOM-LF-at2301-part2 = derive (ℓ "丼並中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乏乄乏乏乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑乏並丼") (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫乡义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶乡义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为")
  (re 68 3 (ℓ "乑") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q2 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q3 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 73 q3 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q3 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q3 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 77 q3 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 78 q3 ∷
   rw 79 q4 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q3 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q3 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q3 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q3 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 84 q3 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 85 q3 ∷
   rw 86 q2 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 87 q3 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 88 q3 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 89 q3 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 90 q3 ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 91 q3 ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw 92 q3 ∷
   rw 93 q3 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 3 q5 ∷
   rw 4 q7 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "乔") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 5 q5 ∷
   rw 6 q7 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乔") ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 6 q5 ∷
   rw 7 q7 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "乔") ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q5 ∷
   rw 8 q8 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q9 ∷
   rw 9 q10 ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q5 ∷
   rw 24 q8 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   rw 26 q9 ∷
   rw 27 q11 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   re 31 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 30 q12 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q15 ∷
   rw 34 q14 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q12 ∷
   rw 37 q17 ∷
   rw 30 q18 ∷
   rw 31 q12 ∷
   rw 32 q13 ∷
   rw 33 q19 ∷
   rw 34 q15 ∷
   rw 35 q19 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   rw 37 q6 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "丽") ∷
   rw 37 q12 ∷
   rw 38 q20 ∷
   rw 31 q21 ∷
   re 31 8 (ℓ "乥") ∷
   re 30 3 (ℓ "乤") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw 33 q5 ∷
   re 31 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 32 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 34 q5 ∷
   rw 35 q7 ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "乔") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   rw 36 q6 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   rw 37 q6 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "丽") ∷
   rw 37 q22 ∷
   rw 38 q6 ∷
   rw 39 q6 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q7 ∷
   rw 45 q23 ∷
   rw 46 q6 ∷
   rw 47 q6 ∷
   rw 48 q6 ∷
   rw 49 q6 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   rw 52 q6 ∷
   rw 53 q6 ∷
   rw 54 q6 ∷
   rw 55 q22 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q6 ∷
   rw 61 q6 ∷
   re 63 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 62 q12 ∷
   rw 63 q13 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q5 ∷
   rw 68 q16 ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q12 ∷
   rw 69 q17 ∷
   rw 62 q18 ∷
   rw 63 q12 ∷
   rw 64 q13 ∷
   rw 65 q19 ∷
   rw 66 q15 ∷
   rw 67 q19 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 68 q5 ∷
   rw 69 q6 ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "丽") ∷
   rw 69 q12 ∷
   rw 70 q20 ∷
   rw 63 q21 ∷
   re 63 8 (ℓ "乥") ∷
   re 62 3 (ℓ "乤") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   rw 64 q6 ∷
   rw 65 q5 ∷
   re 63 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 64 q5 ∷
   rw 65 q6 ∷
   rw 66 q5 ∷
   re 64 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw 65 q5 ∷
   rw 66 q7 ∷
   rw 67 q5 ∷
   re 65 3 (ℓ "乔") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw 68 q5 ∷
   re 66 3 (ℓ "丽") ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw 67 q5 ∷
   rw 68 q7 ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "乔") ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 68 q5 ∷
   rw 69 q7 ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "乔") ∷
   rw 69 q22 ∷
   rw 70 q7 ∷
   rw 71 q23 ∷
   rw 72 q7 ∷
   rw 73 q23 ∷
   rw 74 q6 ∷
   rw 75 q6 ∷
   rw 76 q6 ∷
   rw 77 q7 ∷
   rw 78 q23 ∷
   rw 79 q6 ∷
   rw 80 q6 ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   rw 83 q6 ∷
   rw 84 q6 ∷
   rw 85 q22 ∷
   rw 86 q6 ∷
   rw 87 q6 ∷
   rw 88 q7 ∷
   rw 89 q6 ∷
   rw 90 q7 ∷
   rw 91 q7 ∷
   rw 92 q24 ∷
   rw 0 q25 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 5 q26 ∷
   re 7 1 (ℓ "乏丼丳丼乏") ∷
   rw 6 q27 ∷
   rw⁻ 8 q28 ∷
   rw 9 q29 ∷
   re 6 5 (ℓ "乐") ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "丫") ∷
   rw⁻ 8 q31 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "丫") ∷
   rw⁻ 10 q31 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "丧") ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丧") ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "丧") ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "丫") ∷
   rw⁻ 15 q31 ∷
   rw 18 q30 ∷
   re 16 3 (ℓ "丧") ∷
   rw 19 q30 ∷
   re 17 3 (ℓ "丧") ∷
   rw 20 q30 ∷
   re 18 3 (ℓ "丧") ∷
   rw 21 q30 ∷
   re 19 3 (ℓ "丧") ∷
   rw 22 q30 ∷
   re 20 3 (ℓ "丧") ∷
   rw 23 q30 ∷
   re 21 3 (ℓ "丧") ∷
   re 23 1 (ℓ "乏丼丳丼乏") ∷
   rw 22 q27 ∷
   rw⁻ 24 q28 ∷
   rw 25 q29 ∷
   re 22 5 (ℓ "乐") ∷
   rw 25 q30 ∷
   re 23 3 (ℓ "丧") ∷
   rw 26 q30 ∷
   re 24 3 (ℓ "丧") ∷
   rw 27 q30 ∷
   re 25 3 (ℓ "丫") ∷
   rw 28 q30 ∷
   re 26 3 (ℓ "丧") ∷
   rw 29 q30 ∷
   re 27 3 (ℓ "丫") ∷
   rw 30 q30 ∷
   re 28 3 (ℓ "丫") ∷
   re 30 1 (ℓ "並乥並") ∷
   re 31 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 30 q12 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q15 ∷
   rw 34 q14 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q12 ∷
   rw 37 q17 ∷
   rw 38 q24 ∷
   rw 29 q32 ∷
   rw 30 q33 ∷
   re 32 1 (ℓ "丼丣丼") ∷
   rw 31 q34 ∷
   rw 32 q35 ∷
   re 34 1 (ℓ "丼丣丼") ∷
   rw 33 q34 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q27 ∷
   rw⁻ 36 q36 ∷
   rw 37 q29 ∷
   re 34 5 (ℓ "中") ∷
   rw 35 q32 ∷
   rw⁻ 36 q37 ∷
   rw 29 q1 ∷
   rw⁻ 30 q38 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw⁻ 32 q39 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q3 ∷
   rw⁻ 34 q39 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q3 ∷
   rw⁻ 36 q38 ∷
   rw⁻ 37 q40 ∷
   rw 30 q41 ∷
   re 30 8 (ℓ "习") ∷
   re 29 3 (ℓ "乡") ∷
   rw 30 q25 ∷
   rw 31 q25 ∷
   rw 32 q25 ∷
   rw 33 q26 ∷
   rw 34 q25 ∷
   rw 35 q25 ∷
   rw 36 q42 ∷
   rw 37 q43 ∷
   rw 38 q43 ∷
   rw 39 q43 ∷
   rw 40 q43 ∷
   rw 41 q43 ∷
   rw 42 q43 ∷
   rw 43 q44 ∷
   rw 44 q45 ∷
   rw 45 q43 ∷
   rw 46 q43 ∷
   rw 47 q43 ∷
   rw 48 q43 ∷
   rw 49 q43 ∷
   rw 50 q43 ∷
   rw 51 q43 ∷
   rw 52 q43 ∷
   rw 53 q43 ∷
   rw 54 q42 ∷
   rw 55 q43 ∷
   rw 56 q43 ∷
   rw 57 q43 ∷
   rw 58 q44 ∷
   rw 59 q43 ∷
   rw 60 q43 ∷
   re 62 1 (ℓ "並乥並") ∷
   re 63 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 62 q12 ∷
   rw 63 q13 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q5 ∷
   rw 68 q16 ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q12 ∷
   rw 69 q17 ∷
   rw 70 q24 ∷
   rw 61 q32 ∷
   rw 62 q33 ∷
   re 64 1 (ℓ "丼丣丼") ∷
   rw 63 q34 ∷
   rw 64 q35 ∷
   re 66 1 (ℓ "丼丣丼") ∷
   rw 65 q34 ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q27 ∷
   rw⁻ 68 q36 ∷
   rw 69 q29 ∷
   re 66 5 (ℓ "中") ∷
   rw 67 q32 ∷
   rw⁻ 68 q37 ∷
   rw 61 q1 ∷
   rw⁻ 62 q38 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q3 ∷
   rw⁻ 64 q39 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q3 ∷
   rw⁻ 66 q39 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 67 q3 ∷
   rw⁻ 68 q38 ∷
   rw⁻ 69 q40 ∷
   rw 62 q41 ∷
   re 62 8 (ℓ "习") ∷
   re 61 3 (ℓ "乡") ∷
   rw 62 q25 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q25 ∷
   rw 66 q26 ∷
   rw 67 q26 ∷
   rw 68 q42 ∷
   rw 69 q44 ∷
   rw 70 q45 ∷
   rw 71 q44 ∷
   rw 72 q45 ∷
   rw 73 q43 ∷
   rw 74 q43 ∷
   rw 75 q43 ∷
   rw 76 q44 ∷
   rw 77 q45 ∷
   rw 78 q43 ∷
   rw 79 q43 ∷
   rw 80 q43 ∷
   rw 81 q43 ∷
   rw 82 q43 ∷
   rw 83 q43 ∷
   rw 84 q42 ∷
   rw 85 q43 ∷
   rw 86 q43 ∷
   rw 87 q44 ∷
   rw 88 q43 ∷
   rw 89 q44 ∷
   rw 90 q44 ∷
   rw 91 q34 ∷ []) Eq.refl
