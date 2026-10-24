{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D131 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 273 W
  q4 : Eqn
  q4 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = wE 10 W
  q6 : Eqn
  q6 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = wE 216 W
  q9 : Eqn
  q9 = wE 480 W
  q10 : Eqn
  q10 = wE 481 W
  q11 : Eqn
  q11 = wE 12 W
  q12 : Eqn
  q12 = wE 22 W
  q13 : Eqn
  q13 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = wE 23 W
  q15 : Eqn
  q15 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q16 : Eqn
  q16 = wE 14 W
  q17 : Eqn
  q17 = wE 477 W
  q18 : Eqn
  q18 = wE 478 W
  q19 : Eqn
  q19 = wE 479 W
  q20 : Eqn
  q20 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q21 : Eqn
  q21 = wE 50 W
  q22 : Eqn
  q22 = wE 343 W
  q23 : Eqn
  q23 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q24 : Eqn
  q24 = wE 49 W
  q25 : Eqn
  q25 = wE 51 W
  q26 : Eqn
  q26 = wE 20 W
  q27 : Eqn
  q27 = wE 364 W
  q28 : Eqn
  q28 = wE 369 W
  q29 : Eqn
  q29 = wE 157 W
  q30 : Eqn
  q30 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = wE 25 W
  q32 : Eqn
  q32 = wE 275 W
  q33 : Eqn
  q33 = wE 39 W
  q34 : Eqn
  q34 = wE 327 W
  q35 : Eqn
  q35 = wE 315 W
  q36 : Eqn
  q36 = wE 219 W
  q37 : Eqn
  q37 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q38 : Eqn
  q38 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q39 : Eqn
  q39 = wE 30 W
  q40 : Eqn
  q40 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q41 : Eqn
  q41 = wE 27 W
  q42 : Eqn
  q42 = wE 122 W
  q43 : Eqn
  q43 = wE 24 W
  q44 : Eqn
  q44 = wE 124 W
  q45 : Eqn
  q45 = wE 337 W
  q46 : Eqn
  q46 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q47 : Eqn
  q47 = wE 31 W

-- AXIOM LF @1203: 861 steps
lem-AXIOM-LF-at1203 : ⟪ (ℓ "丶丶乇丶乃丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠乔丠丠丠丈两丠丠丠丠丠丠乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乃丶丶丶且乇丶丶丶丶丶丶业乔") ⟫ʷ ≈ ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两乧丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽乧丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔") ⟫ʷ
lem-AXIOM-LF-at1203 = derive (ℓ "丶丶乇丶乃丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠乔丠丠丠丈两丠丠丠丠丠丠乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乃丶丶丶且乇丶丶丶丶丶丶业乔") (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两乧丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽乧丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔")
  (rw 80 q1 ∷
   re 79 1 (ℓ "乏乇乏") ∷
   rw⁻ 81 q2 ∷
   rw 80 q3 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (ℓ "乑") ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q3 ∷
   rw⁻ 70 q6 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q7 ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   rw 61 q8 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q8 ∷
   rw 57 q8 ∷
   rw 56 q9 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   rw 51 q8 ∷
   rw 50 q8 ∷
   rw 49 q8 ∷
   rw 48 q8 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q8 ∷
   rw 43 q8 ∷
   rw 42 q8 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw 36 q8 ∷
   rw 35 q8 ∷
   rw 34 q8 ∷
   rw 33 q7 ∷
   rw 32 q8 ∷
   rw 31 q8 ∷
   rw 30 q8 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q8 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (ℓ "乑") ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q8 ∷
   rw 13 q8 ∷
   rw 12 q8 ∷
   rw 11 q8 ∷
   rw 10 q8 ∷
   rw 9 q10 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q8 ∷
   rw 5 q8 ∷
   rw 4 q7 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 81 q11 ∷
   re 80 1 (ℓ "乏丼临丼乏") ∷
   rw 83 q12 ∷
   rw 82 q13 ∷
   rw 80 q14 ∷
   re 81 5 (ℓ "乑") ∷
   rw⁻ 79 q15 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q16 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q16 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q16 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q16 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 76 q16 ∷
   re 73 1 (ℓ "丼丠丼") ∷
   rw 75 q16 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 74 q16 ∷
   rw 71 q17 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q16 ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 71 q16 ∷
   re 68 1 (ℓ "丼丠丼") ∷
   rw 70 q16 ∷
   rw 67 q18 ∷
   rw 66 q11 ∷
   re 67 3 (ℓ "丧") ∷
   rw 65 q11 ∷
   re 66 3 (ℓ "丧") ∷
   rw 64 q11 ∷
   re 65 3 (ℓ "丧") ∷
   rw 63 q11 ∷
   re 64 3 (ℓ "丧") ∷
   rw 62 q11 ∷
   re 63 3 (ℓ "丧") ∷
   rw 61 q11 ∷
   re 62 3 (ℓ "丧") ∷
   rw 60 q11 ∷
   re 61 3 (ℓ "丧") ∷
   rw 59 q11 ∷
   re 60 3 (ℓ "丧") ∷
   rw 58 q11 ∷
   re 59 3 (ℓ "丧") ∷
   rw 57 q11 ∷
   re 58 3 (ℓ "乄") ∷
   rw 56 q19 ∷
   rw 55 q19 ∷
   rw 54 q19 ∷
   rw 53 q19 ∷
   rw 52 q11 ∷
   re 53 3 (ℓ "丧") ∷
   rw 51 q11 ∷
   re 52 3 (ℓ "丧") ∷
   rw 50 q11 ∷
   re 51 3 (ℓ "丧") ∷
   rw 49 q11 ∷
   re 50 3 (ℓ "丧") ∷
   rw 48 q11 ∷
   re 49 3 (ℓ "丧") ∷
   rw 47 q11 ∷
   re 48 3 (ℓ "丧") ∷
   rw 46 q11 ∷
   re 47 3 (ℓ "丧") ∷
   rw 45 q11 ∷
   re 46 3 (ℓ "丧") ∷
   rw 44 q11 ∷
   re 45 3 (ℓ "丧") ∷
   rw 43 q11 ∷
   re 44 3 (ℓ "丧") ∷
   rw 42 q11 ∷
   re 43 3 (ℓ "丧") ∷
   rw 41 q11 ∷
   re 42 3 (ℓ "丧") ∷
   rw 40 q11 ∷
   re 41 3 (ℓ "丧") ∷
   rw 39 q11 ∷
   re 40 3 (ℓ "丧") ∷
   rw 38 q11 ∷
   re 39 3 (ℓ "丧") ∷
   rw 37 q11 ∷
   re 38 3 (ℓ "丧") ∷
   rw 36 q11 ∷
   re 37 3 (ℓ "丧") ∷
   rw 35 q11 ∷
   re 36 3 (ℓ "丧") ∷
   rw 34 q18 ∷
   rw 33 q11 ∷
   re 34 3 (ℓ "丧") ∷
   rw 32 q11 ∷
   re 33 3 (ℓ "丧") ∷
   rw 31 q11 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q11 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q11 ∷
   re 30 3 (ℓ "丧") ∷
   rw 28 q11 ∷
   re 29 3 (ℓ "丧") ∷
   rw 27 q11 ∷
   re 28 3 (ℓ "乄") ∷
   rw 26 q19 ∷
   rw 25 q11 ∷
   re 26 3 (ℓ "丧") ∷
   rw 24 q11 ∷
   re 25 3 (ℓ "丧") ∷
   rw 23 q11 ∷
   re 24 3 (ℓ "丧") ∷
   re 22 1 (ℓ "乏丼临丼乏") ∷
   rw 25 q12 ∷
   rw 24 q13 ∷
   rw 22 q14 ∷
   re 23 5 (ℓ "乑") ∷
   rw 21 q11 ∷
   re 22 3 (ℓ "丧") ∷
   rw 20 q11 ∷
   re 21 3 (ℓ "乄") ∷
   rw 19 q11 ∷
   re 20 3 (ℓ "丧") ∷
   rw 18 q11 ∷
   re 19 3 (ℓ "丧") ∷
   rw 17 q18 ∷
   rw 16 q11 ∷
   re 17 3 (ℓ "丧") ∷
   rw 15 q11 ∷
   re 16 3 (ℓ "丧") ∷
   rw 14 q11 ∷
   re 15 3 (ℓ "丧") ∷
   rw 13 q11 ∷
   re 14 3 (ℓ "丧") ∷
   rw 12 q11 ∷
   re 13 3 (ℓ "丧") ∷
   rw 11 q11 ∷
   re 12 3 (ℓ "丧") ∷
   rw 10 q19 ∷
   rw 9 q11 ∷
   re 10 3 (ℓ "乄") ∷
   rw 8 q11 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "丧") ∷
   rw 6 q11 ∷
   re 7 3 (ℓ "丧") ∷
   rw 5 q18 ∷
   re 4 1 (ℓ "丼丠丼") ∷
   rw 6 q16 ∷
   re 3 1 (ℓ "丼临丼") ∷
   rw 5 q16 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 4 q16 ∷
   re 1 1 (ℓ "丼丠丼") ∷
   rw 3 q16 ∷
   rw 2 q20 ∷
   rw 3 q11 ∷
   re 1 3 (ℓ "丧") ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "丧") ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "乄") ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "丧") ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "乄") ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "乄") ∷
   rw 7 q21 ∷
   re 9 1 (ℓ "丼临丼") ∷
   rw 8 q16 ∷
   rw 9 q22 ∷
   re 11 1 (ℓ "丼临丼") ∷
   rw 10 q16 ∷
   rw 11 q22 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q16 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q16 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q16 ∷
   re 16 1 (ℓ "丼临丼") ∷
   rw 15 q16 ∷
   rw 16 q22 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q16 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q16 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q16 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q16 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q16 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q16 ∷
   rw 23 q21 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q16 ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q16 ∷
   re 27 1 (ℓ "丼临丼") ∷
   rw 26 q16 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q16 ∷
   re 29 1 (ℓ "丼临丼") ∷
   rw 28 q16 ∷
   re 30 1 (ℓ "丼临丼") ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q23 ∷
   rw 31 q24 ∷
   rw 32 q21 ∷
   rw 33 q25 ∷
   rw 34 q21 ∷
   rw 35 q26 ∷
   rw 36 q23 ∷
   rw 37 q27 ∷
   rw 30 q28 ∷
   re 30 8 (ℓ "乨") ∷
   rw 33 q11 ∷
   re 31 3 (ℓ "丧") ∷
   rw 34 q11 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q11 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q11 ∷
   re 34 3 (ℓ "乄") ∷
   rw 37 q11 ∷
   re 35 3 (ℓ "丧") ∷
   rw 38 q11 ∷
   re 36 3 (ℓ "丧") ∷
   rw 37 q29 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q12 ∷
   rw⁻ 40 q30 ∷
   rw 41 q14 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q12 ∷
   rw⁻ 41 q30 ∷
   rw 42 q14 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q12 ∷
   rw⁻ 42 q30 ∷
   rw 43 q14 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q12 ∷
   rw⁻ 43 q30 ∷
   rw 44 q14 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q12 ∷
   rw⁻ 44 q30 ∷
   rw 45 q14 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q12 ∷
   rw⁻ 45 q30 ∷
   rw 46 q14 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q12 ∷
   rw⁻ 46 q13 ∷
   rw 47 q14 ∷
   re 44 5 (ℓ "乑") ∷
   rw 45 q15 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q12 ∷
   rw⁻ 48 q30 ∷
   rw 49 q14 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q12 ∷
   rw⁻ 49 q30 ∷
   rw 50 q14 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q12 ∷
   rw⁻ 50 q30 ∷
   rw 51 q14 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q12 ∷
   rw⁻ 51 q30 ∷
   rw 52 q14 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q12 ∷
   rw⁻ 52 q30 ∷
   rw 53 q14 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q12 ∷
   rw⁻ 53 q30 ∷
   rw 54 q14 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q12 ∷
   rw⁻ 54 q30 ∷
   rw 55 q14 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q12 ∷
   rw⁻ 55 q30 ∷
   rw 56 q14 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q12 ∷
   rw⁻ 56 q30 ∷
   rw 57 q14 ∷
   re 54 5 (ℓ "中") ∷
   rw 55 q29 ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q12 ∷
   rw⁻ 58 q30 ∷
   rw 59 q14 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q12 ∷
   rw⁻ 59 q30 ∷
   rw 60 q14 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q12 ∷
   rw⁻ 60 q30 ∷
   rw 61 q14 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q12 ∷
   rw⁻ 61 q13 ∷
   rw 62 q14 ∷
   re 59 5 (ℓ "乑") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q12 ∷
   rw⁻ 62 q30 ∷
   rw 63 q14 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q12 ∷
   rw⁻ 63 q30 ∷
   rw 64 q14 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   rw 64 q21 ∷
   rw 65 q25 ∷
   rw 66 q21 ∷
   rw 67 q26 ∷
   rw 68 q23 ∷
   rw 69 q27 ∷
   rw 62 q28 ∷
   re 62 8 (ℓ "乨") ∷
   rw 65 q11 ∷
   re 63 3 (ℓ "丧") ∷
   rw 66 q11 ∷
   re 64 3 (ℓ "丧") ∷
   rw 67 q11 ∷
   re 65 3 (ℓ "乄") ∷
   rw 68 q11 ∷
   re 66 3 (ℓ "丧") ∷
   rw 69 q11 ∷
   re 67 3 (ℓ "乄") ∷
   rw 70 q11 ∷
   re 68 3 (ℓ "乄") ∷
   rw 69 q29 ∷
   re 71 1 (ℓ "乏丼临丼乏") ∷
   rw 70 q12 ∷
   rw⁻ 72 q13 ∷
   rw 73 q14 ∷
   re 70 5 (ℓ "乑") ∷
   rw 71 q15 ∷
   re 73 1 (ℓ "乏丼临丼乏") ∷
   rw 72 q12 ∷
   rw⁻ 74 q13 ∷
   rw 75 q14 ∷
   re 72 5 (ℓ "乑") ∷
   rw 73 q15 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q12 ∷
   rw⁻ 76 q30 ∷
   rw 77 q14 ∷
   re 74 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q12 ∷
   rw⁻ 77 q30 ∷
   rw 78 q14 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q12 ∷
   rw⁻ 78 q30 ∷
   rw 79 q14 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼临丼乏") ∷
   rw 77 q12 ∷
   rw⁻ 79 q13 ∷
   rw 80 q14 ∷
   re 77 5 (ℓ "乑") ∷
   rw 78 q15 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q12 ∷
   rw⁻ 81 q30 ∷
   rw 82 q14 ∷
   re 79 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q12 ∷
   rw⁻ 82 q30 ∷
   rw 83 q14 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q12 ∷
   rw⁻ 83 q30 ∷
   rw 84 q14 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q12 ∷
   rw⁻ 84 q30 ∷
   rw 85 q14 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q12 ∷
   rw⁻ 85 q30 ∷
   rw 86 q14 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q12 ∷
   rw⁻ 86 q30 ∷
   rw 87 q14 ∷
   re 84 5 (ℓ "中") ∷
   rw 85 q29 ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q12 ∷
   rw⁻ 88 q30 ∷
   rw 89 q14 ∷
   re 86 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q12 ∷
   rw⁻ 89 q30 ∷
   rw 90 q14 ∷
   re 87 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丼临丼乏") ∷
   rw 88 q12 ∷
   rw⁻ 90 q13 ∷
   rw 91 q14 ∷
   re 88 5 (ℓ "乑") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q12 ∷
   rw⁻ 91 q30 ∷
   rw 92 q14 ∷
   re 89 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 90 q12 ∷
   rw⁻ 92 q13 ∷
   rw 93 q14 ∷
   re 90 5 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丼临丼乏") ∷
   rw 91 q12 ∷
   rw⁻ 93 q13 ∷
   rw 94 q14 ∷
   re 91 5 (ℓ "乑") ∷
   rw 92 q16 ∷
   rw 0 q31 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q32 ∷
   rw 6 q33 ∷
   rw 7 q34 ∷
   rw 8 q35 ∷
   rw 9 q34 ∷
   rw 10 q35 ∷
   rw 11 q36 ∷
   rw 12 q36 ∷
   rw 13 q36 ∷
   rw 14 q34 ∷
   rw 15 q35 ∷
   rw 16 q36 ∷
   rw 17 q36 ∷
   rw 18 q36 ∷
   rw 19 q36 ∷
   rw 20 q36 ∷
   rw 21 q36 ∷
   rw 22 q33 ∷
   rw 23 q36 ∷
   rw 24 q36 ∷
   rw 25 q34 ∷
   rw 26 q36 ∷
   rw 27 q34 ∷
   rw 28 q34 ∷
   re 30 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 29 q37 ∷
   rw 30 q38 ∷
   rw 31 q39 ∷
   rw 32 q40 ∷
   rw 33 q39 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q2 ∷
   rw 35 q41 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q37 ∷
   rw 36 q42 ∷
   rw 29 q1 ∷
   rw 30 q37 ∷
   rw 31 q38 ∷
   rw 32 q43 ∷
   rw 33 q40 ∷
   rw 34 q43 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q2 ∷
   rw 36 q31 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "丽") ∷
   rw 36 q37 ∷
   rw 37 q44 ∷
   rw 30 q45 ∷
   re 30 8 (ℓ "乨") ∷
   re 29 3 (ℓ "乧") ∷
   rw 30 q31 ∷
   rw 31 q31 ∷
   rw 32 q31 ∷
   rw 33 q32 ∷
   rw 34 q31 ∷
   rw 35 q31 ∷
   rw 36 q46 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q2 ∷
   rw 38 q31 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q2 ∷
   rw 39 q31 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q2 ∷
   rw 40 q31 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q2 ∷
   rw 41 q31 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   rw 42 q31 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q2 ∷
   rw 43 q31 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 43 q2 ∷
   rw 44 q32 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "乔") ∷
   rw 44 q4 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q2 ∷
   rw 46 q31 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   rw 47 q31 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   rw 48 q31 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   rw 49 q31 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   rw 50 q31 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q2 ∷
   rw 51 q31 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q2 ∷
   rw 52 q31 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q2 ∷
   rw 53 q31 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q2 ∷
   rw 54 q31 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "丽") ∷
   rw 54 q46 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 55 q2 ∷
   rw 56 q31 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 56 q2 ∷
   rw 57 q31 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q2 ∷
   rw 58 q31 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 58 q2 ∷
   rw 59 q32 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "乔") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q2 ∷
   rw 60 q31 ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q2 ∷
   rw 61 q31 ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "丽") ∷
   re 62 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 61 q37 ∷
   rw 62 q38 ∷
   rw 63 q39 ∷
   rw 64 q40 ∷
   rw 65 q39 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q2 ∷
   rw 67 q41 ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q37 ∷
   rw 68 q42 ∷
   rw 61 q1 ∷
   rw 62 q37 ∷
   rw 63 q38 ∷
   rw 64 q43 ∷
   rw 65 q40 ∷
   rw 66 q43 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 67 q2 ∷
   rw 68 q31 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "丽") ∷
   rw 68 q37 ∷
   rw 69 q44 ∷
   rw 62 q45 ∷
   re 62 8 (ℓ "乨") ∷
   re 61 3 (ℓ "乧") ∷
   rw 62 q31 ∷
   rw 63 q31 ∷
   rw 64 q32 ∷
   rw 65 q31 ∷
   rw 66 q32 ∷
   rw 67 q32 ∷
   rw 68 q46 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 69 q2 ∷
   rw 70 q32 ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "乔") ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q2 ∷
   rw 72 q32 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乔") ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 73 q2 ∷
   rw 74 q31 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q2 ∷
   rw 75 q31 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q2 ∷
   rw 76 q31 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw 76 q2 ∷
   rw 77 q32 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "乔") ∷
   rw 77 q4 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 78 q2 ∷
   rw 79 q31 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "丽") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q2 ∷
   rw 80 q31 ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q2 ∷
   rw 81 q31 ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q2 ∷
   rw 82 q31 ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "丽") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q2 ∷
   rw 83 q31 ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q2 ∷
   rw 84 q31 ∷
   rw 85 q2 ∷
   re 83 3 (ℓ "丽") ∷
   rw 84 q46 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 85 q2 ∷
   rw 86 q31 ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 86 q2 ∷
   rw 87 q31 ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "丽") ∷
   re 88 1 (ℓ "乏乄乏") ∷
   rw 87 q2 ∷
   rw 88 q32 ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乔") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 88 q2 ∷
   rw 89 q31 ∷
   rw 90 q2 ∷
   re 88 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 89 q2 ∷
   rw 90 q32 ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乔") ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 90 q2 ∷
   rw 91 q32 ∷
   rw 92 q2 ∷
   re 90 3 (ℓ "乔") ∷
   rw 91 q47 ∷ []) Eq.refl
