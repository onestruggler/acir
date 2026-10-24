{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D027 (W : Ws) where

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
  q2 = wE 273 W
  q3 : Eqn
  q3 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 10 W
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = wE 216 W
  q9 : Eqn
  q9 = wE 480 W
  q10 : Eqn
  q10 = wE 481 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 476 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = wE 464 W
  q15 : Eqn
  q15 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q18 : Eqn
  q18 = wE 12 W
  q19 : Eqn
  q19 = wE 22 W
  q20 : Eqn
  q20 = wE 23 W
  q21 : Eqn
  q21 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 477 W
  q24 : Eqn
  q24 = wE 478 W
  q25 : Eqn
  q25 = wE 479 W
  q26 : Eqn
  q26 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q27 : Eqn
  q27 = wE 50 W
  q28 : Eqn
  q28 = wE 343 W
  q29 : Eqn
  q29 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q30 : Eqn
  q30 = wE 49 W
  q31 : Eqn
  q31 = wE 51 W
  q32 : Eqn
  q32 = wE 20 W
  q33 : Eqn
  q33 = wE 364 W
  q34 : Eqn
  q34 = wE 369 W
  q35 : Eqn
  q35 = wE 157 W

-- AXIOM LF @1302 part0: 500 steps
lem-AXIOM-LF-at1302-part0 : ⟪ (ℓ "丽丽乔丽乐丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠乇丠丠丠丈两丠丠丠丠丠丠乐丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乐丽丽丽业乔丽丽丽丽丽丽且乇") ⟫ʷ ≈ ⟪ (ℓ "並乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中乏丼丠乏丼乏中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏並") ⟫ʷ
lem-AXIOM-LF-at1302-part0 = derive (ℓ "丽丽乔丽乐丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠乇丠丠丠丈两丠丠丠丠丠丠乐丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈丈两丠丠丠丠丠丠丠丠丠乐丽丽丽业乔丽丽丽丽丽丽且乇") (ℓ "並乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中乏丼丠乏丼乏中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏並")
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q3 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw⁻ 79 q4 ∷
   rw 78 q5 ∷
   rw⁻ 77 q4 ∷
   re 78 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw⁻ 76 q4 ∷
   re 77 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw⁻ 77 q4 ∷
   rw 76 q5 ∷
   rw⁻ 75 q4 ∷
   re 76 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw⁻ 76 q4 ∷
   rw 75 q5 ∷
   rw⁻ 74 q4 ∷
   re 75 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw⁻ 75 q4 ∷
   rw 74 q5 ∷
   rw⁻ 73 q4 ∷
   re 74 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw⁻ 74 q4 ∷
   rw 73 q5 ∷
   rw⁻ 72 q4 ∷
   re 73 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw⁻ 73 q4 ∷
   rw 72 q2 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (ℓ "乑") ∷
   rw⁻ 70 q6 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw⁻ 71 q4 ∷
   rw 70 q5 ∷
   rw⁻ 69 q4 ∷
   re 70 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw⁻ 69 q4 ∷
   rw 68 q5 ∷
   rw⁻ 67 q4 ∷
   re 68 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏乃乏") ∷
   rw⁻ 68 q4 ∷
   rw 67 q7 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (ℓ "乓") ∷
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
   re 33 1 (ℓ "乏乃乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乓") ∷
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
   rw 21 q2 ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   re 16 1 (ℓ "乏乃乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q7 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "乓") ∷
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
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q4 ∷
   rw 5 q7 ∷
   rw⁻ 4 q4 ∷
   re 5 3 (ℓ "乓") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q4 ∷
   rw 4 q5 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw⁻ 4 q4 ∷
   rw 3 q2 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (ℓ "乑") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q4 ∷
   rw 2 q5 ∷
   rw⁻ 1 q4 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (ℓ "中") ∷
   rw 81 q11 ∷
   rw 80 q11 ∷
   re 81 3 (ℓ "乑") ∷
   rw 79 q12 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q13 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q13 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q13 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q13 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q13 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q13 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 74 q13 ∷
   rw 71 q14 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q13 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q13 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q13 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 69 q13 ∷
   rw 66 q15 ∷
   rw 65 q15 ∷
   rw 64 q15 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q15 ∷
   rw 60 q15 ∷
   rw 59 q15 ∷
   rw 58 q15 ∷
   rw 57 q16 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q15 ∷
   rw 37 q15 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 36 q13 ∷
   rw 33 q15 ∷
   rw 32 q15 ∷
   rw 31 q15 ∷
   rw 30 q15 ∷
   rw 29 q15 ∷
   rw 28 q15 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q15 ∷
   rw 24 q15 ∷
   rw 23 q15 ∷
   rw 22 q11 ∷
   re 23 3 (ℓ "乑") ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q15 ∷
   rw 18 q15 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 19 q13 ∷
   rw 16 q15 ∷
   rw 15 q15 ∷
   rw 14 q15 ∷
   rw 13 q15 ∷
   rw 12 q15 ∷
   rw 11 q15 ∷
   rw 10 q17 ∷
   rw 9 q16 ∷
   rw 8 q15 ∷
   rw 7 q15 ∷
   rw 6 q15 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 7 q13 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q13 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q13 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q13 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q13 ∷
   rw 82 q18 ∷
   re 81 1 (ℓ "乏丼临丼乏") ∷
   rw 84 q19 ∷
   rw 83 q16 ∷
   rw 81 q20 ∷
   re 82 5 (ℓ "乑") ∷
   rw⁻ 80 q21 ∷
   re 79 1 (ℓ "丼丠丼") ∷
   rw 81 q22 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q22 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q22 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q22 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q22 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 76 q22 ∷
   re 73 1 (ℓ "丼临丼") ∷
   rw 75 q22 ∷
   rw 72 q23 ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 73 q22 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q22 ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 71 q22 ∷
   rw 68 q24 ∷
   rw 67 q18 ∷
   re 68 3 (ℓ "丧") ∷
   rw 66 q18 ∷
   re 67 3 (ℓ "丧") ∷
   rw 65 q18 ∷
   re 66 3 (ℓ "丧") ∷
   rw 64 q18 ∷
   re 65 3 (ℓ "丧") ∷
   rw 63 q18 ∷
   re 64 3 (ℓ "丧") ∷
   rw 62 q18 ∷
   re 63 3 (ℓ "丧") ∷
   rw 61 q18 ∷
   re 62 3 (ℓ "丧") ∷
   rw 60 q18 ∷
   re 61 3 (ℓ "丧") ∷
   rw 59 q18 ∷
   re 60 3 (ℓ "丧") ∷
   rw 58 q18 ∷
   re 59 3 (ℓ "乄") ∷
   rw 57 q25 ∷
   rw 56 q25 ∷
   rw 55 q25 ∷
   rw 54 q25 ∷
   rw 53 q18 ∷
   re 54 3 (ℓ "丧") ∷
   rw 52 q18 ∷
   re 53 3 (ℓ "丧") ∷
   rw 51 q18 ∷
   re 52 3 (ℓ "丧") ∷
   rw 50 q18 ∷
   re 51 3 (ℓ "丧") ∷
   rw 49 q18 ∷
   re 50 3 (ℓ "丧") ∷
   rw 48 q18 ∷
   re 49 3 (ℓ "丧") ∷
   rw 47 q18 ∷
   re 48 3 (ℓ "丧") ∷
   rw 46 q18 ∷
   re 47 3 (ℓ "丧") ∷
   rw 45 q18 ∷
   re 46 3 (ℓ "丧") ∷
   rw 44 q18 ∷
   re 45 3 (ℓ "丧") ∷
   rw 43 q18 ∷
   re 44 3 (ℓ "丧") ∷
   rw 42 q18 ∷
   re 43 3 (ℓ "丧") ∷
   rw 41 q18 ∷
   re 42 3 (ℓ "丧") ∷
   rw 40 q18 ∷
   re 41 3 (ℓ "丧") ∷
   rw 39 q18 ∷
   re 40 3 (ℓ "丧") ∷
   rw 38 q18 ∷
   re 39 3 (ℓ "丧") ∷
   rw 37 q18 ∷
   re 38 3 (ℓ "丧") ∷
   rw 36 q18 ∷
   re 37 3 (ℓ "丧") ∷
   rw 35 q24 ∷
   rw 34 q18 ∷
   re 35 3 (ℓ "丧") ∷
   rw 33 q18 ∷
   re 34 3 (ℓ "丧") ∷
   rw 32 q18 ∷
   re 33 3 (ℓ "丧") ∷
   rw 31 q18 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q18 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q18 ∷
   re 30 3 (ℓ "丧") ∷
   rw 28 q18 ∷
   re 29 3 (ℓ "乄") ∷
   rw 27 q25 ∷
   rw 26 q18 ∷
   re 27 3 (ℓ "丧") ∷
   rw 25 q18 ∷
   re 26 3 (ℓ "丧") ∷
   rw 24 q18 ∷
   re 25 3 (ℓ "丧") ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 26 q19 ∷
   rw 25 q16 ∷
   rw 23 q20 ∷
   re 24 5 (ℓ "乑") ∷
   rw 22 q18 ∷
   re 23 3 (ℓ "丧") ∷
   rw 21 q18 ∷
   re 22 3 (ℓ "乄") ∷
   rw 20 q18 ∷
   re 21 3 (ℓ "丧") ∷
   rw 19 q18 ∷
   re 20 3 (ℓ "丧") ∷
   rw 18 q24 ∷
   rw 17 q18 ∷
   re 18 3 (ℓ "丧") ∷
   rw 16 q18 ∷
   re 17 3 (ℓ "丧") ∷
   rw 15 q18 ∷
   re 16 3 (ℓ "丧") ∷
   rw 14 q18 ∷
   re 15 3 (ℓ "丧") ∷
   rw 13 q18 ∷
   re 14 3 (ℓ "丧") ∷
   rw 12 q18 ∷
   re 13 3 (ℓ "丧") ∷
   rw 11 q25 ∷
   rw 10 q18 ∷
   re 11 3 (ℓ "乄") ∷
   rw 9 q18 ∷
   re 10 3 (ℓ "丧") ∷
   rw 8 q18 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q18 ∷
   re 8 3 (ℓ "丧") ∷
   rw 6 q24 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q22 ∷
   re 4 1 (ℓ "丼临丼") ∷
   rw 6 q22 ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 5 q22 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 4 q22 ∷
   rw 3 q26 ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丧") ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "丧") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "乄") ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "丧") ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "乄") ∷
   rw 9 q18 ∷
   re 7 3 (ℓ "乄") ∷
   rw 8 q27 ∷
   re 10 1 (ℓ "丼临丼") ∷
   rw 9 q22 ∷
   rw 10 q28 ∷
   re 12 1 (ℓ "丼临丼") ∷
   rw 11 q22 ∷
   rw 12 q28 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q22 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q22 ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 15 q22 ∷
   re 17 1 (ℓ "丼临丼") ∷
   rw 16 q22 ∷
   rw 17 q28 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q22 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q22 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q22 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q22 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q22 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q22 ∷
   rw 24 q27 ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q22 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q22 ∷
   re 28 1 (ℓ "丼临丼") ∷
   rw 27 q22 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q22 ∷
   re 30 1 (ℓ "丼临丼") ∷
   rw 29 q22 ∷
   re 31 1 (ℓ "丼临丼") ∷
   rw 30 q22 ∷
   re 32 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 31 q29 ∷
   rw 32 q30 ∷
   rw 33 q27 ∷
   rw 34 q31 ∷
   rw 35 q27 ∷
   rw 36 q32 ∷
   rw 37 q29 ∷
   rw 38 q33 ∷
   rw 31 q34 ∷
   re 31 8 (ℓ "乨") ∷
   rw 34 q18 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q18 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q18 ∷
   re 34 3 (ℓ "丧") ∷
   rw 37 q18 ∷
   re 35 3 (ℓ "乄") ∷
   rw 38 q18 ∷
   re 36 3 (ℓ "丧") ∷
   rw 39 q18 ∷
   re 37 3 (ℓ "丧") ∷
   rw 38 q35 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q19 ∷
   rw⁻ 41 q15 ∷
   rw 42 q20 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q19 ∷
   rw⁻ 42 q15 ∷
   rw 43 q20 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q19 ∷
   rw⁻ 43 q15 ∷ []) Eq.refl
