{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D028 (W : Ws) where

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
  q1 = wE 23 W
  q2 : Eqn
  q2 = wE 22 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q6 : Eqn
  q6 = wE 157 W
  q7 : Eqn
  q7 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q8 : Eqn
  q8 = wE 49 W
  q9 : Eqn
  q9 = wE 50 W
  q10 : Eqn
  q10 = wE 51 W
  q11 : Eqn
  q11 = wE 20 W
  q12 : Eqn
  q12 = wE 364 W
  q13 : Eqn
  q13 = wE 369 W
  q14 : Eqn
  q14 = wE 12 W
  q15 : Eqn
  q15 = wE 14 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q18 : Eqn
  q18 = wE 336 W
  q19 : Eqn
  q19 = wE 71 W
  q20 : Eqn
  q20 = wE 72 W
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q23 : Eqn
  q23 = wE 386 W
  q24 : Eqn
  q24 = wE 378 W
  q25 : Eqn
  q25 = wE 372 W
  q26 : Eqn
  q26 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q27 : Eqn
  q27 = wE 25 W
  q28 : Eqn
  q28 = wE 275 W
  q29 : Eqn
  q29 = wE 39 W
  q30 : Eqn
  q30 = wE 327 W
  q31 : Eqn
  q31 = wE 315 W
  q32 : Eqn
  q32 = wE 219 W
  q33 : Eqn
  q33 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q34 : Eqn
  q34 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q35 : Eqn
  q35 = wE 30 W
  q36 : Eqn
  q36 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q37 : Eqn
  q37 = wE 27 W
  q38 : Eqn
  q38 = wE 122 W
  q39 : Eqn
  q39 = wE 5 W
  q40 : Eqn
  q40 = wE 24 W
  q41 : Eqn
  q41 = wE 124 W
  q42 : Eqn
  q42 = wE 334 W

-- AXIOM LF @1302 part1: 500 steps
lem-AXIOM-LF-at1302-part1 : ⟪ (ℓ "並乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中乏丼丠乏丼乏中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏並") ⟫ʷ ≈ ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽乏丶乏並乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄並") ⟫ʷ
lem-AXIOM-LF-at1302-part1 = derive (ℓ "並乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中乏丼丠乏丼乏中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏並") (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两乤丽丽乏丶乏並乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄並")
  (rw 44 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q2 ∷
   rw⁻ 44 q3 ∷
   rw 45 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q1 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q2 ∷
   rw⁻ 46 q3 ∷
   rw 47 q1 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼临丼乏") ∷
   rw 45 q2 ∷
   rw⁻ 47 q4 ∷
   rw 48 q1 ∷
   re 45 5 (ℓ "乑") ∷
   rw 46 q5 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q2 ∷
   rw⁻ 49 q3 ∷
   rw 50 q1 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q2 ∷
   rw⁻ 50 q3 ∷
   rw 51 q1 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q2 ∷
   rw⁻ 51 q3 ∷
   rw 52 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   rw⁻ 52 q3 ∷
   rw 53 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q2 ∷
   rw⁻ 53 q3 ∷
   rw 54 q1 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q2 ∷
   rw⁻ 54 q3 ∷
   rw 55 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q2 ∷
   rw⁻ 55 q3 ∷
   rw 56 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q2 ∷
   rw⁻ 56 q3 ∷
   rw 57 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q2 ∷
   rw⁻ 57 q3 ∷
   rw 58 q1 ∷
   re 55 5 (ℓ "中") ∷
   rw 56 q6 ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q1 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q2 ∷
   rw⁻ 60 q3 ∷
   rw 61 q1 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q2 ∷
   rw⁻ 61 q3 ∷
   rw 62 q1 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼临丼乏") ∷
   rw 60 q2 ∷
   rw⁻ 62 q4 ∷
   rw 63 q1 ∷
   re 60 5 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q2 ∷
   rw⁻ 63 q3 ∷
   rw 64 q1 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q2 ∷
   rw⁻ 64 q3 ∷
   rw 65 q1 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 63 q7 ∷
   rw 64 q8 ∷
   rw 65 q9 ∷
   rw 66 q10 ∷
   rw 67 q9 ∷
   rw 68 q11 ∷
   rw 69 q7 ∷
   rw 70 q12 ∷
   rw 63 q13 ∷
   re 63 8 (ℓ "乨") ∷
   rw 66 q14 ∷
   re 64 3 (ℓ "丧") ∷
   rw 67 q14 ∷
   re 65 3 (ℓ "丧") ∷
   rw 68 q14 ∷
   re 66 3 (ℓ "乄") ∷
   rw 69 q14 ∷
   re 67 3 (ℓ "丧") ∷
   rw 70 q14 ∷
   re 68 3 (ℓ "乄") ∷
   rw 71 q14 ∷
   re 69 3 (ℓ "乄") ∷
   rw 70 q6 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 71 q2 ∷
   rw⁻ 73 q4 ∷
   rw 74 q1 ∷
   re 71 5 (ℓ "乑") ∷
   rw 72 q5 ∷
   re 74 1 (ℓ "乏丼临丼乏") ∷
   rw 73 q2 ∷
   rw⁻ 75 q4 ∷
   rw 76 q1 ∷
   re 73 5 (ℓ "乑") ∷
   rw 74 q5 ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q2 ∷
   rw⁻ 77 q3 ∷
   rw 78 q1 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q2 ∷
   rw⁻ 78 q3 ∷
   rw 79 q1 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q2 ∷
   rw⁻ 79 q3 ∷
   rw 80 q1 ∷
   re 77 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼临丼乏") ∷
   rw 78 q2 ∷
   rw⁻ 80 q4 ∷
   rw 81 q1 ∷
   re 78 5 (ℓ "乑") ∷
   rw 79 q5 ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q2 ∷
   rw⁻ 82 q3 ∷
   rw 83 q1 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q2 ∷
   rw⁻ 83 q3 ∷
   rw 84 q1 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q2 ∷
   rw⁻ 84 q3 ∷
   rw 85 q1 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   rw⁻ 85 q3 ∷
   rw 86 q1 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q2 ∷
   rw⁻ 86 q3 ∷
   rw 87 q1 ∷
   re 84 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q2 ∷
   rw⁻ 87 q3 ∷
   rw 88 q1 ∷
   re 85 5 (ℓ "中") ∷
   rw 86 q6 ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   rw⁻ 89 q3 ∷
   rw 90 q1 ∷
   re 87 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q2 ∷
   rw⁻ 90 q3 ∷
   rw 91 q1 ∷
   re 88 5 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q2 ∷
   rw⁻ 91 q4 ∷
   rw 92 q1 ∷
   re 89 5 (ℓ "乑") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q2 ∷
   rw⁻ 92 q3 ∷
   rw 93 q1 ∷
   re 90 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼临丼乏") ∷
   rw 91 q2 ∷
   rw⁻ 93 q4 ∷
   rw 94 q1 ∷
   re 91 5 (ℓ "乑") ∷
   re 93 1 (ℓ "乏丼临丼乏") ∷
   rw 92 q2 ∷
   rw⁻ 94 q4 ∷
   rw 95 q1 ∷
   re 92 5 (ℓ "乑") ∷
   rw 93 q15 ∷
   rw 3 q16 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q16 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q16 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q16 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 22 q3 ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q3 ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q18 ∷
   rw 31 q19 ∷
   rw 34 q16 ∷
   re 32 3 (ℓ "乀") ∷
   rw 33 q20 ∷
   rw 36 q16 ∷
   re 34 3 (ℓ "乀") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q21 ∷
   rw 36 q18 ∷
   rw⁻ 37 q22 ∷
   rw 30 q23 ∷
   re 30 8 (ℓ "乥") ∷
   rw 33 q16 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q16 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q16 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q16 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q16 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q16 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q24 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q21 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q21 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q21 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q21 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q21 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q21 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 44 q21 ∷
   rw 45 q25 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q21 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q21 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q21 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q21 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q21 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q21 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q21 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q21 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 54 q21 ∷
   rw 55 q24 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 56 q21 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q21 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 58 q21 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 59 q21 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q21 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q21 ∷
   re 63 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 62 q18 ∷
   rw 63 q19 ∷
   rw 66 q16 ∷
   re 64 3 (ℓ "乀") ∷
   rw 65 q20 ∷
   rw 68 q16 ∷
   re 66 3 (ℓ "乀") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q21 ∷
   rw 68 q18 ∷
   rw⁻ 69 q22 ∷
   rw 62 q23 ∷
   re 62 8 (ℓ "乥") ∷
   rw 65 q16 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q16 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q16 ∷
   re 65 3 (ℓ "乑") ∷
   rw 68 q16 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q16 ∷
   re 67 3 (ℓ "乑") ∷
   rw 70 q16 ∷
   re 68 3 (ℓ "乑") ∷
   rw 69 q24 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw 70 q21 ∷
   rw 71 q25 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw 72 q21 ∷
   rw 73 q25 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q21 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q21 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q21 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw 77 q21 ∷
   rw 78 q25 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q21 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q21 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q21 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q21 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q21 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 84 q21 ∷
   rw 85 q24 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 86 q21 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 87 q21 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 88 q21 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 89 q21 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 90 q21 ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 91 q21 ∷
   rw 92 q21 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q26 ∷
   re 0 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 2 q26 ∷
   rw 3 q28 ∷
   rw 4 q26 ∷
   re 2 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q26 ∷
   rw 4 q27 ∷
   rw 5 q26 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 4 q26 ∷
   rw 5 q28 ∷
   rw 6 q26 ∷
   re 4 3 (ℓ "乔") ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 5 q26 ∷
   rw 6 q28 ∷
   rw 7 q26 ∷
   re 5 3 (ℓ "乔") ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 6 q26 ∷
   rw 7 q29 ∷
   rw 8 q26 ∷
   re 6 3 (ℓ "乐") ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q32 ∷
   rw 12 q32 ∷
   rw 13 q32 ∷
   rw 14 q30 ∷
   rw 15 q31 ∷
   rw 16 q32 ∷
   rw 17 q32 ∷
   rw 18 q32 ∷
   rw 19 q32 ∷
   rw 20 q32 ∷
   rw 21 q32 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q26 ∷
   rw 23 q29 ∷
   rw 24 q26 ∷
   re 22 3 (ℓ "乐") ∷
   rw 23 q32 ∷
   rw 24 q32 ∷
   rw 25 q30 ∷
   rw 26 q32 ∷
   rw 27 q30 ∷
   rw 28 q30 ∷
   re 30 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 29 q33 ∷
   rw 30 q34 ∷
   rw 31 q35 ∷
   rw 32 q36 ∷
   rw 33 q35 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q26 ∷
   rw 35 q37 ∷
   rw 36 q26 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q33 ∷
   rw 36 q38 ∷
   rw 29 q39 ∷
   rw 30 q33 ∷
   rw 31 q34 ∷
   rw 32 q40 ∷
   rw 33 q36 ∷
   rw 34 q40 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q26 ∷
   rw 36 q27 ∷
   rw 37 q26 ∷
   re 35 3 (ℓ "丽") ∷
   rw 36 q33 ∷
   rw 37 q41 ∷
   rw 30 q42 ∷
   re 30 8 (ℓ "乥") ∷
   re 29 3 (ℓ "乤") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q26 ∷
   rw 31 q27 ∷
   rw 32 q26 ∷
   re 30 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q26 ∷
   rw 32 q27 ∷
   rw 33 q26 ∷
   re 31 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q26 ∷
   rw 33 q27 ∷
   rw 34 q26 ∷ []) Eq.refl
