{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D449 (W : Ws) where

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
  q1 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 372 W
  q4 : Eqn
  q4 = wE 378 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 151 W
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 25 W
  q10 : Eqn
  q10 = wE 275 W
  q11 : Eqn
  q11 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q13 : Eqn
  q13 = wE 327 W
  q14 : Eqn
  q14 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q15 : Eqn
  q15 = wE 315 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 20 W
  q18 : Eqn
  q18 = wE 359 W
  q19 : Eqn
  q19 = wE 114 W
  q20 : Eqn
  q20 = wE 18 W
  q21 : Eqn
  q21 = wE 355 W
  q22 : Eqn
  q22 = wE 343 W
  q23 : Eqn
  q23 = wE 12 W
  q24 : Eqn
  q24 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q25 : Eqn
  q25 = eqn (ℓ "丈丼") (ℓ "丼丈") (low₁-comm (S) (Swap))
  q26 : Eqn
  q26 = wE 14 W
  q27 : Eqn
  q27 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q28 : Eqn
  q28 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q29 : Eqn
  q29 = wE 39 W
  q30 : Eqn
  q30 = wE 27 W
  q31 : Eqn
  q31 = wE 329 W
  q32 : Eqn
  q32 = wE 324 W
  q33 : Eqn
  q33 = wE 311 W

-- hyb sym 23 @2310 part2: 425 steps
lem-hyb-sym-23-at2310-part2 : ⟪ (ℓ "並丼並中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乏临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临乏並丼並") ⟫ʷ ≈ ⟪ (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") ⟫ʷ
lem-hyb-sym-23-at2310-part2 = derive (ℓ "並丼並中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乏临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临乏並丼並") (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为")
  (rw⁻ 24 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q2 ∷
   rw 36 q4 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q2 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 54 q2 ∷
   rw 55 q3 ∷
   rw 56 q3 ∷
   rw 57 q3 ∷
   rw 58 q3 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 59 q2 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q2 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q2 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q2 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 64 q2 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 65 q2 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 66 q2 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 67 q2 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 68 q2 ∷
   rw 69 q4 ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q5 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q6 ∷
   rw 76 q5 ∷
   re 74 3 (ℓ "乑") ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q5 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q5 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q5 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q5 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q5 ∷
   re 80 3 (ℓ "中") ∷
   rw⁻ 81 q7 ∷
   rw⁻ 82 q1 ∷
   rw 83 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "乔") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q8 ∷
   rw 6 q9 ∷
   rw 7 q8 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q11 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q12 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 18 q11 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q10 ∷
   rw 22 q9 ∷
   rw 23 q13 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q12 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q9 ∷
   rw 35 q11 ∷
   rw 36 q9 ∷
   rw 37 q9 ∷
   rw 38 q9 ∷
   rw 39 q9 ∷
   rw 40 q9 ∷
   rw 41 q9 ∷
   rw 42 q9 ∷
   rw 43 q9 ∷
   rw 44 q9 ∷
   rw 45 q9 ∷
   rw 46 q9 ∷
   rw 47 q9 ∷
   rw 48 q9 ∷
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 51 q9 ∷
   rw 52 q9 ∷
   rw 53 q9 ∷
   rw 54 q12 ∷
   rw 55 q12 ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   rw 58 q10 ∷
   rw 59 q9 ∷
   rw 60 q9 ∷
   rw 61 q9 ∷
   rw 62 q9 ∷
   rw 63 q9 ∷
   rw 64 q9 ∷
   rw 65 q9 ∷
   rw 66 q9 ∷
   rw 67 q9 ∷
   rw 68 q11 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 69 q8 ∷
   rw 70 q9 ∷
   rw 71 q8 ∷
   re 69 3 (ℓ "丽") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 70 q8 ∷
   rw 71 q9 ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "丽") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 71 q8 ∷
   rw 72 q9 ∷
   rw 73 q8 ∷
   re 71 3 (ℓ "丽") ∷
   rw 72 q14 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 73 q8 ∷
   rw 74 q10 ∷
   rw 75 q8 ∷
   re 73 3 (ℓ "乔") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q8 ∷
   rw 75 q9 ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q8 ∷
   rw 76 q9 ∷
   rw 77 q8 ∷
   re 75 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q8 ∷
   rw 77 q9 ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 77 q8 ∷
   rw 78 q9 ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 78 q8 ∷
   rw 79 q9 ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "丽") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q8 ∷
   rw 80 q9 ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "丽") ∷
   rw 80 q15 ∷
   rw 81 q13 ∷
   rw 82 q16 ∷
   rw 1 q17 ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q20 ∷
   rw 8 q20 ∷
   rw 9 q21 ∷
   rw 10 q22 ∷
   rw 11 q20 ∷
   rw 12 q20 ∷
   rw 13 q20 ∷
   rw 14 q20 ∷
   rw 15 q20 ∷
   rw 16 q20 ∷
   rw 17 q19 ∷
   rw 18 q20 ∷
   rw 19 q20 ∷
   rw 20 q21 ∷
   rw 21 q20 ∷
   rw 24 q23 ∷
   re 22 3 (ℓ "丫") ∷
   rw 23 q20 ∷
   rw 24 q20 ∷
   rw 25 q20 ∷
   rw 26 q22 ∷
   rw 27 q21 ∷
   rw 28 q20 ∷
   rw 29 q20 ∷
   rw 30 q20 ∷
   rw 31 q20 ∷
   rw 32 q20 ∷
   rw 33 q20 ∷
   rw 34 q19 ∷
   rw 35 q20 ∷
   rw 36 q20 ∷
   rw 37 q20 ∷
   rw 38 q20 ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q20 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q20 ∷
   rw 49 q20 ∷
   rw 50 q20 ∷
   rw 51 q20 ∷
   rw 52 q20 ∷
   rw 53 q22 ∷
   rw 54 q22 ∷
   rw 55 q22 ∷
   rw 56 q22 ∷
   rw 57 q21 ∷
   rw 58 q20 ∷
   rw 59 q20 ∷
   rw 60 q20 ∷
   rw 61 q20 ∷
   rw 62 q20 ∷
   rw 63 q20 ∷
   rw 64 q20 ∷
   rw 65 q20 ∷
   rw 66 q20 ∷
   rw 67 q19 ∷
   rw 68 q17 ∷
   rw 69 q17 ∷
   rw 70 q17 ∷
   rw 71 q24 ∷
   rw 72 q18 ∷
   rw 73 q17 ∷
   rw 74 q17 ∷
   rw 75 q17 ∷
   rw 76 q17 ∷
   rw 77 q17 ∷
   rw 78 q17 ∷
   rw⁻ 79 q25 ∷
   rw 82 q23 ∷
   re 80 3 (ℓ "丫") ∷
   rw 81 q26 ∷
   rw 0 q27 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 4 q8 ∷
   rw 5 q29 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q30 ∷
   rw 6 q30 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q15 ∷
   rw 10 q30 ∷
   rw 11 q30 ∷
   rw 12 q30 ∷
   rw 13 q30 ∷
   rw 14 q30 ∷
   rw 15 q30 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q8 ∷
   rw 17 q29 ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "乐") ∷
   rw 17 q30 ∷
   rw 18 q30 ∷
   rw 19 q31 ∷
   rw 20 q30 ∷
   rw 21 q32 ∷
   rw 22 q30 ∷
   rw 23 q30 ∷
   rw 24 q30 ∷
   rw 25 q15 ∷
   rw 26 q31 ∷
   rw 27 q30 ∷
   rw 28 q30 ∷
   rw 29 q30 ∷
   rw 30 q30 ∷
   rw 31 q30 ∷
   rw 32 q30 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q8 ∷
   rw 34 q29 ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乐") ∷
   rw 34 q30 ∷
   rw 35 q30 ∷
   rw 36 q30 ∷
   rw 37 q30 ∷
   rw 38 q30 ∷
   rw 39 q30 ∷
   rw 40 q30 ∷
   rw 41 q30 ∷
   rw 42 q30 ∷
   rw 43 q30 ∷
   rw 44 q30 ∷
   rw 45 q30 ∷
   rw 46 q30 ∷
   rw 47 q30 ∷
   rw 48 q30 ∷
   rw 49 q30 ∷
   rw 50 q30 ∷
   rw 51 q30 ∷
   rw 52 q15 ∷
   rw 53 q15 ∷
   rw 54 q15 ∷
   rw 55 q15 ∷
   rw 56 q31 ∷
   rw 57 q30 ∷
   rw 58 q30 ∷
   rw 59 q30 ∷
   rw 60 q30 ∷
   rw 61 q30 ∷
   rw 62 q30 ∷
   rw 63 q30 ∷
   rw 64 q30 ∷
   rw 65 q30 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q8 ∷
   rw 67 q29 ∷
   rw 68 q8 ∷
   re 66 3 (ℓ "乐") ∷
   rw 67 q27 ∷
   rw 68 q27 ∷
   rw 69 q27 ∷
   rw 70 q14 ∷
   rw 71 q28 ∷
   rw 72 q27 ∷
   rw 73 q27 ∷
   rw 74 q27 ∷
   rw 75 q27 ∷
   rw 76 q27 ∷
   rw 77 q27 ∷
   rw 78 q33 ∷
   rw 79 q32 ∷
   rw 80 q16 ∷ []) Eq.refl
