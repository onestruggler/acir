{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D430 (W : Ws) where

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
  q2 = wE 480 W
  q3 : Eqn
  q3 = wE 481 W
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 10 W
  q6 : Eqn
  q6 = wE 273 W
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q9 : Eqn
  q9 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q10 : Eqn
  q10 = wE 12 W
  q11 : Eqn
  q11 = wE 479 W
  q12 : Eqn
  q12 = wE 22 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = wE 23 W
  q15 : Eqn
  q15 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q17 : Eqn
  q17 = wE 78 W
  q18 : Eqn
  q18 = wE 14 W
  q19 : Eqn
  q19 = wE 477 W
  q20 : Eqn
  q20 = wE 1 W
  q21 : Eqn
  q21 = wE 476 W
  q22 : Eqn
  q22 = wE 3 W
  q23 : Eqn
  q23 = wE 464 W
  q24 : Eqn
  q24 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q25 : Eqn
  q25 = wE 478 W

-- hyb sym 23 @1320 part0: 500 steps
lem-hyb-sym-23-at1320-part0 : ⟪ (ℓ "丽丽乔丽乖丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶两丶丶丶且乇丶丶丶丶丶丶乖丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶乖丽丽丽业乔丽丽丽丽丽丽丈两") ⟫ʷ ≈ ⟪ (ℓ "並丼乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丼丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏丼並") ⟫ʷ
lem-hyb-sym-23-at1320-part0 = derive (ℓ "丽丽乔丽乖丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶两丶丶丶且乇丶丶丶丶丶丶乖丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶乖丽丽丽业乔丽丽丽丽丽丽丈两") (ℓ "並丼乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丼丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏丼並")
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
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
   rw 72 q6 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (ℓ "乑") ∷
   rw⁻ 70 q7 ∷
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
   rw⁻ 66 q8 ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   rw 62 q5 ∷
   rw 61 q5 ∷
   rw 60 q5 ∷
   rw 59 q5 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw⁻ 55 q9 ∷
   rw⁻ 54 q9 ∷
   rw⁻ 53 q9 ∷
   rw⁻ 52 q9 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw⁻ 33 q8 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw⁻ 25 q9 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw⁻ 16 q8 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw⁻ 9 q9 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   rw⁻ 4 q8 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q4 ∷
   rw 4 q5 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw⁻ 4 q4 ∷
   rw 3 q6 ∷
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
   rw 81 q10 ∷
   rw 80 q10 ∷
   re 81 3 (ℓ "乄") ∷
   rw 79 q11 ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 78 q14 ∷
   re 79 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q12 ∷
   rw 79 q13 ∷
   rw 77 q14 ∷
   re 78 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q12 ∷
   rw 78 q13 ∷
   rw 76 q14 ∷
   re 77 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q12 ∷
   rw 77 q13 ∷
   rw 75 q14 ∷
   re 76 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q12 ∷
   rw 76 q13 ∷
   rw 74 q14 ∷
   re 75 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q12 ∷
   rw 75 q13 ∷
   rw 73 q14 ∷
   re 74 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 75 q12 ∷
   rw 74 q15 ∷
   rw 72 q14 ∷
   re 73 5 (ℓ "乑") ∷
   rw⁻ 71 q16 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q12 ∷
   rw 72 q13 ∷
   rw 70 q14 ∷
   re 71 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 69 q14 ∷
   re 70 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 68 q14 ∷
   re 69 5 (ℓ "中") ∷
   rw 67 q17 ∷
   re 66 1 (ℓ "丼丠丼") ∷
   rw 68 q18 ∷
   re 65 1 (ℓ "丼丠丼") ∷
   rw 67 q18 ∷
   re 64 1 (ℓ "丼丠丼") ∷
   rw 66 q18 ∷
   re 63 1 (ℓ "丼丠丼") ∷
   rw 65 q18 ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 64 q18 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 63 q18 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 62 q18 ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 61 q18 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 60 q18 ∷
   re 57 1 (ℓ "丼临丼") ∷
   rw 59 q18 ∷
   rw 56 q19 ∷
   rw 55 q19 ∷
   rw 54 q19 ∷
   rw 53 q19 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 54 q18 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 53 q18 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 52 q18 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 51 q18 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 50 q18 ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 49 q18 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 48 q18 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 47 q18 ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 46 q18 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 45 q18 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 44 q18 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 43 q18 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 42 q18 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 41 q18 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 40 q18 ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 39 q18 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 38 q18 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 37 q18 ∷
   rw 34 q17 ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 35 q18 ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 34 q18 ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 33 q18 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 32 q18 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 31 q18 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 30 q18 ∷
   re 27 1 (ℓ "丼临丼") ∷
   rw 29 q18 ∷
   rw 26 q19 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 27 q18 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 26 q18 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 25 q18 ∷
   rw 22 q10 ∷
   re 23 3 (ℓ "乄") ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 23 q18 ∷
   re 20 1 (ℓ "丼临丼") ∷
   rw 22 q18 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 21 q18 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 20 q18 ∷
   rw 17 q17 ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 18 q18 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q18 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q18 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q18 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q18 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (ℓ "丼临丼") ∷
   rw 11 q18 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q18 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q18 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q18 ∷
   rw 5 q17 ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q12 ∷
   rw 6 q13 ∷
   rw 4 q14 ∷
   re 5 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丼临丼乏") ∷
   rw 6 q12 ∷
   rw 5 q15 ∷
   rw 3 q14 ∷
   re 4 5 (ℓ "乑") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q12 ∷
   rw 4 q13 ∷
   rw 2 q14 ∷
   re 3 5 (ℓ "中") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 1 q14 ∷
   re 2 5 (ℓ "中") ∷
   rw 82 q20 ∷
   rw 81 q20 ∷
   re 82 3 (ℓ "乑") ∷
   rw 80 q21 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q22 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q22 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q22 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q22 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q22 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q22 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw 75 q22 ∷
   rw 72 q23 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q22 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q22 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q22 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 70 q22 ∷
   rw 67 q13 ∷
   rw 66 q13 ∷
   rw 65 q13 ∷
   rw 64 q13 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q13 ∷
   rw 60 q13 ∷
   rw 59 q13 ∷
   rw 58 q15 ∷
   rw 57 q24 ∷
   rw 56 q24 ∷
   rw 55 q24 ∷
   rw 54 q24 ∷
   rw 53 q13 ∷
   rw 52 q13 ∷
   rw 51 q13 ∷
   rw 50 q13 ∷
   rw 49 q13 ∷
   rw 48 q13 ∷
   rw 47 q13 ∷
   rw 46 q13 ∷
   rw 45 q13 ∷
   rw 44 q13 ∷
   rw 43 q13 ∷
   rw 42 q13 ∷
   rw 41 q13 ∷
   rw 40 q13 ∷
   rw 39 q13 ∷
   rw 38 q13 ∷
   rw 37 q13 ∷
   rw 36 q13 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 37 q22 ∷
   rw 34 q13 ∷
   rw 33 q13 ∷
   rw 32 q13 ∷
   rw 31 q13 ∷
   rw 30 q13 ∷
   rw 29 q13 ∷
   rw 28 q15 ∷
   rw 27 q24 ∷
   rw 26 q13 ∷
   rw 25 q13 ∷
   rw 24 q13 ∷
   rw 23 q20 ∷
   re 24 3 (ℓ "乑") ∷
   rw 22 q13 ∷
   rw 21 q15 ∷
   rw 20 q13 ∷
   rw 19 q13 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 20 q22 ∷
   rw 17 q13 ∷
   rw 16 q13 ∷
   rw 15 q13 ∷
   rw 14 q13 ∷
   rw 13 q13 ∷
   rw 12 q13 ∷
   rw 11 q24 ∷
   rw 10 q15 ∷
   rw 9 q13 ∷
   rw 8 q13 ∷
   rw 7 q13 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q22 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q22 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q22 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q22 ∷
   rw 83 q10 ∷
   re 82 1 (ℓ "乏丼临丼乏") ∷
   rw 85 q12 ∷
   rw 84 q15 ∷
   rw 82 q14 ∷
   re 83 5 (ℓ "乑") ∷
   rw⁻ 81 q16 ∷
   re 80 1 (ℓ "丼丠丼") ∷
   rw 82 q18 ∷
   re 79 1 (ℓ "丼丠丼") ∷
   rw 81 q18 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q18 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q18 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q18 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q18 ∷
   re 74 1 (ℓ "丼临丼") ∷
   rw 76 q18 ∷
   rw 73 q19 ∷
   re 72 1 (ℓ "丼丠丼") ∷
   rw 74 q18 ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 73 q18 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q18 ∷
   rw 69 q25 ∷
   rw 68 q10 ∷
   re 69 3 (ℓ "丧") ∷
   rw 67 q10 ∷
   re 68 3 (ℓ "丧") ∷
   rw 66 q10 ∷
   re 67 3 (ℓ "丧") ∷
   rw 65 q10 ∷
   re 66 3 (ℓ "丧") ∷
   rw 64 q10 ∷
   re 65 3 (ℓ "丧") ∷
   rw 63 q10 ∷
   re 64 3 (ℓ "丧") ∷
   rw 62 q10 ∷
   re 63 3 (ℓ "丧") ∷
   rw 61 q10 ∷
   re 62 3 (ℓ "丧") ∷
   rw 60 q10 ∷
   re 61 3 (ℓ "丧") ∷
   rw 59 q10 ∷
   re 60 3 (ℓ "乄") ∷
   rw 58 q11 ∷
   rw 57 q11 ∷
   rw 56 q11 ∷
   rw 55 q11 ∷
   rw 54 q10 ∷
   re 55 3 (ℓ "丧") ∷
   rw 53 q10 ∷
   re 54 3 (ℓ "丧") ∷
   rw 52 q10 ∷
   re 53 3 (ℓ "丧") ∷
   rw 51 q10 ∷
   re 52 3 (ℓ "丧") ∷
   rw 50 q10 ∷
   re 51 3 (ℓ "丧") ∷
   rw 49 q10 ∷
   re 50 3 (ℓ "丧") ∷
   rw 48 q10 ∷
   re 49 3 (ℓ "丧") ∷
   rw 47 q10 ∷
   re 48 3 (ℓ "丧") ∷
   rw 46 q10 ∷
   re 47 3 (ℓ "丧") ∷ []) Eq.refl
