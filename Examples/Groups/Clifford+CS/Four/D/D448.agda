{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D448 (W : Ws) where

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
  q2 = wE 772 W
  q3 : Eqn
  q3 = wE 481 W
  q4 : Eqn
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 1205 W
  q9 : Eqn
  q9 = wE 10 W
  q10 : Eqn
  q10 = wE 1206 W
  q11 : Eqn
  q11 = wE 1207 W
  q12 : Eqn
  q12 = wE 12 W
  q13 : Eqn
  q13 = wE 757 W
  q14 : Eqn
  q14 = wE 479 W
  q15 : Eqn
  q15 = wE 48 W
  q16 : Eqn
  q16 = wE 280 W
  q17 : Eqn
  q17 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q18 : Eqn
  q18 = wE 22 W
  q19 : Eqn
  q19 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q20 : Eqn
  q20 = wE 23 W
  q21 : Eqn
  q21 = wE 14 W
  q22 : Eqn
  q22 = eqn (ℓ "丈丼") (ℓ "丼丈") (low₁-comm (S) (Swap))
  q23 : Eqn
  q23 = wE 273 W
  q24 : Eqn
  q24 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q25 : Eqn
  q25 = wE 6 W
  q26 : Eqn
  q26 = wE 216 W
  q27 : Eqn
  q27 = wE 480 W
  q28 : Eqn
  q28 = wE 1 W
  q29 : Eqn
  q29 = wE 476 W
  q30 : Eqn
  q30 = wE 3 W
  q31 : Eqn
  q31 = wE 464 W
  q32 : Eqn
  q32 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q34 : Eqn
  q34 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))

-- hyb sym 23 @2310 part0: 500 steps
lem-hyb-sym-23-at2310-part0 : ⟪ (ℓ "义义乗义乓丶丶丶为与丶丶丶丶丶丶乓丶丶为丶丫丶丶丶与为丶丶丶丶丶丶乓丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶乓义义义业乗义义义义义义丈丫") ⟫ʷ ≈ ⟪ (ℓ "並丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑乏並丼並") ⟫ʷ
lem-hyb-sym-23-at2310-part0 = derive (ℓ "义义乗义乓丶丶丶为与丶丶丶丶丶丶乓丶丶为丶丫丶丶丶与为丶丶丶丶丶丶乓丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶乓义义义业乗义义义义义义丈丫") (ℓ "並丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑乏並丼並")
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw⁻ 77 q4 ∷
   rw⁻ 76 q4 ∷
   rw⁻ 75 q4 ∷
   rw⁻ 74 q4 ∷
   rw⁻ 73 q4 ∷
   rw⁻ 72 q4 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 70 q6 ∷
   rw⁻ 69 q4 ∷
   rw⁻ 68 q4 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw⁻ 68 q7 ∷
   rw 67 q8 ∷
   rw⁻ 66 q7 ∷
   re 67 3 (ℓ "乐") ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q10 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   rw 53 q11 ∷
   rw 52 q11 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q8 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "乐") ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   rw 21 q2 ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw⁻ 18 q7 ∷
   rw 17 q8 ∷
   rw⁻ 16 q7 ∷
   re 17 3 (ℓ "乐") ∷
   rw 15 q9 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q9 ∷
   rw 9 q11 ∷
   rw 8 q10 ∷
   rw 7 q9 ∷
   rw 6 q9 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "乐") ∷
   rw⁻ 3 q4 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 0 q4 ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 79 q14 ∷
   rw 78 q15 ∷
   rw 77 q15 ∷
   rw 76 q15 ∷
   rw 75 q15 ∷
   rw 74 q15 ∷
   rw 73 q15 ∷
   rw 72 q16 ∷
   rw⁻ 71 q17 ∷
   rw 70 q15 ∷
   rw 69 q15 ∷
   rw 68 q15 ∷
   re 67 1 (ℓ "乏丼丳丼乏") ∷
   rw 70 q18 ∷
   rw 69 q19 ∷
   rw 67 q20 ∷
   re 68 5 (ℓ "乐") ∷
   re 66 1 (ℓ "丼丠丼") ∷
   rw 68 q21 ∷
   re 65 1 (ℓ "丼丠丼") ∷
   rw 67 q21 ∷
   re 64 1 (ℓ "丼丠丼") ∷
   rw 66 q21 ∷
   re 63 1 (ℓ "丼丠丼") ∷
   rw 65 q21 ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 64 q21 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 63 q21 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 62 q21 ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 61 q21 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 60 q21 ∷
   re 57 1 (ℓ "丼两丼") ∷
   rw 59 q21 ∷
   rw 56 q22 ∷
   rw 55 q22 ∷
   rw 54 q22 ∷
   rw 53 q22 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 54 q21 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 53 q21 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 52 q21 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 51 q21 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 50 q21 ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 49 q21 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 48 q21 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 47 q21 ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 46 q21 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 45 q21 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 44 q21 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 43 q21 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 42 q21 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 41 q21 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 40 q21 ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 39 q21 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 38 q21 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 37 q21 ∷
   re 34 1 (ℓ "乏丼丳丼乏") ∷
   rw 37 q18 ∷
   rw 36 q19 ∷
   rw 34 q20 ∷
   re 35 5 (ℓ "乐") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 35 q21 ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 34 q21 ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 33 q21 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 32 q21 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 31 q21 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 30 q21 ∷
   re 27 1 (ℓ "丼两丼") ∷
   rw 29 q21 ∷
   rw 26 q22 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 27 q21 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 26 q21 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 25 q21 ∷
   rw 22 q13 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 23 q21 ∷
   re 20 1 (ℓ "丼两丼") ∷
   rw 22 q21 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 21 q21 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 20 q21 ∷
   re 17 1 (ℓ "乏丼丳丼乏") ∷
   rw 20 q18 ∷
   rw 19 q19 ∷
   rw 17 q20 ∷
   re 18 5 (ℓ "乐") ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 18 q21 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q21 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q21 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q21 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q21 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (ℓ "丼两丼") ∷
   rw 11 q21 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q21 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q21 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q21 ∷
   re 5 1 (ℓ "乏丼丳丼乏") ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw 5 q20 ∷
   re 6 5 (ℓ "乐") ∷
   rw 4 q15 ∷
   rw 3 q16 ∷
   rw 2 q15 ∷
   rw 1 q15 ∷
   rw 82 q1 ∷
   rw 81 q23 ∷
   rw⁻ 80 q24 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw⁻ 81 q7 ∷
   rw 80 q9 ∷
   rw⁻ 79 q7 ∷
   re 80 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw⁻ 80 q7 ∷
   rw 79 q9 ∷
   rw⁻ 78 q7 ∷
   re 79 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw⁻ 79 q7 ∷
   rw 78 q9 ∷
   rw⁻ 77 q7 ∷
   re 78 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw⁻ 78 q7 ∷
   rw 77 q9 ∷
   rw⁻ 76 q7 ∷
   re 77 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw⁻ 77 q7 ∷
   rw 76 q9 ∷
   rw⁻ 75 q7 ∷
   re 76 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw⁻ 76 q7 ∷
   rw 75 q9 ∷
   rw⁻ 74 q7 ∷
   re 75 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw⁻ 75 q7 ∷
   rw 74 q23 ∷
   rw⁻ 73 q7 ∷
   re 74 3 (ℓ "乑") ∷
   rw⁻ 72 q6 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw⁻ 73 q7 ∷
   rw 72 q9 ∷
   rw⁻ 71 q7 ∷
   re 72 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw⁻ 72 q7 ∷
   rw 71 q9 ∷
   rw⁻ 70 q7 ∷
   re 71 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw⁻ 71 q7 ∷
   rw 70 q9 ∷
   rw⁻ 69 q7 ∷
   re 70 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏乃乏") ∷
   rw⁻ 70 q7 ∷
   rw 69 q25 ∷
   rw⁻ 68 q7 ∷
   re 69 3 (ℓ "乓") ∷
   rw 67 q26 ∷
   rw 66 q26 ∷
   rw 65 q26 ∷
   rw 64 q26 ∷
   rw 63 q26 ∷
   rw 62 q26 ∷
   rw 61 q26 ∷
   rw 60 q26 ∷
   rw 59 q26 ∷
   rw 58 q27 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q26 ∷
   rw 52 q26 ∷
   rw 51 q26 ∷
   rw 50 q26 ∷
   rw 49 q26 ∷
   rw 48 q26 ∷
   rw 47 q26 ∷
   rw 46 q26 ∷
   rw 45 q26 ∷
   rw 44 q26 ∷
   rw 43 q26 ∷
   rw 42 q26 ∷
   rw 41 q26 ∷
   rw 40 q26 ∷
   rw 39 q26 ∷
   rw 38 q26 ∷
   rw 37 q26 ∷
   rw 36 q26 ∷
   re 35 1 (ℓ "乏乃乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q25 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "乓") ∷
   rw 34 q26 ∷
   rw 33 q26 ∷
   rw 32 q26 ∷
   rw 31 q26 ∷
   rw 30 q26 ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   rw 27 q3 ∷
   rw 26 q26 ∷
   rw 25 q26 ∷
   rw 24 q26 ∷
   rw 23 q23 ∷
   rw 22 q26 ∷
   rw 21 q27 ∷
   rw 20 q26 ∷
   rw 19 q26 ∷
   re 18 1 (ℓ "乏乃乏") ∷
   rw⁻ 20 q7 ∷
   rw 19 q25 ∷
   rw⁻ 18 q7 ∷
   re 19 3 (ℓ "乓") ∷
   rw 17 q26 ∷
   rw 16 q26 ∷
   rw 15 q26 ∷
   rw 14 q26 ∷
   rw 13 q26 ∷
   rw 12 q26 ∷
   rw 11 q3 ∷
   rw 10 q27 ∷
   rw 9 q26 ∷
   rw 8 q26 ∷
   rw 7 q26 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q25 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "乓") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw⁻ 7 q7 ∷
   rw 6 q9 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q23 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "乑") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q7 ∷
   rw 4 q9 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q7 ∷
   rw 3 q9 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (ℓ "中") ∷
   rw 83 q28 ∷
   rw 82 q28 ∷
   re 83 3 (ℓ "乑") ∷
   rw 81 q29 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q30 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q30 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q30 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q30 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q30 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q30 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 76 q30 ∷
   rw 73 q31 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q30 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q30 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q30 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 71 q30 ∷
   rw 68 q32 ∷
   rw 67 q32 ∷
   rw 66 q32 ∷
   rw 65 q32 ∷
   rw 64 q32 ∷
   rw 63 q32 ∷
   rw 62 q32 ∷
   rw 61 q32 ∷
   rw 60 q32 ∷
   rw 59 q33 ∷
   rw 58 q34 ∷
   rw 57 q34 ∷
   rw 56 q34 ∷
   rw 55 q34 ∷
   rw 54 q32 ∷
   rw 53 q32 ∷
   rw 52 q32 ∷
   rw 51 q32 ∷
   rw 50 q32 ∷
   rw 49 q32 ∷
   rw 48 q32 ∷
   rw 47 q32 ∷
   rw 46 q32 ∷
   rw 45 q32 ∷
   rw 44 q32 ∷
   rw 43 q32 ∷
   rw 42 q32 ∷
   rw 41 q32 ∷
   rw 40 q32 ∷
   rw 39 q32 ∷
   rw 38 q32 ∷
   rw 37 q32 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q30 ∷
   rw 35 q32 ∷
   rw 34 q32 ∷
   rw 33 q32 ∷
   rw 32 q32 ∷
   rw 31 q32 ∷
   rw 30 q32 ∷
   rw 29 q33 ∷
   rw 28 q34 ∷
   rw 27 q32 ∷
   rw 26 q32 ∷
   rw 25 q32 ∷
   rw 24 q28 ∷
   re 25 3 (ℓ "乑") ∷
   rw 23 q32 ∷
   rw 22 q33 ∷
   rw 21 q32 ∷
   rw 20 q32 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 21 q30 ∷
   rw 18 q32 ∷
   rw 17 q32 ∷
   rw 16 q32 ∷
   rw 15 q32 ∷
   rw 14 q32 ∷
   rw 13 q32 ∷
   rw 12 q34 ∷
   rw 11 q33 ∷
   rw 10 q32 ∷
   rw 9 q32 ∷
   rw 8 q32 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q30 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q30 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q30 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q30 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q30 ∷ []) Eq.refl
