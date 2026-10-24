{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D181 (W : Ws) where

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
  q2 = wE 757 W
  q3 : Eqn
  q3 = wE 479 W
  q4 : Eqn
  q4 = wE 48 W
  q5 : Eqn
  q5 = wE 280 W
  q6 : Eqn
  q6 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q7 : Eqn
  q7 = wE 22 W
  q8 : Eqn
  q8 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q9 : Eqn
  q9 = wE 23 W
  q10 : Eqn
  q10 = wE 14 W
  q11 : Eqn
  q11 = eqn (ℓ "丈丼") (ℓ "丼丈") (low₁-comm (S) (Swap))
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = wE 273 W
  q14 : Eqn
  q14 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 10 W
  q17 : Eqn
  q17 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 6 W
  q19 : Eqn
  q19 = wE 216 W
  q20 : Eqn
  q20 = wE 480 W
  q21 : Eqn
  q21 = wE 481 W
  q22 : Eqn
  q22 = wE 1 W
  q23 : Eqn
  q23 = wE 476 W
  q24 : Eqn
  q24 = wE 3 W
  q25 : Eqn
  q25 = wE 464 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q28 : Eqn
  q28 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q29 : Eqn
  q29 = wE 477 W
  q30 : Eqn
  q30 = wE 478 W

-- AXIOM LF @2301 part0: 500 steps
lem-AXIOM-LF-at2301-part0 : ⟪ (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") ⟫ʷ ≈ ⟪ (ℓ "丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丼丼丠丼丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏並丼") ⟫ʷ
lem-AXIOM-LF-at2301-part0 = derive (ℓ "义义乗义乐丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧为丧丧丧丈丫丧丧丧丧丧丧乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丈丫丧丧丧丧丧丧丧丧丧乐义义义业乗义义义义义义与为") (ℓ "丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丼丼丠丼丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏並丼")
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 76 q4 ∷
   rw 75 q4 ∷
   rw 74 q4 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q5 ∷
   rw⁻ 70 q6 ∷
   rw 69 q4 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   re 66 1 (ℓ "乏丼丳丼乏") ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   rw 66 q9 ∷
   re 67 5 (ℓ "乐") ∷
   re 65 1 (ℓ "丼丠丼") ∷
   rw 67 q10 ∷
   re 64 1 (ℓ "丼丠丼") ∷
   rw 66 q10 ∷
   re 63 1 (ℓ "丼丠丼") ∷
   rw 65 q10 ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 64 q10 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 63 q10 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 62 q10 ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 61 q10 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 60 q10 ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 59 q10 ∷
   re 56 1 (ℓ "丼两丼") ∷
   rw 58 q10 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   rw 53 q11 ∷
   rw 52 q11 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 53 q10 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 52 q10 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 51 q10 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 50 q10 ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 49 q10 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 48 q10 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 47 q10 ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 46 q10 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 45 q10 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 44 q10 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 43 q10 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 42 q10 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 41 q10 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 40 q10 ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 39 q10 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 38 q10 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 37 q10 ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 36 q10 ∷
   re 33 1 (ℓ "乏丼丳丼乏") ∷
   rw 36 q7 ∷
   rw 35 q8 ∷
   rw 33 q9 ∷
   re 34 5 (ℓ "乐") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 34 q10 ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 33 q10 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 32 q10 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 31 q10 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 30 q10 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 29 q10 ∷
   re 26 1 (ℓ "丼两丼") ∷
   rw 28 q10 ∷
   rw 25 q11 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 26 q10 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 25 q10 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 24 q10 ∷
   rw 21 q2 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 22 q10 ∷
   re 19 1 (ℓ "丼两丼") ∷
   rw 21 q10 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 20 q10 ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 19 q10 ∷
   re 16 1 (ℓ "乏丼丳丼乏") ∷
   rw 19 q7 ∷
   rw 18 q8 ∷
   rw 16 q9 ∷
   re 17 5 (ℓ "乐") ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q10 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q10 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q10 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q10 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q10 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q10 ∷
   rw 9 q11 ∷
   re 8 1 (ℓ "丼两丼") ∷
   rw 10 q10 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q10 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q10 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q10 ∷
   re 4 1 (ℓ "乏丼丳丼乏") ∷
   rw 7 q7 ∷
   rw 6 q8 ∷
   rw 4 q9 ∷
   re 5 5 (ℓ "乐") ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw⁻ 79 q14 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw⁻ 80 q15 ∷
   rw 79 q16 ∷
   rw⁻ 78 q15 ∷
   re 79 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw⁻ 79 q15 ∷
   rw 78 q16 ∷
   rw⁻ 77 q15 ∷
   re 78 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw⁻ 78 q15 ∷
   rw 77 q16 ∷
   rw⁻ 76 q15 ∷
   re 77 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw⁻ 77 q15 ∷
   rw 76 q16 ∷
   rw⁻ 75 q15 ∷
   re 76 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw⁻ 76 q15 ∷
   rw 75 q16 ∷
   rw⁻ 74 q15 ∷
   re 75 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw⁻ 75 q15 ∷
   rw 74 q16 ∷
   rw⁻ 73 q15 ∷
   re 74 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw⁻ 74 q15 ∷
   rw 73 q13 ∷
   rw⁻ 72 q15 ∷
   re 73 3 (ℓ "乑") ∷
   rw⁻ 71 q17 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw⁻ 72 q15 ∷
   rw 71 q16 ∷
   rw⁻ 70 q15 ∷
   re 71 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw⁻ 71 q15 ∷
   rw 70 q16 ∷
   rw⁻ 69 q15 ∷
   re 70 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw⁻ 70 q15 ∷
   rw 69 q16 ∷
   rw⁻ 68 q15 ∷
   re 69 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏乃乏") ∷
   rw⁻ 69 q15 ∷
   rw 68 q18 ∷
   rw⁻ 67 q15 ∷
   re 68 3 (ℓ "乓") ∷
   rw 66 q19 ∷
   rw 65 q19 ∷
   rw 64 q19 ∷
   rw 63 q19 ∷
   rw 62 q19 ∷
   rw 61 q19 ∷
   rw 60 q19 ∷
   rw 59 q19 ∷
   rw 58 q19 ∷
   rw 57 q20 ∷
   rw 56 q21 ∷
   rw 55 q21 ∷
   rw 54 q21 ∷
   rw 53 q21 ∷
   rw 52 q19 ∷
   rw 51 q19 ∷
   rw 50 q19 ∷
   rw 49 q19 ∷
   rw 48 q19 ∷
   rw 47 q19 ∷
   rw 46 q19 ∷
   rw 45 q19 ∷
   rw 44 q19 ∷
   rw 43 q19 ∷
   rw 42 q19 ∷
   rw 41 q19 ∷
   rw 40 q19 ∷
   rw 39 q19 ∷
   rw 38 q19 ∷
   rw 37 q19 ∷
   rw 36 q19 ∷
   rw 35 q19 ∷
   re 34 1 (ℓ "乏乃乏") ∷
   rw⁻ 36 q15 ∷
   rw 35 q18 ∷
   rw⁻ 34 q15 ∷
   re 35 3 (ℓ "乓") ∷
   rw 33 q19 ∷
   rw 32 q19 ∷
   rw 31 q19 ∷
   rw 30 q19 ∷
   rw 29 q19 ∷
   rw 28 q19 ∷
   rw 27 q20 ∷
   rw 26 q21 ∷
   rw 25 q19 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   rw 22 q13 ∷
   rw 21 q19 ∷
   rw 20 q20 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   re 17 1 (ℓ "乏乃乏") ∷
   rw⁻ 19 q15 ∷
   rw 18 q18 ∷
   rw⁻ 17 q15 ∷
   re 18 3 (ℓ "乓") ∷
   rw 16 q19 ∷
   rw 15 q19 ∷
   rw 14 q19 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q21 ∷
   rw 9 q20 ∷
   rw 8 q19 ∷
   rw 7 q19 ∷
   rw 6 q19 ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw⁻ 7 q15 ∷
   rw 6 q18 ∷
   rw⁻ 5 q15 ∷
   re 6 3 (ℓ "乓") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw⁻ 6 q15 ∷
   rw 5 q16 ∷
   rw⁻ 4 q15 ∷
   re 5 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw⁻ 5 q15 ∷
   rw 4 q13 ∷
   rw⁻ 3 q15 ∷
   re 4 3 (ℓ "乑") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q15 ∷
   rw 3 q16 ∷
   rw⁻ 2 q15 ∷
   re 3 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q15 ∷
   rw 2 q16 ∷
   rw⁻ 1 q15 ∷
   re 2 3 (ℓ "中") ∷
   rw 82 q22 ∷
   rw 81 q22 ∷
   re 82 3 (ℓ "乑") ∷
   rw 80 q23 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q24 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q24 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q24 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q24 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q24 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q24 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw 75 q24 ∷
   rw 72 q25 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q24 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q24 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q24 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 70 q24 ∷
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
   rw 57 q28 ∷
   rw 56 q28 ∷
   rw 55 q28 ∷
   rw 54 q28 ∷
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
   re 35 1 (ℓ "乏乆乏") ∷
   rw 37 q24 ∷
   rw 34 q26 ∷
   rw 33 q26 ∷
   rw 32 q26 ∷
   rw 31 q26 ∷
   rw 30 q26 ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   rw 27 q28 ∷
   rw 26 q26 ∷
   rw 25 q26 ∷
   rw 24 q26 ∷
   rw 23 q22 ∷
   re 24 3 (ℓ "乑") ∷
   rw 22 q26 ∷
   rw 21 q27 ∷
   rw 20 q26 ∷
   rw 19 q26 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 20 q24 ∷
   rw 17 q26 ∷
   rw 16 q26 ∷
   rw 15 q26 ∷
   rw 14 q26 ∷
   rw 13 q26 ∷
   rw 12 q26 ∷
   rw 11 q28 ∷
   rw 10 q27 ∷
   rw 9 q26 ∷
   rw 8 q26 ∷
   rw 7 q26 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q24 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q24 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q24 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q24 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q24 ∷
   rw 83 q1 ∷
   re 82 1 (ℓ "乏丼临丼乏") ∷
   rw 85 q7 ∷
   rw 84 q27 ∷
   rw 82 q9 ∷
   re 83 5 (ℓ "乑") ∷
   rw⁻ 81 q6 ∷
   re 80 1 (ℓ "丼丠丼") ∷
   rw 82 q10 ∷
   re 79 1 (ℓ "丼丠丼") ∷
   rw 81 q10 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q10 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q10 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q10 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q10 ∷
   re 74 1 (ℓ "丼临丼") ∷
   rw 76 q10 ∷
   rw 73 q29 ∷
   re 72 1 (ℓ "丼丠丼") ∷
   rw 74 q10 ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 73 q10 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q10 ∷
   rw 69 q30 ∷
   rw 68 q1 ∷
   re 69 3 (ℓ "丧") ∷
   rw 67 q1 ∷
   re 68 3 (ℓ "丧") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "丧") ∷
   rw 65 q1 ∷
   re 66 3 (ℓ "丧") ∷
   rw 64 q1 ∷
   re 65 3 (ℓ "丧") ∷
   rw 63 q1 ∷
   re 64 3 (ℓ "丧") ∷
   rw 62 q1 ∷
   re 63 3 (ℓ "丧") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "丧") ∷
   rw 60 q1 ∷
   re 61 3 (ℓ "丧") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "乄") ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q1 ∷
   re 55 3 (ℓ "丧") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "丧") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "丧") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "丧") ∷
   rw 50 q1 ∷
   re 51 3 (ℓ "丧") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "丧") ∷
   rw 48 q1 ∷
   re 49 3 (ℓ "丧") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "丧") ∷
   rw 46 q1 ∷
   re 47 3 (ℓ "丧") ∷
   rw 45 q1 ∷
   re 46 3 (ℓ "丧") ∷
   rw 44 q1 ∷
   re 45 3 (ℓ "丧") ∷
   rw 43 q1 ∷
   re 44 3 (ℓ "丧") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "丧") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "丧") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "丧") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "丧") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "丧") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "丧") ∷
   rw 36 q30 ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "丧") ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "丧") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "丧") ∷
   rw 32 q1 ∷ []) Eq.refl
