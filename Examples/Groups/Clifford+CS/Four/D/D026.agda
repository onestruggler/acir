{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D026 (W : Ws) where

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
  q2 = wE 476 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = wE 22 W
  q10 : Eqn
  q10 = wE 23 W
  q11 : Eqn
  q11 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q12 : Eqn
  q12 = wE 14 W
  q13 : Eqn
  q13 = wE 477 W
  q14 : Eqn
  q14 = wE 478 W
  q15 : Eqn
  q15 = wE 479 W
  q16 : Eqn
  q16 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q17 : Eqn
  q17 = wE 50 W
  q18 : Eqn
  q18 = wE 343 W
  q19 : Eqn
  q19 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q20 : Eqn
  q20 = wE 49 W
  q21 : Eqn
  q21 = wE 51 W
  q22 : Eqn
  q22 = wE 20 W
  q23 : Eqn
  q23 = wE 364 W
  q24 : Eqn
  q24 = wE 369 W
  q25 : Eqn
  q25 = wE 157 W
  q26 : Eqn
  q26 = wE 336 W
  q27 : Eqn
  q27 = wE 71 W
  q28 : Eqn
  q28 = wE 72 W
  q29 : Eqn
  q29 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q30 : Eqn
  q30 = wE 386 W
  q31 : Eqn
  q31 = wE 378 W
  q32 : Eqn
  q32 = wE 372 W

-- AXIOM LF @0312: 743 steps
lem-AXIOM-LF-at0312 : ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-AXIOM-LF-at0312 = derive (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 80 q1 ∷
   rw 79 q1 ∷
   re 80 3 (ℓ "乑") ∷
   rw 78 q2 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q3 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q3 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q3 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q3 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q3 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q3 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw 73 q3 ∷
   rw 70 q4 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q3 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q3 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q3 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 68 q3 ∷
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
   rw 55 q7 ∷
   rw 54 q7 ∷
   rw 53 q7 ∷
   rw 52 q7 ∷
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
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q3 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "乑") ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 18 q3 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q3 ∷
   rw 81 q8 ∷
   re 80 1 (ℓ "乏丼临丼乏") ∷
   rw 83 q9 ∷
   rw 82 q6 ∷
   rw 80 q10 ∷
   re 81 5 (ℓ "乑") ∷
   rw⁻ 79 q11 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q12 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q12 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q12 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q12 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 76 q12 ∷
   re 73 1 (ℓ "丼丠丼") ∷
   rw 75 q12 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 74 q12 ∷
   rw 71 q13 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q12 ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 71 q12 ∷
   re 68 1 (ℓ "丼丠丼") ∷
   rw 70 q12 ∷
   rw 67 q14 ∷
   rw 66 q8 ∷
   re 67 3 (ℓ "丧") ∷
   rw 65 q8 ∷
   re 66 3 (ℓ "丧") ∷
   rw 64 q8 ∷
   re 65 3 (ℓ "丧") ∷
   rw 63 q8 ∷
   re 64 3 (ℓ "丧") ∷
   rw 62 q8 ∷
   re 63 3 (ℓ "丧") ∷
   rw 61 q8 ∷
   re 62 3 (ℓ "丧") ∷
   rw 60 q8 ∷
   re 61 3 (ℓ "丧") ∷
   rw 59 q8 ∷
   re 60 3 (ℓ "丧") ∷
   rw 58 q8 ∷
   re 59 3 (ℓ "丧") ∷
   rw 57 q8 ∷
   re 58 3 (ℓ "乄") ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q8 ∷
   re 53 3 (ℓ "丧") ∷
   rw 51 q8 ∷
   re 52 3 (ℓ "丧") ∷
   rw 50 q8 ∷
   re 51 3 (ℓ "丧") ∷
   rw 49 q8 ∷
   re 50 3 (ℓ "丧") ∷
   rw 48 q8 ∷
   re 49 3 (ℓ "丧") ∷
   rw 47 q8 ∷
   re 48 3 (ℓ "丧") ∷
   rw 46 q8 ∷
   re 47 3 (ℓ "丧") ∷
   rw 45 q8 ∷
   re 46 3 (ℓ "丧") ∷
   rw 44 q8 ∷
   re 45 3 (ℓ "丧") ∷
   rw 43 q8 ∷
   re 44 3 (ℓ "丧") ∷
   rw 42 q8 ∷
   re 43 3 (ℓ "丧") ∷
   rw 41 q8 ∷
   re 42 3 (ℓ "丧") ∷
   rw 40 q8 ∷
   re 41 3 (ℓ "丧") ∷
   rw 39 q8 ∷
   re 40 3 (ℓ "丧") ∷
   rw 38 q8 ∷
   re 39 3 (ℓ "丧") ∷
   rw 37 q8 ∷
   re 38 3 (ℓ "丧") ∷
   rw 36 q8 ∷
   re 37 3 (ℓ "丧") ∷
   rw 35 q8 ∷
   re 36 3 (ℓ "丧") ∷
   rw 34 q14 ∷
   rw 33 q8 ∷
   re 34 3 (ℓ "丧") ∷
   rw 32 q8 ∷
   re 33 3 (ℓ "丧") ∷
   rw 31 q8 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q8 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q8 ∷
   re 30 3 (ℓ "丧") ∷
   rw 28 q8 ∷
   re 29 3 (ℓ "丧") ∷
   rw 27 q8 ∷
   re 28 3 (ℓ "乄") ∷
   rw 26 q15 ∷
   rw 25 q8 ∷
   re 26 3 (ℓ "丧") ∷
   rw 24 q8 ∷
   re 25 3 (ℓ "丧") ∷
   rw 23 q8 ∷
   re 24 3 (ℓ "丧") ∷
   re 22 1 (ℓ "乏丼临丼乏") ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   rw 22 q10 ∷
   re 23 5 (ℓ "乑") ∷
   rw 21 q8 ∷
   re 22 3 (ℓ "丧") ∷
   rw 20 q8 ∷
   re 21 3 (ℓ "乄") ∷
   rw 19 q8 ∷
   re 20 3 (ℓ "丧") ∷
   rw 18 q8 ∷
   re 19 3 (ℓ "丧") ∷
   rw 17 q14 ∷
   rw 16 q8 ∷
   re 17 3 (ℓ "丧") ∷
   rw 15 q8 ∷
   re 16 3 (ℓ "丧") ∷
   rw 14 q8 ∷
   re 15 3 (ℓ "丧") ∷
   rw 13 q8 ∷
   re 14 3 (ℓ "丧") ∷
   rw 12 q8 ∷
   re 13 3 (ℓ "丧") ∷
   rw 11 q8 ∷
   re 12 3 (ℓ "丧") ∷
   rw 10 q15 ∷
   rw 9 q8 ∷
   re 10 3 (ℓ "乄") ∷
   rw 8 q8 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q8 ∷
   re 8 3 (ℓ "丧") ∷
   rw 6 q8 ∷
   re 7 3 (ℓ "丧") ∷
   rw 5 q14 ∷
   re 4 1 (ℓ "丼丠丼") ∷
   rw 6 q12 ∷
   re 3 1 (ℓ "丼临丼") ∷
   rw 5 q12 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 4 q12 ∷
   re 1 1 (ℓ "丼丠丼") ∷
   rw 3 q12 ∷
   rw 2 q16 ∷
   rw 3 q8 ∷
   re 1 3 (ℓ "丧") ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "丧") ∷
   rw 5 q8 ∷
   re 3 3 (ℓ "乄") ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "丧") ∷
   rw 7 q8 ∷
   re 5 3 (ℓ "乄") ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "乄") ∷
   rw 7 q17 ∷
   re 9 1 (ℓ "丼临丼") ∷
   rw 8 q12 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "丼临丼") ∷
   rw 10 q12 ∷
   rw 11 q18 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q12 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q12 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q12 ∷
   re 16 1 (ℓ "丼临丼") ∷
   rw 15 q12 ∷
   rw 16 q18 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q12 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q12 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q12 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q12 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q12 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q12 ∷
   rw 23 q17 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q12 ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q12 ∷
   re 27 1 (ℓ "丼临丼") ∷
   rw 26 q12 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q12 ∷
   re 29 1 (ℓ "丼临丼") ∷
   rw 28 q12 ∷
   re 30 1 (ℓ "丼临丼") ∷
   rw 29 q12 ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q19 ∷
   rw 31 q20 ∷
   rw 32 q17 ∷
   rw 33 q21 ∷
   rw 34 q17 ∷
   rw 35 q22 ∷
   rw 36 q19 ∷
   rw 37 q23 ∷
   rw 30 q24 ∷
   re 30 8 (ℓ "乨") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "丧") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "乄") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "丧") ∷
   rw 38 q8 ∷
   re 36 3 (ℓ "丧") ∷
   rw 37 q25 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q9 ∷
   rw⁻ 40 q5 ∷
   rw 41 q10 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q9 ∷
   rw⁻ 41 q5 ∷
   rw 42 q10 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q9 ∷
   rw⁻ 42 q5 ∷
   rw 43 q10 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q9 ∷
   rw⁻ 43 q5 ∷
   rw 44 q10 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q9 ∷
   rw⁻ 44 q5 ∷
   rw 45 q10 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q9 ∷
   rw⁻ 45 q5 ∷
   rw 46 q10 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q9 ∷
   rw⁻ 46 q6 ∷
   rw 47 q10 ∷
   re 44 5 (ℓ "乑") ∷
   rw 45 q11 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q9 ∷
   rw⁻ 48 q5 ∷
   rw 49 q10 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q9 ∷
   rw⁻ 49 q5 ∷
   rw 50 q10 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q9 ∷
   rw⁻ 50 q5 ∷
   rw 51 q10 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q9 ∷
   rw⁻ 51 q5 ∷
   rw 52 q10 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q9 ∷
   rw⁻ 52 q5 ∷
   rw 53 q10 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q9 ∷
   rw⁻ 53 q5 ∷
   rw 54 q10 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q9 ∷
   rw⁻ 54 q5 ∷
   rw 55 q10 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q9 ∷
   rw⁻ 55 q5 ∷
   rw 56 q10 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q9 ∷
   rw⁻ 56 q5 ∷
   rw 57 q10 ∷
   re 54 5 (ℓ "中") ∷
   rw 55 q25 ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q9 ∷
   rw⁻ 58 q5 ∷
   rw 59 q10 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q9 ∷
   rw⁻ 59 q5 ∷
   rw 60 q10 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q9 ∷
   rw⁻ 60 q5 ∷
   rw 61 q10 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q9 ∷
   rw⁻ 61 q6 ∷
   rw 62 q10 ∷
   re 59 5 (ℓ "乑") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q9 ∷
   rw⁻ 62 q5 ∷
   rw 63 q10 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q9 ∷
   rw⁻ 63 q5 ∷
   rw 64 q10 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 62 q19 ∷
   rw 63 q20 ∷
   rw 64 q17 ∷
   rw 65 q21 ∷
   rw 66 q17 ∷
   rw 67 q22 ∷
   rw 68 q19 ∷
   rw 69 q23 ∷
   rw 62 q24 ∷
   re 62 8 (ℓ "乨") ∷
   rw 65 q8 ∷
   re 63 3 (ℓ "丧") ∷
   rw 66 q8 ∷
   re 64 3 (ℓ "丧") ∷
   rw 67 q8 ∷
   re 65 3 (ℓ "乄") ∷
   rw 68 q8 ∷
   re 66 3 (ℓ "丧") ∷
   rw 69 q8 ∷
   re 67 3 (ℓ "乄") ∷
   rw 70 q8 ∷
   re 68 3 (ℓ "乄") ∷
   rw 69 q25 ∷
   re 71 1 (ℓ "乏丼临丼乏") ∷
   rw 70 q9 ∷
   rw⁻ 72 q6 ∷
   rw 73 q10 ∷
   re 70 5 (ℓ "乑") ∷
   rw 71 q11 ∷
   re 73 1 (ℓ "乏丼临丼乏") ∷
   rw 72 q9 ∷
   rw⁻ 74 q6 ∷
   rw 75 q10 ∷
   re 72 5 (ℓ "乑") ∷
   rw 73 q11 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q9 ∷
   rw⁻ 76 q5 ∷
   rw 77 q10 ∷
   re 74 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q9 ∷
   rw⁻ 77 q5 ∷
   rw 78 q10 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q9 ∷
   rw⁻ 78 q5 ∷
   rw 79 q10 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼临丼乏") ∷
   rw 77 q9 ∷
   rw⁻ 79 q6 ∷
   rw 80 q10 ∷
   re 77 5 (ℓ "乑") ∷
   rw 78 q11 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q9 ∷
   rw⁻ 81 q5 ∷
   rw 82 q10 ∷
   re 79 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q9 ∷
   rw⁻ 82 q5 ∷
   rw 83 q10 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q9 ∷
   rw⁻ 83 q5 ∷
   rw 84 q10 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q9 ∷
   rw⁻ 84 q5 ∷
   rw 85 q10 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q9 ∷
   rw⁻ 85 q5 ∷
   rw 86 q10 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q9 ∷
   rw⁻ 86 q5 ∷
   rw 87 q10 ∷
   re 84 5 (ℓ "中") ∷
   rw 85 q25 ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q9 ∷
   rw⁻ 88 q5 ∷
   rw 89 q10 ∷
   re 86 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q9 ∷
   rw⁻ 89 q5 ∷
   rw 90 q10 ∷
   re 87 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丼临丼乏") ∷
   rw 88 q9 ∷
   rw⁻ 90 q6 ∷
   rw 91 q10 ∷
   re 88 5 (ℓ "乑") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q9 ∷
   rw⁻ 91 q5 ∷
   rw 92 q10 ∷
   re 89 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 90 q9 ∷
   rw⁻ 92 q6 ∷
   rw 93 q10 ∷
   re 90 5 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丼临丼乏") ∷
   rw 91 q9 ∷
   rw⁻ 93 q6 ∷
   rw 94 q10 ∷
   re 91 5 (ℓ "乑") ∷
   rw 92 q12 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乑") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乓") ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乓") ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 28 q6 ∷
   re 30 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 29 q26 ∷
   rw 30 q27 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乀") ∷
   rw 32 q28 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乀") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q3 ∷
   rw 35 q26 ∷
   rw⁻ 36 q29 ∷
   rw 29 q30 ∷
   re 29 8 (ℓ "乥") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q31 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 43 q3 ∷
   rw 44 q32 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q3 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q3 ∷
   rw 54 q31 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 55 q3 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 56 q3 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q3 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 58 q3 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q3 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 61 q26 ∷
   rw 62 q27 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乀") ∷
   rw 64 q28 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "乀") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q3 ∷
   rw 67 q26 ∷
   rw⁻ 68 q29 ∷
   rw 61 q30 ∷
   re 61 8 (ℓ "乥") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乑") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乑") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q31 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 69 q3 ∷
   rw 70 q32 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q3 ∷
   rw 72 q32 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 73 q3 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q3 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q3 ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw 76 q3 ∷
   rw 77 q32 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 78 q3 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q3 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 80 q3 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 81 q3 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q3 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 83 q3 ∷
   rw 84 q31 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 85 q3 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 86 q3 ∷
   re 88 1 (ℓ "乏乄乏") ∷
   rw 87 q3 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 88 q3 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 89 q3 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 90 q3 ∷
   rw 91 q3 ∷ []) Eq.refl
