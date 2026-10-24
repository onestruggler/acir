{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D211 (W : Ws) where

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
  q2 = wE 22 W
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 23 W
  q5 : Eqn
  q5 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q6 : Eqn
  q6 = wE 14 W
  q7 : Eqn
  q7 = wE 477 W
  q8 : Eqn
  q8 = wE 478 W
  q9 : Eqn
  q9 = wE 479 W
  q10 : Eqn
  q10 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q11 : Eqn
  q11 = wE 50 W
  q12 : Eqn
  q12 = wE 343 W
  q13 : Eqn
  q13 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q14 : Eqn
  q14 = wE 49 W
  q15 : Eqn
  q15 = wE 51 W
  q16 : Eqn
  q16 = wE 20 W
  q17 : Eqn
  q17 = wE 364 W
  q18 : Eqn
  q18 = wE 369 W
  q19 : Eqn
  q19 = wE 157 W
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))

-- AXIOM LF @0213: 464 steps
lem-AXIOM-LF-at0213 : ⟪ (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") ⟫ʷ ≈ ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中乨丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-AXIOM-LF-at0213 = derive (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临乨丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中乨丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 80 q1 ∷
   re 79 1 (ℓ "乏丼临丼乏") ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw 79 q4 ∷
   re 80 5 (ℓ "乑") ∷
   rw⁻ 78 q5 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q6 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q6 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q6 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 76 q6 ∷
   re 73 1 (ℓ "丼丠丼") ∷
   rw 75 q6 ∷
   re 72 1 (ℓ "丼丠丼") ∷
   rw 74 q6 ∷
   re 71 1 (ℓ "丼临丼") ∷
   rw 73 q6 ∷
   rw 70 q7 ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 71 q6 ∷
   re 68 1 (ℓ "丼丠丼") ∷
   rw 70 q6 ∷
   re 67 1 (ℓ "丼丠丼") ∷
   rw 69 q6 ∷
   rw 66 q8 ∷
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
   re 60 3 (ℓ "丧") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "丧") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "丧") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "乄") ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
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
   rw 36 q1 ∷
   re 37 3 (ℓ "丧") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "丧") ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "丧") ∷
   rw 33 q8 ∷
   rw 32 q1 ∷
   re 33 3 (ℓ "丧") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "丧") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "丧") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "丧") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "乄") ∷
   rw 25 q9 ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "丧") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "丧") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "丧") ∷
   re 21 1 (ℓ "乏丼临丼乏") ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "乑") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "丧") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "乄") ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "丧") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "丧") ∷
   rw 16 q8 ∷
   rw 15 q1 ∷
   re 16 3 (ℓ "丧") ∷
   rw 14 q1 ∷
   re 15 3 (ℓ "丧") ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "丧") ∷
   rw 12 q1 ∷
   re 13 3 (ℓ "丧") ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "丧") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "丧") ∷
   rw 9 q9 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "乄") ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "丧") ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "丧") ∷
   rw 5 q1 ∷
   re 6 3 (ℓ "丧") ∷
   rw 4 q8 ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 5 q6 ∷
   re 2 1 (ℓ "丼临丼") ∷
   rw 4 q6 ∷
   re 1 1 (ℓ "丼丠丼") ∷
   rw 3 q6 ∷
   re 0 1 (ℓ "丼丠丼") ∷
   rw 2 q6 ∷
   rw 1 q10 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乄") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乄") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乄") ∷
   rw 6 q11 ∷
   re 8 1 (ℓ "丼临丼") ∷
   rw 7 q6 ∷
   rw 8 q12 ∷
   re 10 1 (ℓ "丼临丼") ∷
   rw 9 q6 ∷
   rw 10 q12 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q6 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q6 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q6 ∷
   re 15 1 (ℓ "丼临丼") ∷
   rw 14 q6 ∷
   rw 15 q12 ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q6 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q6 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q6 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q6 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q6 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q6 ∷
   rw 22 q11 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q6 ∷
   re 26 1 (ℓ "丼临丼") ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "丼临丼") ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "丼临丼") ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q11 ∷
   rw 32 q15 ∷
   rw 33 q11 ∷
   rw 34 q16 ∷
   rw 35 q13 ∷
   rw 36 q17 ∷
   rw 29 q18 ∷
   re 29 8 (ℓ "乨") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丧") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丧") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乄") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丧") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "丧") ∷
   rw 36 q19 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   rw⁻ 39 q20 ∷
   rw 40 q4 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q2 ∷
   rw⁻ 40 q20 ∷
   rw 41 q4 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q2 ∷
   rw⁻ 41 q20 ∷
   rw 42 q4 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q2 ∷
   rw⁻ 42 q20 ∷
   rw 43 q4 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q2 ∷
   rw⁻ 43 q20 ∷
   rw 44 q4 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q2 ∷
   rw⁻ 44 q20 ∷
   rw 45 q4 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q4 ∷
   re 43 5 (ℓ "乑") ∷
   rw 44 q5 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q2 ∷
   rw⁻ 47 q20 ∷
   rw 48 q4 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q2 ∷
   rw⁻ 48 q20 ∷
   rw 49 q4 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q2 ∷
   rw⁻ 49 q20 ∷
   rw 50 q4 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q2 ∷
   rw⁻ 50 q20 ∷
   rw 51 q4 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q2 ∷
   rw⁻ 51 q20 ∷
   rw 52 q4 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   rw⁻ 52 q20 ∷
   rw 53 q4 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q2 ∷
   rw⁻ 53 q20 ∷
   rw 54 q4 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q2 ∷
   rw⁻ 54 q20 ∷
   rw 55 q4 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q2 ∷
   rw⁻ 55 q20 ∷
   rw 56 q4 ∷
   re 53 5 (ℓ "中") ∷
   rw 54 q19 ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q2 ∷
   rw⁻ 57 q20 ∷
   rw 58 q4 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q2 ∷
   rw⁻ 58 q20 ∷
   rw 59 q4 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q2 ∷
   rw⁻ 59 q20 ∷
   rw 60 q4 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q2 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 58 5 (ℓ "乑") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q2 ∷
   rw⁻ 61 q20 ∷
   rw 62 q4 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q2 ∷
   rw⁻ 62 q20 ∷
   rw 63 q4 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 61 q13 ∷
   rw 62 q14 ∷
   rw 63 q11 ∷
   rw 64 q15 ∷
   rw 65 q11 ∷
   rw 66 q16 ∷
   rw 67 q13 ∷
   rw 68 q17 ∷
   rw 61 q18 ∷
   re 61 8 (ℓ "乨") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "丧") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "丧") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乄") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "丧") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乄") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乄") ∷
   rw 68 q19 ∷
   re 70 1 (ℓ "乏丼临丼乏") ∷
   rw 69 q2 ∷
   rw⁻ 71 q3 ∷
   rw 72 q4 ∷
   re 69 5 (ℓ "乑") ∷
   rw 70 q5 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 71 q2 ∷
   rw⁻ 73 q3 ∷
   rw 74 q4 ∷
   re 71 5 (ℓ "乑") ∷
   rw 72 q5 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q2 ∷
   rw⁻ 75 q20 ∷
   rw 76 q4 ∷
   re 73 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q2 ∷
   rw⁻ 76 q20 ∷
   rw 77 q4 ∷
   re 74 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q2 ∷
   rw⁻ 77 q20 ∷
   rw 78 q4 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼临丼乏") ∷
   rw 76 q2 ∷
   rw⁻ 78 q3 ∷
   rw 79 q4 ∷
   re 76 5 (ℓ "乑") ∷
   rw 77 q5 ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q2 ∷
   rw⁻ 80 q20 ∷
   rw 81 q4 ∷
   re 78 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q2 ∷
   rw⁻ 81 q20 ∷
   rw 82 q4 ∷
   re 79 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q2 ∷
   rw⁻ 82 q20 ∷
   rw 83 q4 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q2 ∷
   rw⁻ 83 q20 ∷
   rw 84 q4 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q2 ∷
   rw⁻ 84 q20 ∷
   rw 85 q4 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   rw⁻ 85 q20 ∷
   rw 86 q4 ∷
   re 83 5 (ℓ "中") ∷
   rw 84 q19 ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q2 ∷
   rw⁻ 87 q20 ∷
   rw 88 q4 ∷
   re 85 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q2 ∷
   rw⁻ 88 q20 ∷
   rw 89 q4 ∷
   re 86 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼临丼乏") ∷
   rw 87 q2 ∷
   rw⁻ 89 q3 ∷
   rw 90 q4 ∷
   re 87 5 (ℓ "乑") ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q2 ∷
   rw⁻ 90 q20 ∷
   rw 91 q4 ∷
   re 88 5 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q2 ∷
   rw⁻ 91 q3 ∷
   rw 92 q4 ∷
   re 89 5 (ℓ "乑") ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 90 q2 ∷
   rw⁻ 92 q3 ∷
   rw 93 q4 ∷
   re 90 5 (ℓ "乑") ∷
   rw 91 q6 ∷ []) Eq.refl
