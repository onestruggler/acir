{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D182 (W : Ws) where

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
  q2 = wE 479 W
  q3 : Eqn
  q3 = wE 22 W
  q4 : Eqn
  q4 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = wE 23 W
  q6 : Eqn
  q6 = wE 478 W
  q7 : Eqn
  q7 = wE 14 W
  q8 : Eqn
  q8 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q9 : Eqn
  q9 = wE 50 W
  q10 : Eqn
  q10 = wE 343 W
  q11 : Eqn
  q11 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q12 : Eqn
  q12 = wE 49 W
  q13 : Eqn
  q13 = wE 51 W
  q14 : Eqn
  q14 = wE 20 W
  q15 : Eqn
  q15 = wE 364 W
  q16 : Eqn
  q16 = wE 369 W
  q17 : Eqn
  q17 = wE 157 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q20 : Eqn
  q20 = wE 1 W
  q21 : Eqn
  q21 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q22 : Eqn
  q22 = wE 336 W
  q23 : Eqn
  q23 = wE 71 W
  q24 : Eqn
  q24 = wE 72 W
  q25 : Eqn
  q25 = wE 3 W
  q26 : Eqn
  q26 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q27 : Eqn
  q27 = wE 386 W
  q28 : Eqn
  q28 = wE 378 W
  q29 : Eqn
  q29 = wE 372 W

-- AXIOM LF @2301 part1: 500 steps
lem-AXIOM-LF-at2301-part1 : ⟪ (ℓ "丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丼丼丠丼丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏並丼") ⟫ʷ ≈ ⟪ (ℓ "丼並中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乏乄乏乏乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑乏並丼") ⟫ʷ
lem-AXIOM-LF-at2301-part1 = derive (ℓ "丼並乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丼丼丠丼丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏並丼") (ℓ "丼並中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乏乄乏乏乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑乏並丼")
  (re 33 3 (ℓ "丧") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "乄") ∷
   rw 28 q2 ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "丧") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "丧") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "丧") ∷
   re 24 1 (ℓ "乏丼临丼乏") ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "乑") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "丧") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "乄") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "丧") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "丧") ∷
   rw 19 q6 ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "丧") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "丧") ∷
   rw 16 q1 ∷
   re 17 3 (ℓ "丧") ∷
   rw 15 q1 ∷
   re 16 3 (ℓ "丧") ∷
   rw 14 q1 ∷
   re 15 3 (ℓ "丧") ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "丧") ∷
   rw 12 q2 ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "乄") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "丧") ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "丧") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q7 ∷
   re 5 1 (ℓ "丼临丼") ∷
   rw 7 q7 ∷
   re 4 1 (ℓ "丼丠丼") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乄") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丧") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乄") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乄") ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "丼临丼") ∷
   rw 10 q7 ∷
   rw 11 q10 ∷
   re 13 1 (ℓ "丼临丼") ∷
   rw 12 q7 ∷
   rw 13 q10 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q7 ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 15 q7 ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q7 ∷
   re 18 1 (ℓ "丼临丼") ∷
   rw 17 q7 ∷
   rw 18 q10 ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q7 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q7 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q7 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q7 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q7 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q7 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q7 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q7 ∷
   re 29 1 (ℓ "丼临丼") ∷
   rw 28 q7 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q7 ∷
   re 31 1 (ℓ "丼临丼") ∷
   rw 30 q7 ∷
   re 32 1 (ℓ "丼临丼") ∷
   rw 31 q7 ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q11 ∷
   rw 33 q12 ∷
   rw 34 q9 ∷
   rw 35 q13 ∷
   rw 36 q9 ∷
   rw 37 q14 ∷
   rw 38 q11 ∷
   rw 39 q15 ∷
   rw 32 q16 ∷
   re 32 8 (ℓ "乨") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丧") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "丧") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乄") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "丧") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "丧") ∷
   rw 39 q17 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q3 ∷
   rw⁻ 42 q18 ∷
   rw 43 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   rw⁻ 43 q18 ∷
   rw 44 q5 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   rw⁻ 44 q18 ∷
   rw 45 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   rw⁻ 45 q18 ∷
   rw 46 q5 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   rw⁻ 46 q18 ∷
   rw 47 q5 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   rw⁻ 47 q18 ∷
   rw 48 q5 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼临丼乏") ∷
   rw 46 q3 ∷
   rw⁻ 48 q4 ∷
   rw 49 q5 ∷
   re 46 5 (ℓ "乑") ∷
   rw 47 q19 ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q3 ∷
   rw⁻ 50 q18 ∷
   rw 51 q5 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   rw⁻ 51 q18 ∷
   rw 52 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q3 ∷
   rw⁻ 52 q18 ∷
   rw 53 q5 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q3 ∷
   rw⁻ 53 q18 ∷
   rw 54 q5 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q3 ∷
   rw⁻ 54 q18 ∷
   rw 55 q5 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q3 ∷
   rw⁻ 55 q18 ∷
   rw 56 q5 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q3 ∷
   rw⁻ 56 q18 ∷
   rw 57 q5 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q3 ∷
   rw⁻ 57 q18 ∷
   rw 58 q5 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q3 ∷
   rw⁻ 58 q18 ∷
   rw 59 q5 ∷
   re 56 5 (ℓ "中") ∷
   rw 57 q17 ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q3 ∷
   rw⁻ 60 q18 ∷
   rw 61 q5 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q3 ∷
   rw⁻ 61 q18 ∷
   rw 62 q5 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q3 ∷
   rw⁻ 62 q18 ∷
   rw 63 q5 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q3 ∷
   rw⁻ 63 q4 ∷
   rw 64 q5 ∷
   re 61 5 (ℓ "乑") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q3 ∷
   rw⁻ 64 q18 ∷
   rw 65 q5 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q3 ∷
   rw⁻ 65 q18 ∷
   rw 66 q5 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 64 q11 ∷
   rw 65 q12 ∷
   rw 66 q9 ∷
   rw 67 q13 ∷
   rw 68 q9 ∷
   rw 69 q14 ∷
   rw 70 q11 ∷
   rw 71 q15 ∷
   rw 64 q16 ∷
   re 64 8 (ℓ "乨") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "丧") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "丧") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乄") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "丧") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乄") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "乄") ∷
   rw 71 q17 ∷
   re 73 1 (ℓ "乏丼临丼乏") ∷
   rw 72 q3 ∷
   rw⁻ 74 q4 ∷
   rw 75 q5 ∷
   re 72 5 (ℓ "乑") ∷
   rw 73 q19 ∷
   re 75 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q3 ∷
   rw⁻ 76 q4 ∷
   rw 77 q5 ∷
   re 74 5 (ℓ "乑") ∷
   rw 75 q19 ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q3 ∷
   rw⁻ 78 q18 ∷
   rw 79 q5 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q3 ∷
   rw⁻ 79 q18 ∷
   rw 80 q5 ∷
   re 77 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q3 ∷
   rw⁻ 80 q18 ∷
   rw 81 q5 ∷
   re 78 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼临丼乏") ∷
   rw 79 q3 ∷
   rw⁻ 81 q4 ∷
   rw 82 q5 ∷
   re 79 5 (ℓ "乑") ∷
   rw 80 q19 ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q3 ∷
   rw⁻ 83 q18 ∷
   rw 84 q5 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q3 ∷
   rw⁻ 84 q18 ∷
   rw 85 q5 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q3 ∷
   rw⁻ 85 q18 ∷
   rw 86 q5 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q3 ∷
   rw⁻ 86 q18 ∷
   rw 87 q5 ∷
   re 84 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q3 ∷
   rw⁻ 87 q18 ∷
   rw 88 q5 ∷
   re 85 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q3 ∷
   rw⁻ 88 q18 ∷
   rw 89 q5 ∷
   re 86 5 (ℓ "中") ∷
   rw 87 q17 ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q3 ∷
   rw⁻ 90 q18 ∷
   rw 91 q5 ∷
   re 88 5 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q3 ∷
   rw⁻ 91 q18 ∷
   rw 92 q5 ∷
   re 89 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 90 q3 ∷
   rw⁻ 92 q4 ∷
   rw 93 q5 ∷
   re 90 5 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q3 ∷
   rw⁻ 93 q18 ∷
   rw 94 q5 ∷
   re 91 5 (ℓ "中") ∷
   re 93 1 (ℓ "乏丼临丼乏") ∷
   rw 92 q3 ∷
   rw⁻ 94 q4 ∷
   rw 95 q5 ∷
   re 92 5 (ℓ "乑") ∷
   re 94 1 (ℓ "乏丼临丼乏") ∷
   rw 93 q3 ∷
   rw⁻ 95 q4 ∷
   rw 96 q5 ∷
   re 93 5 (ℓ "乑") ∷
   rw 94 q7 ∷
   rw 4 q20 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q18 ∷
   rw⁻ 14 q18 ∷
   rw⁻ 15 q18 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q18 ∷
   rw⁻ 19 q18 ∷
   rw⁻ 20 q18 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 22 q18 ∷
   rw⁻ 23 q18 ∷
   rw 26 q20 ∷
   re 24 3 (ℓ "乓") ∷
   rw⁻ 25 q18 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   re 32 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 31 q22 ∷
   rw 32 q23 ∷
   rw 35 q20 ∷
   re 33 3 (ℓ "乀") ∷
   rw 34 q24 ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "乀") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q25 ∷
   rw 37 q22 ∷
   rw⁻ 38 q26 ∷
   rw 31 q27 ∷
   re 31 8 (ℓ "乥") ∷
   rw 34 q20 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q20 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q20 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "乑") ∷
   rw 38 q20 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q20 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q28 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q25 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q25 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q25 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q25 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q25 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q25 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw 45 q25 ∷
   rw 46 q29 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q25 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q25 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q25 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q25 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q25 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q25 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q25 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 54 q25 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 55 q25 ∷
   rw 56 q28 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q25 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 58 q25 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q25 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 60 q25 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q25 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q25 ∷
   re 64 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 63 q22 ∷
   rw 64 q23 ∷
   rw 67 q20 ∷
   re 65 3 (ℓ "乀") ∷
   rw 66 q24 ∷
   rw 69 q20 ∷
   re 67 3 (ℓ "乀") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q25 ∷
   rw 69 q22 ∷
   rw⁻ 70 q26 ∷
   rw 63 q27 ∷
   re 63 8 (ℓ "乥") ∷
   rw 66 q20 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q20 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q20 ∷
   re 66 3 (ℓ "乑") ∷
   rw 69 q20 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q20 ∷ []) Eq.refl
