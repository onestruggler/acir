{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D179 (W : Ws) where

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
  q1 = wE 14 W
  q2 : Eqn
  q2 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q3 : Eqn
  q3 = wE 49 W
  q4 : Eqn
  q4 = wE 50 W
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 20 W
  q7 : Eqn
  q7 = wE 364 W
  q8 : Eqn
  q8 = wE 369 W
  q9 : Eqn
  q9 = wE 12 W
  q10 : Eqn
  q10 = wE 157 W
  q11 : Eqn
  q11 = wE 22 W
  q12 : Eqn
  q12 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = wE 23 W
  q14 : Eqn
  q14 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
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
  q26 = wE 113 W
  q27 : Eqn
  q27 = wE 338 W

-- AXIOM LF @0321 part1: 500 steps
lem-AXIOM-LF-at0321-part1 : ⟪ (ℓ "丼乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临丼丼临丼乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏丼") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丼丠丼丼临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丼") ⟫ʷ
lem-AXIOM-LF-at0321-part1 = derive (ℓ "丼乏丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临丼丼临丼乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丼乏丼") (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丼丠丼丼临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丼")
  (rw 30 q1 ∷
   re 32 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 31 q2 ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q4 ∷
   rw 36 q6 ∷
   rw 37 q2 ∷
   rw 38 q7 ∷
   rw 31 q8 ∷
   re 31 8 (ℓ "乨") ∷
   rw 34 q9 ∷
   re 32 3 (ℓ "丧") ∷
   rw 35 q9 ∷
   re 33 3 (ℓ "丧") ∷
   rw 36 q9 ∷
   re 34 3 (ℓ "丧") ∷
   rw 37 q9 ∷
   re 35 3 (ℓ "乄") ∷
   rw 38 q9 ∷
   re 36 3 (ℓ "丧") ∷
   rw 39 q9 ∷
   re 37 3 (ℓ "丧") ∷
   rw 38 q10 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q11 ∷
   rw⁻ 41 q12 ∷
   rw 42 q13 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q11 ∷
   rw⁻ 42 q12 ∷
   rw 43 q13 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q11 ∷
   rw⁻ 43 q12 ∷
   rw 44 q13 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q11 ∷
   rw⁻ 44 q12 ∷
   rw 45 q13 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q11 ∷
   rw⁻ 45 q12 ∷
   rw 46 q13 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q11 ∷
   rw⁻ 46 q12 ∷
   rw 47 q13 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼临丼乏") ∷
   rw 45 q11 ∷
   rw⁻ 47 q14 ∷
   rw 48 q13 ∷
   re 45 5 (ℓ "乑") ∷
   rw 46 q15 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q11 ∷
   rw⁻ 49 q12 ∷
   rw 50 q13 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q11 ∷
   rw⁻ 50 q12 ∷
   rw 51 q13 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q11 ∷
   rw⁻ 51 q12 ∷
   rw 52 q13 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q11 ∷
   rw⁻ 52 q12 ∷
   rw 53 q13 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q11 ∷
   rw⁻ 53 q12 ∷
   rw 54 q13 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q11 ∷
   rw⁻ 54 q12 ∷
   rw 55 q13 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q11 ∷
   rw⁻ 55 q12 ∷
   rw 56 q13 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q11 ∷
   rw⁻ 56 q12 ∷
   rw 57 q13 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q11 ∷
   rw⁻ 57 q12 ∷
   rw 58 q13 ∷
   re 55 5 (ℓ "中") ∷
   rw 56 q10 ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q11 ∷
   rw⁻ 59 q12 ∷
   rw 60 q13 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q11 ∷
   rw⁻ 60 q12 ∷
   rw 61 q13 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q11 ∷
   rw⁻ 61 q12 ∷
   rw 62 q13 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼临丼乏") ∷
   rw 60 q11 ∷
   rw⁻ 62 q14 ∷
   rw 63 q13 ∷
   re 60 5 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q11 ∷
   rw⁻ 63 q12 ∷
   rw 64 q13 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q11 ∷
   rw⁻ 64 q12 ∷
   rw 65 q13 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 63 q2 ∷
   rw 64 q3 ∷
   rw 65 q4 ∷
   rw 66 q5 ∷
   rw 67 q4 ∷
   rw 68 q6 ∷
   rw 69 q2 ∷
   rw 70 q7 ∷
   rw 63 q8 ∷
   re 63 8 (ℓ "乨") ∷
   rw 66 q9 ∷
   re 64 3 (ℓ "丧") ∷
   rw 67 q9 ∷
   re 65 3 (ℓ "丧") ∷
   rw 68 q9 ∷
   re 66 3 (ℓ "乄") ∷
   rw 69 q9 ∷
   re 67 3 (ℓ "丧") ∷
   rw 70 q9 ∷
   re 68 3 (ℓ "乄") ∷
   rw 71 q9 ∷
   re 69 3 (ℓ "乄") ∷
   rw 70 q10 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 71 q11 ∷
   rw⁻ 73 q14 ∷
   rw 74 q13 ∷
   re 71 5 (ℓ "乑") ∷
   rw 72 q15 ∷
   re 74 1 (ℓ "乏丼临丼乏") ∷
   rw 73 q11 ∷
   rw⁻ 75 q14 ∷
   rw 76 q13 ∷
   re 73 5 (ℓ "乑") ∷
   rw 74 q15 ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q11 ∷
   rw⁻ 77 q12 ∷
   rw 78 q13 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q11 ∷
   rw⁻ 78 q12 ∷
   rw 79 q13 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q11 ∷
   rw⁻ 79 q12 ∷
   rw 80 q13 ∷
   re 77 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼临丼乏") ∷
   rw 78 q11 ∷
   rw⁻ 80 q14 ∷
   rw 81 q13 ∷
   re 78 5 (ℓ "乑") ∷
   rw 79 q15 ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q11 ∷
   rw⁻ 82 q12 ∷
   rw 83 q13 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q11 ∷
   rw⁻ 83 q12 ∷
   rw 84 q13 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q11 ∷
   rw⁻ 84 q12 ∷
   rw 85 q13 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q11 ∷
   rw⁻ 85 q12 ∷
   rw 86 q13 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q11 ∷
   rw⁻ 86 q12 ∷
   rw 87 q13 ∷
   re 84 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q11 ∷
   rw⁻ 87 q12 ∷
   rw 88 q13 ∷
   re 85 5 (ℓ "中") ∷
   rw 86 q10 ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q11 ∷
   rw⁻ 89 q12 ∷
   rw 90 q13 ∷
   re 87 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q11 ∷
   rw⁻ 90 q12 ∷
   rw 91 q13 ∷
   re 88 5 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q11 ∷
   rw⁻ 91 q14 ∷
   rw 92 q13 ∷
   re 89 5 (ℓ "乑") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q11 ∷
   rw⁻ 92 q12 ∷
   rw 93 q13 ∷
   re 90 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼临丼乏") ∷
   rw 91 q11 ∷
   rw⁻ 93 q14 ∷
   rw 94 q13 ∷
   re 91 5 (ℓ "乑") ∷
   re 93 1 (ℓ "乏丼临丼乏") ∷
   rw 92 q11 ∷
   rw⁻ 94 q14 ∷
   rw 95 q13 ∷
   re 92 5 (ℓ "乑") ∷
   rw 93 q1 ∷
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
   rw⁻ 8 q14 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 12 q12 ∷
   rw⁻ 13 q12 ∷
   rw⁻ 14 q12 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q12 ∷
   rw⁻ 18 q12 ∷
   rw⁻ 19 q12 ∷
   rw⁻ 20 q12 ∷
   rw⁻ 21 q12 ∷
   rw⁻ 22 q12 ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q12 ∷
   rw⁻ 25 q12 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 27 q12 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 29 q14 ∷
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
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q11 ∷
   rw⁻ 2 q12 ∷
   rw 3 q13 ∷
   re 0 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 1 q11 ∷
   rw⁻ 3 q12 ∷
   rw 4 q13 ∷
   re 1 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丼临丼乏") ∷
   rw 2 q11 ∷
   rw⁻ 4 q14 ∷
   rw 5 q13 ∷
   re 2 5 (ℓ "乑") ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 3 q11 ∷
   rw⁻ 5 q12 ∷
   rw 6 q13 ∷
   re 3 5 (ℓ "中") ∷
   re 5 1 (ℓ "乏丼临丼乏") ∷
   rw 4 q11 ∷
   rw⁻ 6 q14 ∷
   rw 7 q13 ∷
   re 4 5 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丼临丼乏") ∷
   rw 5 q11 ∷
   rw⁻ 7 q14 ∷
   rw 8 q13 ∷
   re 5 5 (ℓ "乑") ∷
   rw 6 q26 ∷
   rw 9 q9 ∷
   re 7 3 (ℓ "乄") ∷
   rw 8 q27 ∷
   rw 11 q9 ∷
   re 9 3 (ℓ "乄") ∷
   rw 10 q27 ∷
   rw 13 q9 ∷
   re 11 3 (ℓ "丧") ∷
   rw 14 q9 ∷
   re 12 3 (ℓ "丧") ∷
   rw 15 q9 ∷
   re 13 3 (ℓ "丧") ∷
   rw 16 q9 ∷
   re 14 3 (ℓ "乄") ∷
   rw 15 q27 ∷
   rw 18 q9 ∷
   re 16 3 (ℓ "丧") ∷
   rw 19 q9 ∷
   re 17 3 (ℓ "丧") ∷
   rw 20 q9 ∷
   re 18 3 (ℓ "丧") ∷
   rw 21 q9 ∷
   re 19 3 (ℓ "丧") ∷
   rw 22 q9 ∷
   re 20 3 (ℓ "丧") ∷
   rw 23 q9 ∷
   re 21 3 (ℓ "丧") ∷
   rw 22 q26 ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "丧") ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "丧") ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "乄") ∷
   rw 28 q9 ∷ []) Eq.refl
