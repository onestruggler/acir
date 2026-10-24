{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D428 (W : Ws) where

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
  q1 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q2 : Eqn
  q2 = wE 23 W
  q3 : Eqn
  q3 = wE 22 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 14 W
  q7 : Eqn
  q7 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = wE 338 W
  q10 : Eqn
  q10 = wE 343 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 378 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = wE 372 W
  q15 : Eqn
  q15 = wE 151 W
  q16 : Eqn
  q16 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = wE 114 W

-- hyb sym 23 @0321 part1: 500 steps
lem-hyb-sym-23-at0321-part1 : ⟪ (ℓ "丼乏丧丧乄丧乌中中中乑业中中中中乏丼乏丠丼乏中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丼乏丼") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丼丼丠丼丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丼") ⟫ʷ
lem-hyb-sym-23-at0321-part1 = derive (ℓ "丼乏丧丧乄丧乌中中中乑业中中中中乏丼乏丠丼乏中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丼乏丼") (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丼丼丠丼丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丼")
  (rw⁻ 18 q1 ∷
   rw 19 q2 ∷
   re 16 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q3 ∷
   rw⁻ 19 q1 ∷
   rw 20 q2 ∷
   re 17 5 (ℓ "中") ∷
   rw 18 q4 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q3 ∷
   rw⁻ 21 q1 ∷
   rw 22 q2 ∷
   re 19 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q3 ∷
   rw⁻ 22 q1 ∷
   rw 23 q2 ∷
   re 20 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q3 ∷
   rw⁻ 23 q5 ∷
   rw 24 q2 ∷
   re 21 5 (ℓ "乑") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q3 ∷
   rw⁻ 24 q1 ∷
   rw 25 q2 ∷
   re 22 5 (ℓ "中") ∷
   re 24 1 (ℓ "丼临丼") ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   rw⁻ 26 q1 ∷
   rw 27 q2 ∷
   re 24 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   rw⁻ 27 q1 ∷
   rw 28 q2 ∷
   re 25 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   rw⁻ 28 q1 ∷
   rw 29 q2 ∷
   re 26 5 (ℓ "中") ∷
   rw 27 q7 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 28 q3 ∷
   rw⁻ 30 q5 ∷
   rw 31 q2 ∷
   re 28 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q3 ∷
   rw⁻ 31 q1 ∷
   rw 32 q2 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q3 ∷
   rw⁻ 32 q1 ∷
   rw 33 q2 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q3 ∷
   rw⁻ 33 q1 ∷
   rw 34 q2 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q3 ∷
   rw⁻ 34 q1 ∷
   rw 35 q2 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q3 ∷
   rw⁻ 35 q1 ∷
   rw 36 q2 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q3 ∷
   rw⁻ 36 q1 ∷
   rw 37 q2 ∷
   re 34 5 (ℓ "中") ∷
   rw 35 q4 ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q3 ∷
   rw⁻ 38 q1 ∷
   rw 39 q2 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   rw⁻ 39 q1 ∷
   rw 40 q2 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q3 ∷
   rw⁻ 40 q1 ∷
   rw 41 q2 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q3 ∷
   rw⁻ 41 q1 ∷
   rw 42 q2 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q3 ∷
   rw⁻ 42 q1 ∷
   rw 43 q2 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   rw⁻ 43 q1 ∷
   rw 44 q2 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   rw⁻ 44 q1 ∷
   rw 45 q2 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   rw⁻ 45 q1 ∷
   rw 46 q2 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   rw⁻ 46 q1 ∷
   rw 47 q2 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   rw⁻ 47 q1 ∷
   rw 48 q2 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q3 ∷
   rw⁻ 48 q1 ∷
   rw 49 q2 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q3 ∷
   rw⁻ 49 q1 ∷
   rw 50 q2 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q3 ∷
   rw⁻ 50 q1 ∷
   rw 51 q2 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   rw⁻ 51 q1 ∷
   rw 52 q2 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q3 ∷
   rw⁻ 52 q1 ∷
   rw 53 q2 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q3 ∷
   rw⁻ 53 q1 ∷
   rw 54 q2 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q3 ∷
   rw⁻ 54 q1 ∷
   rw 55 q2 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q3 ∷
   rw⁻ 55 q1 ∷
   rw 56 q2 ∷
   re 53 5 (ℓ "中") ∷
   rw 54 q7 ∷
   rw 55 q7 ∷
   rw 56 q7 ∷
   rw 57 q7 ∷
   re 59 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q3 ∷
   rw⁻ 60 q5 ∷
   rw 61 q2 ∷
   re 58 5 (ℓ "乑") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q3 ∷
   rw⁻ 61 q1 ∷
   rw 62 q2 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q3 ∷
   rw⁻ 62 q1 ∷
   rw 63 q2 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q3 ∷
   rw⁻ 63 q1 ∷
   rw 64 q2 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q3 ∷
   rw⁻ 64 q1 ∷
   rw 65 q2 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q3 ∷
   rw⁻ 65 q1 ∷
   rw 66 q2 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q3 ∷
   rw⁻ 66 q1 ∷
   rw 67 q2 ∷
   re 64 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q3 ∷
   rw⁻ 67 q1 ∷
   rw 68 q2 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q3 ∷
   rw⁻ 68 q1 ∷
   rw 69 q2 ∷
   re 66 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q3 ∷
   rw⁻ 69 q1 ∷
   rw 70 q2 ∷
   re 67 5 (ℓ "中") ∷
   rw 68 q4 ∷
   rw 71 q8 ∷
   re 69 3 (ℓ "丧") ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "丧") ∷
   rw 73 q8 ∷
   re 71 3 (ℓ "丧") ∷
   rw 72 q9 ∷
   rw 75 q8 ∷
   re 73 3 (ℓ "乄") ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "丧") ∷
   rw 77 q8 ∷
   re 75 3 (ℓ "丧") ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "丧") ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "丧") ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "丧") ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "丧") ∷
   rw 80 q10 ∷
   re 82 1 (ℓ "丼临丼") ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   rw 3 q11 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q13 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q13 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q13 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q13 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q13 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q13 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q13 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q13 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q13 ∷
   rw 17 q12 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 18 q13 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 19 q13 ∷
   re 21 1 (ℓ "乏乄乏") ∷
   rw 20 q13 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 21 q13 ∷
   rw⁻ 22 q5 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 23 q13 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 24 q13 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 25 q13 ∷
   rw 26 q14 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 27 q13 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 28 q13 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 29 q13 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q13 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q13 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q13 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 33 q13 ∷
   rw 34 q12 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q13 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q13 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q13 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q13 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q13 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q13 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q13 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q13 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q13 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q13 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q13 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q13 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q13 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q13 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q13 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q13 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q13 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q13 ∷
   rw 53 q14 ∷
   rw 54 q14 ∷
   rw 55 q14 ∷
   rw 56 q14 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 57 q13 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 58 q13 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q13 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q13 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q13 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q13 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q13 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 64 q13 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 65 q13 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 66 q13 ∷
   rw 67 q12 ∷
   rw 70 q11 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q11 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q11 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q15 ∷
   rw 74 q11 ∷
   re 72 3 (ℓ "乑") ∷
   rw 75 q11 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q11 ∷
   re 74 3 (ℓ "中") ∷
   rw 77 q11 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q11 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q11 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q11 ∷
   re 78 3 (ℓ "中") ∷
   rw⁻ 79 q16 ∷
   rw⁻ 80 q5 ∷
   rw 81 q13 ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q3 ∷
   rw⁻ 2 q1 ∷
   rw 3 q2 ∷
   re 0 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 1 q3 ∷
   rw⁻ 3 q1 ∷
   rw 4 q2 ∷
   re 1 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丼临丼乏") ∷
   rw 2 q3 ∷
   rw⁻ 4 q5 ∷
   rw 5 q2 ∷
   re 2 5 (ℓ "乑") ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 3 q3 ∷
   rw⁻ 5 q1 ∷
   rw 6 q2 ∷
   re 3 5 (ℓ "中") ∷
   rw 4 q17 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q6 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 6 q6 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q6 ∷
   re 9 1 (ℓ "丼临丼") ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 10 q6 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q6 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q6 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q6 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q6 ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 15 q6 ∷
   rw 16 q17 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q6 ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q6 ∷
   re 20 1 (ℓ "丼临丼") ∷
   rw 19 q6 ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q6 ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "乄") ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q6 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q6 ∷
   rw 25 q10 ∷
   re 27 1 (ℓ "丼临丼") ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q6 ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q6 ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q6 ∷
   rw 33 q17 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q6 ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q6 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q6 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q6 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q6 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q6 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q6 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q6 ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q6 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q6 ∷
   re 47 1 (ℓ "丼丠丼") ∷ []) Eq.refl
