{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD665 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D665 (W : Ws) (Sᴰ : SD665) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-hyb-sym-23 : St 1758
  lem-hyb-sym-23 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 12 W
  q2 : Eqn
  q2 = wE 479 W
  q3 : Eqn
  q3 = wE 22 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 23 W
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q8 : Eqn
  q8 = wE 78 W
  q9 : Eqn
  q9 = wE 14 W
  q10 : Eqn
  q10 = wE 477 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 476 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = wE 464 W
  q15 : Eqn
  q15 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = wE 478 W
  q17 : Eqn
  q17 = sE 1758 lem-hyb-sym-23
  q18 : Eqn
  q18 = wE 157 W

-- hyb sym 23 @0321 part0: 500 steps
lem-hyb-sym-23-at0321-part0 : ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ ≈ ⟪ (ℓ "丼乏丧丧乄丧乌中中中乑业中中中中乏丼乏丠丼乏中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丼乏丼") ⟫ʷ
lem-hyb-sym-23-at0321-part0 = derive (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") (ℓ "丼乏丧丧乄丧乌中中中乑业中中中中乏丼乏丠丼乏中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丼乏丼")
  (rw 80 q1 ∷
   rw 79 q1 ∷
   re 80 3 (ℓ "乄") ∷
   rw 78 q2 ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   rw 77 q5 ∷
   re 78 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   rw 76 q5 ∷
   re 77 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 75 q5 ∷
   re 76 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 74 q5 ∷
   re 75 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   rw 73 q5 ∷
   re 74 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   rw 72 q5 ∷
   re 73 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q3 ∷
   rw 73 q6 ∷
   rw 71 q5 ∷
   re 72 5 (ℓ "乑") ∷
   rw⁻ 70 q7 ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   rw 69 q5 ∷
   re 70 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   rw 68 q5 ∷
   re 69 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "中") ∷
   rw 66 q8 ∷
   re 65 1 (ℓ "丼丠丼") ∷
   rw 67 q9 ∷
   re 64 1 (ℓ "丼丠丼") ∷
   rw 66 q9 ∷
   re 63 1 (ℓ "丼丠丼") ∷
   rw 65 q9 ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 64 q9 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 63 q9 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 62 q9 ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 61 q9 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 60 q9 ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 59 q9 ∷
   re 56 1 (ℓ "丼临丼") ∷
   rw 58 q9 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 53 q9 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 52 q9 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 51 q9 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 50 q9 ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 49 q9 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 48 q9 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 47 q9 ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 46 q9 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 45 q9 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 44 q9 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 43 q9 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 42 q9 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 41 q9 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 40 q9 ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 39 q9 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 38 q9 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 37 q9 ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 36 q9 ∷
   rw 33 q8 ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 34 q9 ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 33 q9 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 32 q9 ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 31 q9 ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 30 q9 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 29 q9 ∷
   re 26 1 (ℓ "丼临丼") ∷
   rw 28 q9 ∷
   rw 25 q10 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 26 q9 ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 25 q9 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 24 q9 ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "乄") ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 22 q9 ∷
   re 19 1 (ℓ "丼临丼") ∷
   rw 21 q9 ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 20 q9 ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 19 q9 ∷
   rw 16 q8 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q9 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q9 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q9 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q9 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q9 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q9 ∷
   rw 9 q10 ∷
   re 8 1 (ℓ "丼临丼") ∷
   rw 10 q9 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q9 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q9 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q9 ∷
   rw 4 q8 ∷
   re 3 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   rw 3 q5 ∷
   re 4 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼临丼乏") ∷
   rw 5 q3 ∷
   rw 4 q6 ∷
   rw 2 q5 ∷
   re 3 5 (ℓ "乑") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 1 q5 ∷
   re 2 5 (ℓ "中") ∷
   re 0 1 (ℓ "乏丼丠丼乏") ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 0 q5 ∷
   re 1 5 (ℓ "中") ∷
   rw 81 q11 ∷
   rw 80 q11 ∷
   re 81 3 (ℓ "乑") ∷
   rw 79 q12 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q13 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q13 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q13 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q13 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q13 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q13 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 74 q13 ∷
   rw 71 q14 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q13 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q13 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q13 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 69 q13 ∷
   rw 66 q4 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q4 ∷
   rw 62 q4 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw 59 q4 ∷
   rw 58 q4 ∷
   rw 57 q6 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q4 ∷
   rw 39 q4 ∷
   rw 38 q4 ∷
   rw 37 q4 ∷
   rw 36 q4 ∷
   rw 35 q4 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 36 q13 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q6 ∷
   rw 26 q15 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q11 ∷
   re 23 3 (ℓ "乑") ∷
   rw 21 q4 ∷
   rw 20 q6 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 19 q13 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q15 ∷
   rw 9 q6 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 7 q13 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q13 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q13 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q13 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q13 ∷
   rw 82 q1 ∷
   re 81 1 (ℓ "乏丼临丼乏") ∷
   rw 84 q3 ∷
   rw 83 q6 ∷
   rw 81 q5 ∷
   re 82 5 (ℓ "乑") ∷
   rw⁻ 80 q7 ∷
   re 79 1 (ℓ "丼丠丼") ∷
   rw 81 q9 ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 80 q9 ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 79 q9 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 78 q9 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 77 q9 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 76 q9 ∷
   re 73 1 (ℓ "丼临丼") ∷
   rw 75 q9 ∷
   rw 72 q10 ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 73 q9 ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 72 q9 ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 71 q9 ∷
   rw 68 q16 ∷
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
   re 60 3 (ℓ "丧") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "乄") ∷
   rw 57 q2 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   rw 54 q2 ∷
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
   rw 36 q1 ∷
   re 37 3 (ℓ "丧") ∷
   rw 35 q16 ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "丧") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "丧") ∷
   rw 32 q1 ∷
   re 33 3 (ℓ "丧") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "丧") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "丧") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "丧") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "乄") ∷
   rw 27 q2 ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "丧") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "丧") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "丧") ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 26 q3 ∷
   rw 25 q6 ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "乑") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "丧") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "乄") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "丧") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "丧") ∷
   rw 18 q16 ∷
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
   rw 12 q1 ∷
   re 13 3 (ℓ "丧") ∷
   rw 11 q2 ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "乄") ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "丧") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "丧") ∷
   rw 6 q16 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q9 ∷
   re 4 1 (ℓ "丼临丼") ∷
   rw 6 q9 ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 5 q9 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 4 q9 ∷
   rw 3 q17 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乄") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丧") ∷
   rw 6 q18 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q3 ∷
   rw⁻ 9 q4 ∷
   rw 10 q5 ∷
   re 7 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q3 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   re 8 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q3 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   re 9 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 10 q3 ∷
   rw⁻ 12 q6 ∷
   rw 13 q5 ∷
   re 10 5 (ℓ "乑") ∷
   rw 11 q7 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q3 ∷
   rw⁻ 14 q4 ∷
   rw 15 q5 ∷
   re 12 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q3 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   re 13 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q3 ∷
   rw⁻ 16 q4 ∷
   rw 17 q5 ∷
   re 14 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q3 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   re 15 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q3 ∷ []) Eq.refl
