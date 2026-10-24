{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD669 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D669 (W : Ws) (Sᴰ : SD669) where

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
  q10 = sE 1758 lem-hyb-sym-23
  q11 : Eqn
  q11 = wE 157 W
  q12 : Eqn
  q12 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = wE 338 W
  q14 : Eqn
  q14 = wE 343 W

-- hyb sym 23 @0213: 461 steps
lem-hyb-sym-23-at0213 : ⟪ (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") ⟫ʷ ≈ ⟪ (ℓ "丧丧乄丧乌中中中乑业中中中中中中乌中中乑中临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临") ⟫ʷ
lem-hyb-sym-23-at0213 = derive (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") (ℓ "丧丧乄丧乌中中中乑业中中中中中中乌中中乑中临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临")
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
   rw 4 q11 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q2 ∷
   rw⁻ 7 q12 ∷
   rw 8 q4 ∷
   re 5 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q2 ∷
   rw⁻ 8 q12 ∷
   rw 9 q4 ∷
   re 6 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q2 ∷
   rw⁻ 9 q12 ∷
   rw 10 q4 ∷
   re 7 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 8 q2 ∷
   rw⁻ 10 q3 ∷
   rw 11 q4 ∷
   re 8 5 (ℓ "乑") ∷
   rw 9 q5 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q2 ∷
   rw⁻ 12 q12 ∷
   rw 13 q4 ∷
   re 10 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q2 ∷
   rw⁻ 13 q12 ∷
   rw 14 q4 ∷
   re 11 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q2 ∷
   rw⁻ 14 q12 ∷
   rw 15 q4 ∷
   re 12 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q2 ∷
   rw⁻ 15 q12 ∷
   rw 16 q4 ∷
   re 13 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q2 ∷
   rw⁻ 16 q12 ∷
   rw 17 q4 ∷
   re 14 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q2 ∷
   rw⁻ 17 q12 ∷
   rw 18 q4 ∷
   re 15 5 (ℓ "中") ∷
   rw 16 q11 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q2 ∷
   rw⁻ 19 q12 ∷
   rw 20 q4 ∷
   re 17 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q2 ∷
   rw⁻ 20 q12 ∷
   rw 21 q4 ∷
   re 18 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q2 ∷
   rw⁻ 21 q3 ∷
   rw 22 q4 ∷
   re 19 5 (ℓ "乑") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q2 ∷
   rw⁻ 22 q12 ∷
   rw 23 q4 ∷
   re 20 5 (ℓ "中") ∷
   re 22 1 (ℓ "丼临丼") ∷
   rw 21 q6 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q2 ∷
   rw⁻ 24 q12 ∷
   rw 25 q4 ∷
   re 22 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q2 ∷
   rw⁻ 25 q12 ∷
   rw 26 q4 ∷
   re 23 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   rw⁻ 26 q12 ∷
   rw 27 q4 ∷
   re 24 5 (ℓ "中") ∷
   rw 25 q5 ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 26 q2 ∷
   rw⁻ 28 q3 ∷
   rw 29 q4 ∷
   re 26 5 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   rw⁻ 29 q12 ∷
   rw 30 q4 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   rw⁻ 30 q12 ∷
   rw 31 q4 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   rw⁻ 31 q12 ∷
   rw 32 q4 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   rw⁻ 32 q12 ∷
   rw 33 q4 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   rw⁻ 33 q12 ∷
   rw 34 q4 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   rw⁻ 34 q12 ∷
   rw 35 q4 ∷
   re 32 5 (ℓ "中") ∷
   rw 33 q11 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   rw⁻ 36 q12 ∷
   rw 37 q4 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   rw⁻ 37 q12 ∷
   rw 38 q4 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   rw⁻ 38 q12 ∷
   rw 39 q4 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   rw⁻ 39 q12 ∷
   rw 40 q4 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q2 ∷
   rw⁻ 40 q12 ∷
   rw 41 q4 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q2 ∷
   rw⁻ 41 q12 ∷
   rw 42 q4 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q2 ∷
   rw⁻ 42 q12 ∷
   rw 43 q4 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q2 ∷
   rw⁻ 43 q12 ∷
   rw 44 q4 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q2 ∷
   rw⁻ 44 q12 ∷
   rw 45 q4 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q2 ∷
   rw⁻ 45 q12 ∷
   rw 46 q4 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q2 ∷
   rw⁻ 46 q12 ∷
   rw 47 q4 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q2 ∷
   rw⁻ 47 q12 ∷
   rw 48 q4 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q2 ∷
   rw⁻ 48 q12 ∷
   rw 49 q4 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q2 ∷
   rw⁻ 49 q12 ∷
   rw 50 q4 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q2 ∷
   rw⁻ 50 q12 ∷
   rw 51 q4 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q2 ∷
   rw⁻ 51 q12 ∷
   rw 52 q4 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   rw⁻ 52 q12 ∷
   rw 53 q4 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q2 ∷
   rw⁻ 53 q12 ∷
   rw 54 q4 ∷
   re 51 5 (ℓ "中") ∷
   rw 52 q5 ∷
   rw 53 q5 ∷
   rw 54 q5 ∷
   rw 55 q5 ∷
   re 57 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   re 56 5 (ℓ "乑") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q2 ∷
   rw⁻ 59 q12 ∷
   rw 60 q4 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q2 ∷
   rw⁻ 60 q12 ∷
   rw 61 q4 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q2 ∷
   rw⁻ 61 q12 ∷
   rw 62 q4 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q2 ∷
   rw⁻ 62 q12 ∷
   rw 63 q4 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q2 ∷
   rw⁻ 63 q12 ∷
   rw 64 q4 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q2 ∷
   rw⁻ 64 q12 ∷
   rw 65 q4 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q2 ∷
   rw⁻ 65 q12 ∷
   rw 66 q4 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q2 ∷
   rw⁻ 66 q12 ∷
   rw 67 q4 ∷
   re 64 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q2 ∷
   rw⁻ 67 q12 ∷
   rw 68 q4 ∷
   re 65 5 (ℓ "中") ∷
   rw 66 q11 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "丧") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "丧") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "丧") ∷
   rw 70 q13 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乄") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "丧") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "丧") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "丧") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "丧") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "丧") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "丧") ∷
   rw 78 q14 ∷
   re 80 1 (ℓ "丼临丼") ∷
   rw 79 q6 ∷
   rw 80 q6 ∷ []) Eq.refl
