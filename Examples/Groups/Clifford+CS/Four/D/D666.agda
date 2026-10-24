{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD666 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D666 (W : Ws) (Sᴰ : SD666) where

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
  q2 = wE 478 W
  q3 : Eqn
  q3 = wE 479 W
  q4 : Eqn
  q4 = wE 22 W
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 23 W
  q7 : Eqn
  q7 = wE 14 W
  q8 : Eqn
  q8 = sE 1758 lem-hyb-sym-23
  q9 : Eqn
  q9 = wE 157 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q12 : Eqn
  q12 = wE 338 W
  q13 : Eqn
  q13 = wE 343 W
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = wE 378 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 372 W

-- hyb sym 23 @1320 part1: 500 steps
lem-hyb-sym-23-at1320-part1 : ⟪ (ℓ "並丼乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丼丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏丼並") ⟫ʷ ≈ ⟪ (ℓ "並丼中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧乏中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临乏丼並") ⟫ʷ
lem-hyb-sym-23-at1320-part1 = derive (ℓ "並丼乏丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丼丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丼乏丼並") (ℓ "並丼中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧乏中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临乏丼並")
  (rw 45 q1 ∷
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
   rw 36 q2 ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "丧") ∷
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
   re 30 3 (ℓ "乄") ∷
   rw 28 q3 ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "丧") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "丧") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "丧") ∷
   re 24 1 (ℓ "乏丼临丼乏") ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "乑") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "丧") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "乄") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "丧") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "丧") ∷
   rw 19 q2 ∷
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
   rw 12 q3 ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "乄") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "丧") ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "丧") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丧") ∷
   rw 7 q2 ∷
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
   rw 7 q9 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q4 ∷
   rw⁻ 10 q10 ∷
   rw 11 q6 ∷
   re 8 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q4 ∷
   rw⁻ 11 q10 ∷
   rw 12 q6 ∷
   re 9 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q4 ∷
   rw⁻ 12 q10 ∷
   rw 13 q6 ∷
   re 10 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼临丼乏") ∷
   rw 11 q4 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   re 11 5 (ℓ "乑") ∷
   rw 12 q11 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q4 ∷
   rw⁻ 15 q10 ∷
   rw 16 q6 ∷
   re 13 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q4 ∷
   rw⁻ 16 q10 ∷
   rw 17 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q4 ∷
   rw⁻ 17 q10 ∷
   rw 18 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q4 ∷
   rw⁻ 18 q10 ∷
   rw 19 q6 ∷
   re 16 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q4 ∷
   rw⁻ 19 q10 ∷
   rw 20 q6 ∷
   re 17 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q4 ∷
   rw⁻ 20 q10 ∷
   rw 21 q6 ∷
   re 18 5 (ℓ "中") ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q4 ∷
   rw⁻ 22 q10 ∷
   rw 23 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q4 ∷
   rw⁻ 23 q10 ∷
   rw 24 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 22 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   rw⁻ 25 q10 ∷
   rw 26 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 25 1 (ℓ "丼临丼") ∷
   rw 24 q7 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   rw⁻ 27 q10 ∷
   rw 28 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   rw⁻ 28 q10 ∷
   rw 29 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   rw⁻ 29 q10 ∷
   rw 30 q6 ∷
   re 27 5 (ℓ "中") ∷
   rw 28 q11 ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 29 q4 ∷
   rw⁻ 31 q5 ∷
   rw 32 q6 ∷
   re 29 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q4 ∷
   rw⁻ 32 q10 ∷
   rw 33 q6 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q4 ∷
   rw⁻ 33 q10 ∷
   rw 34 q6 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q4 ∷
   rw⁻ 34 q10 ∷
   rw 35 q6 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q4 ∷
   rw⁻ 35 q10 ∷
   rw 36 q6 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q4 ∷
   rw⁻ 36 q10 ∷
   rw 37 q6 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q4 ∷
   rw⁻ 37 q10 ∷
   rw 38 q6 ∷
   re 35 5 (ℓ "中") ∷
   rw 36 q9 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q4 ∷
   rw⁻ 39 q10 ∷
   rw 40 q6 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q4 ∷
   rw⁻ 40 q10 ∷
   rw 41 q6 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q4 ∷
   rw⁻ 41 q10 ∷
   rw 42 q6 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q4 ∷
   rw⁻ 42 q10 ∷
   rw 43 q6 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q4 ∷
   rw⁻ 43 q10 ∷
   rw 44 q6 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q4 ∷
   rw⁻ 44 q10 ∷
   rw 45 q6 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q4 ∷
   rw⁻ 45 q10 ∷
   rw 46 q6 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q4 ∷
   rw⁻ 46 q10 ∷
   rw 47 q6 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q4 ∷
   rw⁻ 47 q10 ∷
   rw 48 q6 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q4 ∷
   rw⁻ 48 q10 ∷
   rw 49 q6 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q4 ∷
   rw⁻ 49 q10 ∷
   rw 50 q6 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q4 ∷
   rw⁻ 50 q10 ∷
   rw 51 q6 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q4 ∷
   rw⁻ 51 q10 ∷
   rw 52 q6 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q4 ∷
   rw⁻ 52 q10 ∷
   rw 53 q6 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q4 ∷
   rw⁻ 53 q10 ∷
   rw 54 q6 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q4 ∷
   rw⁻ 54 q10 ∷
   rw 55 q6 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q4 ∷
   rw⁻ 55 q10 ∷
   rw 56 q6 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q4 ∷
   rw⁻ 56 q10 ∷
   rw 57 q6 ∷
   re 54 5 (ℓ "中") ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q11 ∷
   rw 58 q11 ∷
   re 60 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q4 ∷
   rw⁻ 61 q5 ∷
   rw 62 q6 ∷
   re 59 5 (ℓ "乑") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q4 ∷
   rw⁻ 62 q10 ∷
   rw 63 q6 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q4 ∷
   rw⁻ 63 q10 ∷
   rw 64 q6 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q4 ∷
   rw⁻ 64 q10 ∷
   rw 65 q6 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q4 ∷
   rw⁻ 65 q10 ∷
   rw 66 q6 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q4 ∷
   rw⁻ 66 q10 ∷
   rw 67 q6 ∷
   re 64 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q4 ∷
   rw⁻ 67 q10 ∷
   rw 68 q6 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q4 ∷
   rw⁻ 68 q10 ∷
   rw 69 q6 ∷
   re 66 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q4 ∷
   rw⁻ 69 q10 ∷
   rw 70 q6 ∷
   re 67 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q4 ∷
   rw⁻ 70 q10 ∷
   rw 71 q6 ∷
   re 68 5 (ℓ "中") ∷
   rw 69 q9 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "丧") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "丧") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "丧") ∷
   rw 73 q12 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "乄") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "丧") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "丧") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "丧") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "丧") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "丧") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "丧") ∷
   rw 81 q13 ∷
   re 83 1 (ℓ "丼临丼") ∷
   rw 82 q7 ∷
   rw 83 q7 ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q15 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q16 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 10 q16 ∷
   rw 11 q17 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q16 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q16 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q16 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q16 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q16 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q16 ∷
   rw 18 q15 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 19 q16 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q16 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw 21 q16 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 22 q16 ∷
   rw⁻ 23 q5 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 24 q16 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 25 q16 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 26 q16 ∷
   rw 27 q17 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 28 q16 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q16 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q16 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q16 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 33 q16 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q16 ∷
   rw 35 q15 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q16 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q16 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q16 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q16 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q16 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q16 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q16 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q16 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q16 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q16 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q16 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q16 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q16 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q16 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q16 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q16 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 52 q16 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 53 q16 ∷
   rw 54 q17 ∷
   rw 55 q17 ∷
   rw 56 q17 ∷
   rw 57 q17 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 58 q16 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q16 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q16 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q16 ∷ []) Eq.refl
