{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D152 (W : Ws) where

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
  q1 = wE 655 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 352 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q5 : Eqn
  q5 = wE 357 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "临乍") (ℓ "乍临") (low-comm (CK₁₀) (CK₀₁))
  q8 : Eqn
  q8 = wE 701 W
  q9 : Eqn
  q9 = wE 702 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 600 W
  q12 : Eqn
  q12 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = wE 599 W
  q14 : Eqn
  q14 = wE 656 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [CK13]: 389 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CK13 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠乁") ⟫ʷ ≈ ⟪ (ℓ "乁丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CK13 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠乁") (ℓ "乁丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q1 ∷
   re 31 1 (ℓ "乏为乏") ∷
   rw 30 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乁") ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (ℓ "乏为乏") ∷
   rw 31 q6 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q6 ∷
   re 30 3 (ℓ "乁") ∷
   re 30 1 (ℓ "乏为乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乁") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏为乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "乁") ∷
   re 29 1 (ℓ "乏为乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乁") ∷
   rw 32 q3 ∷
   rw 31 q7 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏为乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "乁") ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "乁") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏为乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "乁") ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乁") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "乁") ∷
   re 26 1 (ℓ "乏为乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乁") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "乁") ∷
   rw 24 q8 ∷
   re 24 1 (ℓ "乏为乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乁") ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 23 3 (ℓ "乁") ∷
   re 23 1 (ℓ "乏为乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乁") ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏为乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "乁") ∷
   re 22 1 (ℓ "乏为乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乁") ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏为乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "乁") ∷
   re 21 1 (ℓ "乏为乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乁") ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏为乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "乁") ∷
   re 20 1 (ℓ "乏为乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乁") ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏为乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "乁") ∷
   re 19 1 (ℓ "乏为乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乁") ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏为乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "乁") ∷
   re 18 1 (ℓ "乏为乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乁") ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏为乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "乁") ∷
   re 17 1 (ℓ "乏为乏") ∷
   rw 16 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "乁") ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   re 18 1 (ℓ "乏为乏") ∷
   rw 17 q6 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 16 3 (ℓ "乁") ∷
   re 16 1 (ℓ "乏为乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乁") ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (ℓ "乏为乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "乁") ∷
   rw 14 q9 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "乁") ∷
   rw 17 q3 ∷
   rw 16 q7 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏为乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "乁") ∷
   re 13 1 (ℓ "乏为乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "乁") ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "乁") ∷
   re 12 1 (ℓ "乏为乏") ∷
   rw 11 q2 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "乁") ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   re 13 1 (ℓ "乏为乏") ∷
   rw 12 q6 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   re 11 3 (ℓ "乁") ∷
   re 11 1 (ℓ "乏为乏") ∷
   rw 10 q2 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乁") ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (ℓ "乏为乏") ∷
   rw 11 q6 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   re 10 3 (ℓ "乁") ∷
   re 10 1 (ℓ "乏为乏") ∷
   rw 9 q2 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "乁") ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 11 1 (ℓ "乏为乏") ∷
   rw 10 q6 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   re 9 3 (ℓ "乁") ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 8 q2 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "乁") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (ℓ "乏为乏") ∷
   rw 9 q6 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   re 8 3 (ℓ "乁") ∷
   re 8 1 (ℓ "乏为乏") ∷
   rw 7 q2 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乁") ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 8 q6 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   re 7 3 (ℓ "乁") ∷
   rw 6 q8 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 8 q6 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "乁") ∷
   rw⁻ 6 q10 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 7 q6 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乁") ∷
   rw⁻ 5 q10 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏为乏") ∷
   rw 6 q6 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乁") ∷
   rw⁻ 4 q12 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏为乏") ∷
   rw 5 q6 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乁") ∷
   rw⁻ 3 q10 ∷
   rw 4 q6 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏为乏") ∷
   rw 4 q6 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "乁") ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏为乏") ∷
   rw 3 q6 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "乁") ∷
   rw⁻ 1 q10 ∷
   rw 2 q6 ∷
   rw 1 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q16 : Eqn
  q16 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q17 : Eqn
  q17 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q18 : Eqn
  q18 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 686 W
  q20 : Eqn
  q20 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q21 : Eqn
  q21 = eqn (ℓ "与乊") (ℓ "乊与") (low-comm ((S ↑)) ((CS • CS • CS)))
  q22 : Eqn
  q22 = wE 5 W
  q23 : Eqn
  q23 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q24 : Eqn
  q24 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 704 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 140 W
  q30 : Eqn
  q30 = wE 703 W
  q31 : Eqn
  q31 = wE 142 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CSd23 X2]: 137 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd23-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乊丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd23-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乊丘") (ℓ "丘乊丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 30 q15 ∷
   rw 31 q16 ∷
   rw 32 q15 ∷
   rw 29 q15 ∷
   rw 30 q16 ∷
   rw 31 q15 ∷
   rw 28 q17 ∷
   rw 29 q18 ∷
   rw 30 q17 ∷
   rw 27 q15 ∷
   rw 28 q16 ∷
   rw 29 q15 ∷
   rw 26 q15 ∷
   rw 27 q16 ∷
   rw 28 q15 ∷
   rw 25 q15 ∷
   rw 26 q16 ∷
   rw 27 q15 ∷
   rw 24 q19 ∷
   rw 23 q15 ∷
   rw 24 q16 ∷
   rw 25 q15 ∷
   rw 22 q15 ∷
   rw 23 q16 ∷
   rw 24 q15 ∷
   rw 21 q15 ∷
   rw 22 q16 ∷
   rw 23 q15 ∷
   rw 20 q15 ∷
   rw 21 q16 ∷
   rw 22 q15 ∷
   rw 19 q15 ∷
   rw 20 q16 ∷
   rw 21 q15 ∷
   rw 18 q15 ∷
   rw 19 q16 ∷
   rw 20 q15 ∷
   rw 17 q15 ∷
   rw 18 q16 ∷
   rw 19 q15 ∷
   rw 16 q15 ∷
   rw 17 q16 ∷
   rw 18 q15 ∷
   rw 15 q15 ∷
   rw 16 q16 ∷
   rw 17 q15 ∷
   rw 14 q20 ∷
   rw 15 q21 ∷
   rw 16 q20 ∷
   rw 13 q17 ∷
   rw 14 q18 ∷
   rw 15 q17 ∷
   rw 12 q15 ∷
   rw 13 q16 ∷
   rw 14 q15 ∷
   rw 11 q15 ∷
   rw 12 q16 ∷
   rw 13 q15 ∷
   rw 10 q15 ∷
   rw 11 q16 ∷
   rw 12 q15 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q15 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   rw 6 q19 ∷
   rw 9 q22 ∷
   rw⁻ 8 q23 ∷
   rw⁻ 7 q24 ∷
   rw⁻ 6 q23 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw 7 q23 ∷
   rw 8 q27 ∷
   rw 9 q28 ∷
   rw 8 q22 ∷
   rw⁻ 7 q23 ∷
   rw⁻ 6 q24 ∷
   rw⁻ 5 q23 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   rw 6 q23 ∷
   rw 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q22 ∷
   rw⁻ 6 q23 ∷
   rw⁻ 5 q24 ∷
   rw⁻ 4 q23 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 3 q23 ∷
   rw 4 q24 ∷
   rw 5 q23 ∷
   rw 6 q31 ∷
   rw 7 q28 ∷
   rw 6 q22 ∷
   rw⁻ 5 q23 ∷
   rw⁻ 4 q24 ∷
   rw⁻ 3 q23 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   rw 4 q23 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 5 q22 ∷
   rw⁻ 4 q23 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 2 q23 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q23 ∷
   rw 4 q27 ∷
   rw 5 q28 ∷
   rw 4 q22 ∷
   rw⁻ 3 q23 ∷
   rw⁻ 2 q24 ∷
   rw⁻ 1 q23 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 0 q23 ∷
   rw 1 q24 ∷
   rw 2 q23 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷ []) Eq.refl
