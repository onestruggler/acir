{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D205 (W : Ws) where

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
  q2 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 655 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 21 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 51 W
  q11 : Eqn
  q11 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q12 : Eqn
  q12 = wE 608 W
  q13 : Eqn
  q13 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q14 : Eqn
  q14 = wE 200 W
  q15 : Eqn
  q15 = wE 609 W
  q16 : Eqn
  q16 = wE 464 W
  q17 : Eqn
  q17 = wE 656 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [CSd12]: 401 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丷") ⟫ʷ ≈ ⟪ (ℓ "丷中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丷") (ℓ "丷中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q1 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q2 ∷
   rw 26 q2 ∷
   rw 25 q2 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 21 q2 ∷
   rw 20 q2 ∷
   rw 19 q2 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   rw 16 q2 ∷
   rw 15 q2 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q7 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q4 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q8 ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q8 ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q8 ∷
   rw 30 q11 ∷
   rw 29 q10 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   rw 27 q10 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   rw 24 q12 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q4 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q8 ∷
   rw 23 q9 ∷
   rw 22 q10 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q4 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q8 ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q4 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q8 ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q4 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q4 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q8 ∷
   rw 18 q9 ∷
   rw 17 q10 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q4 ∷
   re 17 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q4 ∷
   re 16 5 (ℓ "中") ∷
   rw⁻ 14 q13 ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q8 ∷
   rw 15 q11 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q4 ∷
   re 14 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q4 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q4 ∷
   re 12 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q4 ∷
   re 11 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q4 ∷
   re 10 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q10 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q4 ∷
   re 8 5 (ℓ "中") ∷
   rw 6 q12 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q14 ∷
   rw 0 q14 ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q4 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q4 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q4 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   rw 15 q16 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q4 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   rw 1 q2 ∷
   rw 2 q17 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 24 q2 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q2 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 31 q2 ∷
   rw 32 q4 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q21 : Eqn
  q21 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q22 : Eqn
  q22 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 7 W
  q25 : Eqn
  q25 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q26 : Eqn
  q26 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q27 : Eqn
  q27 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q28 : Eqn
  q28 = wE 804 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 142 W
  q31 : Eqn
  q31 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK32 CS23 CS23 CKd32 X3]: 121 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-CS23-CS23-CKd32-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-CS23-CS23-CKd32-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗义义乘丞") (ℓ "丞乗义义乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 35 q18 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 33 q20 ∷
   rw⁻ 32 q21 ∷
   rw⁻ 31 q21 ∷
   rw⁻ 30 q22 ∷
   rw⁻ 29 q19 ∷
   rw 28 q23 ∷
   rw 27 q23 ∷
   rw 26 q24 ∷
   rw 25 q23 ∷
   rw 24 q24 ∷
   rw 23 q24 ∷
   rw⁻ 22 q25 ∷
   rw 21 q24 ∷
   rw 20 q24 ∷
   rw 19 q24 ∷
   rw 18 q24 ∷
   rw 17 q24 ∷
   rw 16 q24 ∷
   rw⁻ 15 q26 ∷
   rw 14 q23 ∷
   rw 13 q24 ∷
   rw 12 q24 ∷
   rw 11 q24 ∷
   rw⁻ 10 q26 ∷
   rw 9 q23 ∷
   rw⁻ 8 q26 ∷
   rw 7 q23 ∷
   rw⁻ 6 q25 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q27 ∷
   rw 6 q23 ∷
   rw⁻ 5 q27 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q27 ∷
   rw 5 q23 ∷
   rw⁻ 4 q27 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q27 ∷
   rw 4 q24 ∷
   rw⁻ 3 q27 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q27 ∷
   rw 3 q23 ∷
   rw⁻ 2 q27 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q27 ∷
   rw 2 q24 ∷
   rw⁻ 1 q27 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q27 ∷
   rw 1 q24 ∷
   rw⁻ 0 q27 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q28 ∷
   rw 0 q19 ∷
   rw 1 q22 ∷
   rw 2 q21 ∷
   rw 3 q21 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q27 ∷
   rw 7 q29 ∷
   rw 8 q27 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q27 ∷
   rw 8 q29 ∷
   rw 9 q27 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q27 ∷
   rw 9 q30 ∷
   rw 10 q27 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q27 ∷
   rw 10 q29 ∷
   rw 11 q27 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q27 ∷
   rw 11 q30 ∷
   rw 12 q27 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q27 ∷
   rw 12 q30 ∷
   rw 13 q27 ∷
   re 11 3 (ℓ "乑") ∷
   rw 12 q25 ∷
   rw 13 q30 ∷
   rw 14 q26 ∷
   rw 15 q30 ∷
   rw 16 q26 ∷
   rw 17 q29 ∷
   rw 18 q29 ∷
   rw 19 q29 ∷
   rw 20 q30 ∷
   rw 21 q26 ∷
   rw 22 q29 ∷
   rw 23 q29 ∷
   rw 24 q29 ∷
   rw 25 q29 ∷
   rw 26 q29 ∷
   rw 27 q29 ∷
   rw 28 q25 ∷
   rw 29 q29 ∷
   rw 30 q29 ∷
   rw 31 q30 ∷
   rw 32 q29 ∷
   rw 33 q30 ∷
   rw 34 q30 ∷
   rw 35 q31 ∷ []) Eq.refl
