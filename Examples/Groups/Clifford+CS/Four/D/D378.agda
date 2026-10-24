{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D378 (W : Ws) where

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
  q1 = wE 583 W
  q2 : Eqn
  q2 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 21 W
  q5 : Eqn
  q5 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q6 : Eqn
  q6 = wE 51 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 1034 W
  q11 : Eqn
  q11 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q12 : Eqn
  q12 = wE 211 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = wE 1035 W
  q16 : Eqn
  q16 = wE 175 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 1036 W
  q19 : Eqn
  q19 = wE 586 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd13 X3]: 397 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丞举丞") (ℓ "丞举丞丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q7 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q7 ∷
   re 29 3 (ℓ "举") ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q3 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q7 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q7 ∷
   re 28 3 (ℓ "举") ∷
   rw 29 q2 ∷
   rw 26 q8 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q4 ∷
   rw 30 q9 ∷
   rw 29 q6 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q7 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q7 ∷
   re 27 3 (ℓ "举") ∷
   rw 28 q8 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q3 ∷
   re 27 3 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q7 ∷
   re 28 5 (ℓ "乑") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q7 ∷
   re 26 3 (ℓ "举") ∷
   rw 27 q2 ∷
   rw 24 q8 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q3 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q4 ∷
   rw 28 q9 ∷
   rw 27 q6 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q7 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q7 ∷
   re 25 3 (ℓ "举") ∷
   rw 26 q8 ∷
   rw 23 q8 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q3 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q4 ∷
   rw 27 q9 ∷
   rw 26 q6 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q7 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q7 ∷
   re 24 3 (ℓ "举") ∷
   rw 25 q8 ∷
   rw 22 q10 ∷
   rw 21 q8 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q3 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q4 ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q7 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q7 ∷
   re 22 3 (ℓ "举") ∷
   rw 23 q8 ∷
   rw 20 q8 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q3 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q4 ∷
   rw 24 q9 ∷
   rw 23 q6 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q7 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q7 ∷
   re 21 3 (ℓ "举") ∷
   rw 22 q8 ∷
   rw 19 q8 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q3 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q4 ∷
   rw 23 q9 ∷
   rw 22 q6 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q7 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q7 ∷
   re 20 3 (ℓ "举") ∷
   rw 21 q8 ∷
   rw 18 q8 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q3 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q4 ∷
   rw 22 q9 ∷
   rw 21 q6 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q7 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q7 ∷
   re 19 3 (ℓ "举") ∷
   rw 20 q8 ∷
   rw 17 q8 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q4 ∷
   rw 21 q9 ∷
   rw 20 q6 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q7 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q7 ∷
   re 18 3 (ℓ "举") ∷
   rw 19 q8 ∷
   rw 16 q8 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q3 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q4 ∷
   rw 20 q9 ∷
   rw 19 q6 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q7 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q7 ∷
   re 17 3 (ℓ "举") ∷
   rw 18 q8 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q11 ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q3 ∷
   re 16 3 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   rw 17 q6 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q7 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q7 ∷
   re 15 3 (ℓ "举") ∷
   rw 16 q2 ∷
   rw 13 q8 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q3 ∷
   re 15 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q4 ∷
   rw 17 q9 ∷
   rw 16 q6 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q7 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q7 ∷
   re 14 3 (ℓ "举") ∷
   rw 15 q8 ∷
   rw 12 q8 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q3 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q4 ∷
   rw 16 q9 ∷
   rw 15 q6 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q7 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q7 ∷
   re 13 3 (ℓ "举") ∷
   rw 14 q8 ∷
   rw 11 q8 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q3 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q4 ∷
   rw 15 q9 ∷
   rw 14 q6 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q7 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q7 ∷
   re 12 3 (ℓ "举") ∷
   rw 13 q8 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q11 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q3 ∷
   re 11 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q7 ∷
   re 12 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q7 ∷
   re 10 3 (ℓ "举") ∷
   rw 11 q2 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   re 9 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   re 10 5 (ℓ "乑") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q7 ∷
   re 8 3 (ℓ "举") ∷
   rw 9 q2 ∷
   rw 6 q10 ∷
   rw 9 q3 ∷
   rw 8 q13 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q16 ∷
   rw⁻ 8 q14 ∷
   rw 9 q7 ∷
   rw 8 q3 ∷
   rw 7 q13 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q7 ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   rw 4 q16 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "举") ∷
   rw 6 q16 ∷
   rw⁻ 7 q14 ∷
   rw 8 q7 ∷
   rw 7 q3 ∷
   rw 6 q13 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q7 ∷
   rw 4 q13 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 3 q16 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw 5 q16 ∷
   rw⁻ 6 q17 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q13 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q7 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 2 q16 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw 4 q16 ∷
   rw⁻ 5 q14 ∷
   rw 6 q7 ∷
   rw 5 q3 ∷
   rw 4 q13 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q7 ∷
   rw 2 q13 ∷
   rw 1 q17 ∷
   rw 2 q18 ∷
   rw 1 q16 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q16 ∷
   rw⁻ 4 q17 ∷
   rw 5 q7 ∷
   rw 4 q3 ∷
   rw 3 q13 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q13 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   rw 0 q16 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw 4 q7 ∷
   rw 3 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1017 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CSd12 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘") (ℓ "丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 451 W

-- pass [X3 CKd31 X3] [TOFF213]: 1 steps
lem-pass-X3-CKd31-X3-vs-TOFF213 : ⟪ (ℓ "丞乕丞乥") ⟫ʷ ≈ ⟪ (ℓ "乥丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF213 = derive (ℓ "丞乕丞乥") (ℓ "乥丞乕丞")
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 1037 W

-- pass [CCZ123] [X3 CSd23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CSd23-X3 : ⟪ (ℓ "乜丞乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CSd23-X3 = derive (ℓ "乜丞乊丞") (ℓ "丞乊丞乜")
  (rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1038 W

-- pass [CCZ123] [X3 CKd32 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CKd32-X3 : ⟪ (ℓ "乜丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乘丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd32-X3 = derive (ℓ "乜丞乘丞") (ℓ "丞乘丞乜")
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1039 W

-- pass [CCZ123] [X3 CS23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-X3 : ⟪ (ℓ "乜丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞义丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-X3 = derive (ℓ "乜丞义丞") (ℓ "丞义丞乜")
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 266 W

-- pass [CCZ123] [CS23]: 1 steps
lem-pass-CCZ123-vs-CS23 : ⟪ (ℓ "乜义") ⟫ʷ ≈ ⟪ (ℓ "义乜") ⟫ʷ
lem-pass-CCZ123-vs-CS23 = derive (ℓ "乜义") (ℓ "义乜")
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1040 W

-- pass [CZ12] [CS23]: 1 steps
lem-pass-CZ12-vs-CS23 : ⟪ (ℓ "丸义") ⟫ʷ ≈ ⟪ (ℓ "义丸") ⟫ʷ
lem-pass-CZ12-vs-CS23 = derive (ℓ "丸义") (ℓ "义丸")
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 269 W

-- pass [CCZ123] [CSd23]: 1 steps
lem-pass-CCZ123-vs-CSd23 : ⟪ (ℓ "乜乊") ⟫ʷ ≈ ⟪ (ℓ "乊乜") ⟫ʷ
lem-pass-CCZ123-vs-CSd23 = derive (ℓ "乜乊") (ℓ "乊乜")
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q29 : Eqn
  q29 = wE 43 W
  q30 : Eqn
  q30 = wE 100 W
  q31 : Eqn
  q31 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q32 : Eqn
  q32 = wE 433 W
  q33 : Eqn
  q33 = wE 5 W
  q34 : Eqn
  q34 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q35 : Eqn
  q35 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q36 : Eqn
  q36 = wE 6 W
  q37 : Eqn
  q37 = wE 592 W
  q38 : Eqn
  q38 = wE 39 W
  q39 : Eqn
  q39 = wE 31 W
  q40 : Eqn
  q40 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q41 : Eqn
  q41 = wE 104 W

-- comm CCZ013 CSd23: 97 steps
lem-comm-CCZ013-CSd23 : ⟪ (ℓ "乚乊") ⟫ʷ ≈ ⟪ (ℓ "乊乚") ⟫ʷ
lem-comm-CCZ013-CSd23 = derive (ℓ "乚乊") (ℓ "乊乚")
  (rw 1 q3 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q28 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q28 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 3 q28 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q28 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 1 q29 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q30 ∷
   rw⁻ 0 q17 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乐") ∷
   rw⁻ 2 q31 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "乐") ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q7 ∷
   rw 4 q32 ∷
   rw 5 q33 ∷
   rw⁻ 4 q34 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw⁻ 5 q35 ∷
   rw 4 q36 ∷
   rw⁻ 3 q35 ∷
   re 4 3 (ℓ "乓") ∷
   rw 4 q37 ∷
   rw 3 q34 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 4 q35 ∷
   rw 5 q38 ∷
   rw 6 q35 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q39 ∷
   rw 2 q40 ∷
   rw 3 q33 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw⁻ 3 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q35 ∷
   re 2 3 (ℓ "乓") ∷
   rw 2 q37 ∷
   rw 1 q34 ∷
   re 3 1 (ℓ "乏乆乏") ∷
   rw 2 q35 ∷
   rw 3 q38 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q39 ∷
   rw 0 q9 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw 6 q7 ∷
   rw 3 q31 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q7 ∷
   rw 1 q17 ∷
   rw 2 q41 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q28 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q28 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw⁻ 3 q28 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q28 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 2 q29 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 1041 W

-- pass [CZ12] [CSd23]: 1 steps
lem-pass-CZ12-vs-CSd23 : ⟪ (ℓ "丸乊") ⟫ʷ ≈ ⟪ (ℓ "乊丸") ⟫ʷ
lem-pass-CZ12-vs-CSd23 = derive (ℓ "丸乊") (ℓ "乊丸")
  (rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (ℓ "丢乊") (ℓ "乊丢") (low-comm (CZ) ((CS • CS • CS)))

-- pass [CZ01] [CSd23]: 1 steps
lem-pass-CZ01-vs-CSd23 : ⟪ (ℓ "丢乊") ⟫ʷ ≈ ⟪ (ℓ "乊丢") ⟫ʷ
lem-pass-CZ01-vs-CSd23 = derive (ℓ "丢乊") (ℓ "乊丢")
  (rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 1042 W

-- pass [CCZ123] [X3 CK32 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CK32-X3 : ⟪ (ℓ "乜丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CK32-X3 = derive (ℓ "乜丞乗丞") (ℓ "丞乗丞乜")
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 448 W

-- pass [X3 CK31 X3] [TOFF213]: 1 steps
lem-pass-X3-CK31-X3-vs-TOFF213 : ⟪ (ℓ "丞乔丞乥") ⟫ʷ ≈ ⟪ (ℓ "乥丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF213 = derive (ℓ "丞乔丞乥") (ℓ "乥丞乔丞")
  (rw 0 q45 ∷ []) Eq.refl
