{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D383 (W : Ws) where

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
  q2 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 21 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q6 : Eqn
  q6 = wE 51 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 1034 W
  q11 : Eqn
  q11 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q12 : Eqn
  q12 = wE 211 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 1036 W
  q16 : Eqn
  q16 = wE 175 W
  q17 : Eqn
  q17 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q18 : Eqn
  q18 = wE 1035 W
  q19 : Eqn
  q19 = wE 656 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CSd13 X3]: 459 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丞举丞") (ℓ "丞举丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q1 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q3 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "举") ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q7 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q7 ∷
   re 31 3 (ℓ "举") ∷
   rw 32 q2 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q3 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q7 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q7 ∷
   re 30 3 (ℓ "举") ∷
   rw 31 q2 ∷
   rw 28 q8 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q4 ∷
   rw 32 q9 ∷
   rw 31 q6 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q7 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q7 ∷
   re 29 3 (ℓ "举") ∷
   rw 30 q8 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q3 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q7 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q7 ∷
   re 28 3 (ℓ "举") ∷
   rw 29 q2 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q7 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q7 ∷
   re 27 3 (ℓ "举") ∷
   rw 28 q2 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q3 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q7 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q7 ∷
   re 26 3 (ℓ "举") ∷
   rw 27 q2 ∷
   rw 24 q10 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q3 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q7 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q7 ∷
   re 24 3 (ℓ "举") ∷
   rw 25 q2 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q3 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q6 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q7 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q7 ∷
   re 23 3 (ℓ "举") ∷
   rw 24 q2 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q3 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q7 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q7 ∷
   re 22 3 (ℓ "举") ∷
   rw 23 q2 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q3 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q7 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q7 ∷
   re 21 3 (ℓ "举") ∷
   rw 22 q2 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q3 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q7 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q7 ∷
   re 20 3 (ℓ "举") ∷
   rw 21 q2 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q3 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q7 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q7 ∷
   re 19 3 (ℓ "举") ∷
   rw 20 q2 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q7 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q7 ∷
   re 18 3 (ℓ "举") ∷
   rw 19 q2 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q3 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q7 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q7 ∷
   re 17 3 (ℓ "举") ∷
   rw 18 q2 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q3 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q7 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q7 ∷
   re 16 3 (ℓ "举") ∷
   rw 17 q2 ∷
   rw 14 q11 ∷
   rw 15 q12 ∷
   rw 16 q11 ∷
   rw 13 q8 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q3 ∷
   re 15 3 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q4 ∷
   rw 17 q9 ∷
   rw 16 q6 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q7 ∷
   re 16 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q7 ∷
   re 14 3 (ℓ "举") ∷
   rw 15 q8 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q3 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q7 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q7 ∷
   re 13 3 (ℓ "举") ∷
   rw 14 q2 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q3 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q7 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q7 ∷
   re 12 3 (ℓ "举") ∷
   rw 13 q2 ∷
   rw 10 q2 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q3 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q7 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q7 ∷
   re 11 3 (ℓ "举") ∷
   rw 12 q2 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q3 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q7 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q7 ∷
   re 10 3 (ℓ "举") ∷
   rw 11 q2 ∷
   rw 8 q2 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q3 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q7 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q7 ∷
   re 9 3 (ℓ "举") ∷
   rw 10 q2 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
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
   rw 1 q14 ∷
   rw 2 q15 ∷
   rw 1 q16 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q16 ∷
   rw⁻ 4 q14 ∷
   rw 5 q7 ∷
   rw 4 q3 ∷
   rw 3 q13 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q16 ∷
   rw⁻ 3 q14 ∷
   rw 4 q7 ∷
   rw 3 q19 ∷ []) Eq.refl
