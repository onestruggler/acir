{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D480 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 1052 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q4 : Eqn
  q4 = wE 1053 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 65 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q8 : Eqn
  q8 = wE 48 W
  q9 : Eqn
  q9 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q10 : Eqn
  q10 = wE 1262 W
  q11 : Eqn
  q11 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = wE 1263 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 772 W
  q17 : Eqn
  q17 = wE 1264 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 329 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = wE 93 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [CS03]: 297 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CS03 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CS03 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 30 q3 ∷
   rw 31 q4 ∷
   re 32 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CK13 ∷ []) ∷
   rw 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q4 ∷
   re 31 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q6 ∷
   rw⁻ 28 q7 ∷
   rw 29 q8 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CK13 ∷ []) ∷
   rw 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw 28 q4 ∷
   re 29 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q6 ∷
   rw⁻ 26 q7 ∷
   rw 27 q8 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q6 ∷
   rw⁻ 25 q7 ∷
   rw 26 q8 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   rw 22 q9 ∷
   rw 23 q10 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw⁻ 23 q9 ∷
   rw 24 q5 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q6 ∷
   rw⁻ 23 q7 ∷
   rw 24 q8 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q6 ∷
   rw⁻ 22 q7 ∷
   rw 23 q8 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q6 ∷
   rw⁻ 21 q7 ∷
   rw 22 q8 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q6 ∷
   rw⁻ 20 q7 ∷
   rw 21 q8 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q6 ∷
   rw⁻ 19 q7 ∷
   rw 20 q8 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q6 ∷
   rw⁻ 18 q7 ∷
   rw 19 q8 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 16 5 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q11 ∷
   rw 17 q5 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CK13 ∷ []) ∷
   rw 15 q2 ∷
   rw⁻ 16 q3 ∷
   rw 17 q4 ∷
   re 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q6 ∷
   rw⁻ 15 q7 ∷
   rw 16 q8 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 14 q7 ∷
   rw 15 q8 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q7 ∷
   rw 14 q8 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 12 q5 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CK13 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 11 q3 ∷
   rw 12 q4 ∷
   re 13 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 10 q5 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 8 3 (CK13 ∷ []) ∷
   rw 8 q2 ∷
   rw⁻ 9 q3 ∷
   rw 10 q4 ∷
   re 11 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 8 q5 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q14 ∷
   rw 7 q15 ∷
   rw⁻ 6 q14 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q14 ∷
   rw 6 q18 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw 6 q15 ∷
   rw⁻ 5 q14 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q17 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw 5 q18 ∷
   rw 6 q14 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 5 q13 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw 5 q15 ∷
   rw⁻ 4 q14 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q21 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   rw 4 q18 ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q18 ∷
   rw 5 q20 ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q14 ∷
   rw 4 q15 ∷
   rw⁻ 3 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q14 ∷
   rw 3 q18 ∷
   rw 4 q14 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 3 q13 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q14 ∷
   rw 3 q15 ∷
   rw⁻ 2 q14 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q21 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q18 ∷
   rw 3 q14 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q18 ∷
   rw 3 q20 ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 2 q15 ∷
   rw⁻ 1 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 0 q15 ∷
   rw 1 q21 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q14 ∷
   rw 1 q18 ∷
   rw 2 q14 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q18 ∷
   rw 2 q20 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 1257 W
  q23 : Eqn
  q23 = wE 157 W
  q24 : Eqn
  q24 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q25 : Eqn
  q25 = wE 158 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q27 : Eqn
  q27 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q28 : Eqn
  q28 = wE 1265 W
  q29 : Eqn
  q29 = eqn (S0 ∷ CX13 ∷ []) (CX13 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₀₁ • Swap ↑)))
  q30 : Eqn
  q30 = wE 1266 W
  q31 : Eqn
  q31 = wE 1267 W
  q32 : Eqn
  q32 = wE 1260 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [CX13]: 299 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CX13 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CX13 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ []) (CX13 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (rw 0 q22 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q23 ∷
   rw 31 q24 ∷
   rw 30 q25 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 28 3 (CX13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CK03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q23 ∷
   rw 30 q24 ∷
   rw 29 q25 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 27 3 (CX13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q23 ∷
   rw 29 q26 ∷
   rw 28 q25 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 26 3 (CX13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q23 ∷
   rw 28 q24 ∷
   rw 27 q25 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 25 3 (CX13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q23 ∷
   rw 27 q26 ∷
   rw 26 q25 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 24 3 (CX13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q23 ∷
   rw 26 q26 ∷
   rw 25 q25 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 24 q1 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   rw 22 q27 ∷
   rw 23 q28 ∷
   rw 24 q1 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw⁻ 23 q27 ∷
   rw 24 q5 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 25 q23 ∷
   rw 24 q26 ∷
   rw 23 q25 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 21 3 (CX13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q23 ∷
   rw 23 q26 ∷
   rw 22 q25 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 20 3 (CX13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q23 ∷
   rw 22 q26 ∷
   rw 21 q25 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 19 3 (CX13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q23 ∷
   rw 21 q26 ∷
   rw 20 q25 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 18 3 (CX13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q23 ∷
   rw 20 q26 ∷
   rw 19 q25 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 17 3 (CX13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 20 q23 ∷
   rw 19 q26 ∷
   rw 18 q25 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 15 q29 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CK03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CX13 ∷ []) ∷
   rw 18 q23 ∷
   rw 17 q24 ∷
   rw 16 q25 ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 16 5 (CK03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 14 3 (CX13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 17 q23 ∷
   rw 16 q26 ∷
   rw 15 q25 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 13 3 (CX13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 16 q23 ∷
   rw 15 q26 ∷
   rw 14 q25 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   re 12 3 (CX13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 15 q23 ∷
   rw 14 q26 ∷
   rw 13 q25 ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 11 3 (CX13 ∷ []) ∷
   rw 10 q29 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CK03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CX13 ∷ []) ∷
   rw 13 q23 ∷
   rw 12 q24 ∷
   rw 11 q25 ∷
   re 11 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   re 11 5 (CK03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 8 q29 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 8 3 (CK03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q24 ∷
   rw 9 q25 ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   re 9 5 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 8 q1 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw⁻ 7 q27 ∷
   rw 8 q5 ∷
   rw 5 q30 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷ []) Eq.refl
