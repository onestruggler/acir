{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D478 (W : Ws) where

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
  q1 = eqn (X0 ∷ CK12 ∷ []) (CK12 ∷ X0 ∷ []) (low₁-comm (X) (CK₀₁))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 1052 W
  q4 : Eqn
  q4 = eqn (CK01 ∷ CK23 ∷ []) (CK23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CK₀₁))
  q5 : Eqn
  q5 = wE 1053 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (X0 ∷ CS12 ∷ []) (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS))
  q8 : Eqn
  q8 = wE 65 W
  q9 : Eqn
  q9 = eqn (CK01 ∷ CS23 ∷ []) (CS23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CS))
  q10 : Eqn
  q10 = wE 48 W
  q11 : Eqn
  q11 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q12 : Eqn
  q12 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q13 : Eqn
  q13 = wE 1253 W
  q14 : Eqn
  q14 = eqn (X0 ∷ S1 ∷ []) (S1 ∷ X0 ∷ []) (low₁-comm (X) (S))
  q15 : Eqn
  q15 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = wE 1254 W
  q17 : Eqn
  q17 = wE 5 W
  q18 : Eqn
  q18 = wE 1106 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 772 W
  q21 : Eqn
  q21 = wE 1255 W
  q22 : Eqn
  q22 = wE 317 W
  q23 : Eqn
  q23 = wE 329 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 1256 W
  q27 : Eqn
  q27 = wE 27 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [X0 CK03 X0]: 371 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-CK03-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-CK03-X0 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (rw⁻ 28 q1 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CK13 ∷ []) ∷
   rw 30 q3 ∷
   rw⁻ 31 q4 ∷
   rw 32 q5 ∷
   re 33 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 29 5 (CK03 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw⁻ 27 q1 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw 29 q3 ∷
   rw⁻ 30 q4 ∷
   rw 31 q5 ∷
   re 32 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 28 5 (CK03 ∷ []) ∷
   rw⁻ 29 q1 ∷
   rw⁻ 26 q7 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q8 ∷
   rw⁻ 29 q9 ∷
   rw 30 q10 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 27 5 (CK03 ∷ []) ∷
   rw⁻ 28 q7 ∷
   rw⁻ 25 q1 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CK13 ∷ []) ∷
   rw 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw 29 q5 ∷
   re 30 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 26 5 (CK03 ∷ []) ∷
   rw⁻ 27 q1 ∷
   rw⁻ 24 q7 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q8 ∷
   rw⁻ 27 q9 ∷
   rw 28 q10 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 25 5 (CK03 ∷ []) ∷
   rw⁻ 26 q7 ∷
   rw⁻ 23 q7 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q8 ∷
   rw⁻ 26 q9 ∷
   rw 27 q10 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 24 5 (CK03 ∷ []) ∷
   rw⁻ 25 q7 ∷
   rw 26 q2 ∷
   rw 25 q11 ∷
   re 24 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 23 q11 ∷
   rw 22 q12 ∷
   rw 23 q13 ∷
   rw⁻ 22 q11 ∷
   rw 25 q2 ∷
   re 23 3 (CK03 ∷ []) ∷
   rw⁻ 24 q11 ∷
   rw⁻ 25 q12 ∷
   rw 26 q6 ∷
   rw⁻ 21 q7 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q8 ∷
   rw⁻ 24 q9 ∷
   rw 25 q10 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 22 5 (CK03 ∷ []) ∷
   rw⁻ 23 q7 ∷
   rw⁻ 20 q7 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q8 ∷
   rw⁻ 23 q9 ∷
   rw 24 q10 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 21 5 (CK03 ∷ []) ∷
   rw⁻ 22 q7 ∷
   rw⁻ 19 q7 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q8 ∷
   rw⁻ 22 q9 ∷
   rw 23 q10 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 20 5 (CK03 ∷ []) ∷
   rw⁻ 21 q7 ∷
   rw⁻ 18 q7 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q8 ∷
   rw⁻ 21 q9 ∷
   rw 22 q10 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 19 5 (CK03 ∷ []) ∷
   rw⁻ 20 q7 ∷
   rw⁻ 17 q7 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q8 ∷
   rw⁻ 20 q9 ∷
   rw 21 q10 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 18 5 (CK03 ∷ []) ∷
   rw⁻ 19 q7 ∷
   rw⁻ 16 q7 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q8 ∷
   rw⁻ 19 q9 ∷
   rw 20 q10 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 17 5 (CK03 ∷ []) ∷
   rw⁻ 18 q7 ∷
   rw⁻ 15 q14 ∷
   rw 18 q2 ∷
   re 17 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw 16 q15 ∷
   rw 17 q16 ∷
   rw 18 q2 ∷
   re 16 3 (CK03 ∷ []) ∷
   rw⁻ 17 q15 ∷
   rw 18 q6 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 14 q1 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CK13 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   re 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 15 5 (CK03 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw⁻ 13 q7 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q8 ∷
   rw⁻ 16 q9 ∷
   rw 17 q10 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 14 5 (CK03 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw⁻ 12 q7 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q8 ∷
   rw⁻ 15 q9 ∷
   rw 16 q10 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 13 5 (CK03 ∷ []) ∷
   rw⁻ 14 q7 ∷
   rw⁻ 11 q7 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q8 ∷
   rw⁻ 14 q9 ∷
   rw 15 q10 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 12 5 (CK03 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw⁻ 10 q14 ∷
   rw 13 q2 ∷
   re 12 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 11 q15 ∷
   rw 12 q16 ∷
   rw 13 q2 ∷
   re 11 3 (CK03 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw 13 q6 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 9 q1 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw 11 q3 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   re 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 10 5 (CK03 ∷ []) ∷
   rw⁻ 11 q1 ∷
   rw⁻ 8 q14 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q2 ∷
   re 9 3 (CK03 ∷ []) ∷
   rw⁻ 10 q15 ∷
   rw 11 q6 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 7 q1 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CK13 ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   re 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 8 5 (CK03 ∷ []) ∷
   rw⁻ 9 q1 ∷
   rw 10 q2 ∷
   rw 9 q11 ∷
   re 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw⁻ 6 q11 ∷
   rw 9 q2 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw⁻ 9 q12 ∷
   rw 10 q6 ∷
   rw 9 q17 ∷
   rw 8 q18 ∷
   re 7 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q19 ∷
   rw 8 q20 ∷
   rw⁻ 7 q19 ∷
   re 8 3 (CK13 ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 5 q22 ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q23 ∷
   rw 8 q19 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q22 ∷
   rw 8 q23 ∷
   rw 9 q24 ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   re 6 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q19 ∷
   rw 7 q20 ∷
   rw⁻ 6 q19 ∷
   re 7 3 (CK13 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 4 q22 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q23 ∷
   rw 7 q19 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   rw 8 q24 ∷
   rw 7 q17 ∷
   rw 6 q18 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q19 ∷
   rw 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 6 3 (CK13 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 3 q22 ∷
   re 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   rw 5 q23 ∷
   rw 6 q19 ∷
   re 4 3 (CK03 ∷ []) ∷
   rw 5 q22 ∷
   rw 6 q27 ∷
   rw 7 q24 ∷
   rw 6 q17 ∷
   rw 5 q18 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw 3 q18 ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 2 q22 ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q23 ∷
   rw 5 q19 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw 4 q22 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw 5 q17 ∷
   rw 4 q18 ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 4 q20 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (CK13 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 1 q22 ∷
   re 3 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 2 q19 ∷
   rw 3 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CK03 ∷ []) ∷
   rw 3 q22 ∷
   rw 4 q27 ∷
   rw 5 q24 ∷
   rw 4 q17 ∷
   rw 3 q18 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q19 ∷
   rw 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 3 3 (CK13 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 0 q22 ∷
   re 2 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 1 q19 ∷
   rw 2 q23 ∷
   rw 3 q19 ∷
   re 1 3 (CK03 ∷ []) ∷
   rw 2 q22 ∷
   rw 3 q27 ∷
   rw 4 q24 ∷ []) Eq.refl
