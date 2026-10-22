{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D499 (W : Ws) where

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
  q1 = wE 1052 W
  q2 : Eqn
  q2 = eqn (CS01⁻ ∷ CK23 ∷ []) (CK23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₀₁))
  q3 : Eqn
  q3 = wE 1053 W
  q4 : Eqn
  q4 = wE 65 W
  q5 : Eqn
  q5 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q6 : Eqn
  q6 = wE 48 W
  q7 : Eqn
  q7 = wE 1268 W
  q8 : Eqn
  q8 = wE 1269 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = wE 76 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 772 W
  q13 : Eqn
  q13 = wE 1313 W
  q14 : Eqn
  q14 = wE 29 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 198 W
  q19 : Eqn
  q19 = wE 27 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CSd02]: 185 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CSd02 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CSd02 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (re 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 28 q1 ∷
   rw⁻ 29 q2 ∷
   rw 30 q3 ∷
   re 28 3 (CS02⁻ ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 27 3 (CS02⁻ ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw 28 q6 ∷
   re 26 3 (CS02⁻ ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 25 3 (CS02⁻ ∷ []) ∷
   re 25 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 24 q4 ∷
   rw⁻ 25 q5 ∷
   rw 26 q6 ∷
   re 24 3 (CS02⁻ ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 23 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 23 3 (CS02⁻ ∷ []) ∷
   rw 22 q7 ∷
   re 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 21 q4 ∷
   rw⁻ 22 q5 ∷
   rw 23 q6 ∷
   re 21 3 (CS02⁻ ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 20 q4 ∷
   rw⁻ 21 q5 ∷
   rw 22 q6 ∷
   re 20 3 (CS02⁻ ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 19 q4 ∷
   rw⁻ 20 q5 ∷
   rw 21 q6 ∷
   re 19 3 (CS02⁻ ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 18 q4 ∷
   rw⁻ 19 q5 ∷
   rw 20 q6 ∷
   re 18 3 (CS02⁻ ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 18 q5 ∷
   rw 19 q6 ∷
   re 17 3 (CS02⁻ ∷ []) ∷
   re 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 16 q4 ∷
   rw⁻ 17 q5 ∷
   rw 18 q6 ∷
   re 16 3 (CS02⁻ ∷ []) ∷
   rw 15 q8 ∷
   re 15 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   rw 16 q3 ∷
   re 14 3 (CS02⁻ ∷ []) ∷
   re 14 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   re 13 3 (CS02⁻ ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 12 q4 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   re 12 3 (CS02⁻ ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 11 q4 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   re 11 3 (CS02⁻ ∷ []) ∷
   rw 10 q8 ∷
   re 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   rw 11 q3 ∷
   re 9 3 (CS02⁻ ∷ []) ∷
   rw 8 q8 ∷
   re 8 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   rw 9 q3 ∷
   re 7 3 (CS02⁻ ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q9 ∷
   rw 6 q10 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CK13 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q15 ∷
   rw 8 q11 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q9 ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q15 ∷
   rw 7 q11 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q9 ∷
   rw 4 q10 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q17 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q14 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q19 ∷
   rw 6 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (CK13 ∷ []) ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q15 ∷
   rw 5 q11 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q9 ∷
   rw 2 q10 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q17 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q11 ∷
   rw 3 q19 ∷
   rw 4 q11 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 1 q17 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q14 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q11 ∷
   rw 2 q19 ∷
   rw 3 q11 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (X0 ∷ CK13 ∷ []) (CK13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))
  q21 : Eqn
  q21 = eqn (CK01⁻ ∷ CK23 ∷ []) (CK23 ∷ CK01⁻ ∷ []) (low-comm ((S • CK₀₁)) (CK₀₁))
  q22 : Eqn
  q22 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q23 : Eqn
  q23 = eqn (CK01⁻ ∷ CS23 ∷ []) (CS23 ∷ CK01⁻ ∷ []) (low-comm ((S • CK₀₁)) (CS))
  q24 : Eqn
  q24 = wE 1271 W
  q25 : Eqn
  q25 = eqn (X0 ∷ S1 ∷ []) (S1 ∷ X0 ∷ []) (low₁-comm (X) (S))
  q26 : Eqn
  q26 = wE 1272 W
  q27 : Eqn
  q27 = wE 1106 W
  q28 : Eqn
  q28 = wE 1228 W
  q29 : Eqn
  q29 = wE 1314 W
  q30 : Eqn
  q30 = wE 317 W
  q31 : Eqn
  q31 = wE 330 W
  q32 : Eqn
  q32 = wE 1315 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [X0 CKd02 X0]: 251 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CKd02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CKd02-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (rw⁻ 28 q20 ∷
   re 30 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 29 q1 ∷
   rw⁻ 30 q21 ∷
   rw 31 q3 ∷
   re 29 3 (CK02⁻ ∷ []) ∷
   rw⁻ 30 q20 ∷
   rw⁻ 27 q20 ∷
   re 29 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 28 q1 ∷
   rw⁻ 29 q21 ∷
   rw 30 q3 ∷
   re 28 3 (CK02⁻ ∷ []) ∷
   rw⁻ 29 q20 ∷
   rw⁻ 26 q22 ∷
   re 28 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 27 q4 ∷
   rw⁻ 28 q23 ∷
   rw 29 q6 ∷
   re 27 3 (CK02⁻ ∷ []) ∷
   rw⁻ 28 q22 ∷
   rw⁻ 25 q20 ∷
   re 27 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q1 ∷
   rw⁻ 27 q21 ∷
   rw 28 q3 ∷
   re 26 3 (CK02⁻ ∷ []) ∷
   rw⁻ 27 q20 ∷
   rw⁻ 24 q22 ∷
   re 26 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q4 ∷
   rw⁻ 26 q23 ∷
   rw 27 q6 ∷
   re 25 3 (CK02⁻ ∷ []) ∷
   rw⁻ 26 q22 ∷
   rw⁻ 23 q22 ∷
   re 25 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 24 q4 ∷
   rw⁻ 25 q23 ∷
   rw 26 q6 ∷
   re 24 3 (CK02⁻ ∷ []) ∷
   rw⁻ 25 q22 ∷
   rw 22 q24 ∷
   rw⁻ 21 q22 ∷
   re 23 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 22 q4 ∷
   rw⁻ 23 q23 ∷
   rw 24 q6 ∷
   re 22 3 (CK02⁻ ∷ []) ∷
   rw⁻ 23 q22 ∷
   rw⁻ 20 q22 ∷
   re 22 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 21 q4 ∷
   rw⁻ 22 q23 ∷
   rw 23 q6 ∷
   re 21 3 (CK02⁻ ∷ []) ∷
   rw⁻ 22 q22 ∷
   rw⁻ 19 q22 ∷
   re 21 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 20 q4 ∷
   rw⁻ 21 q23 ∷
   rw 22 q6 ∷
   re 20 3 (CK02⁻ ∷ []) ∷
   rw⁻ 21 q22 ∷
   rw⁻ 18 q22 ∷
   re 20 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 19 q4 ∷
   rw⁻ 20 q23 ∷
   rw 21 q6 ∷
   re 19 3 (CK02⁻ ∷ []) ∷
   rw⁻ 20 q22 ∷
   rw⁻ 17 q22 ∷
   re 19 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 18 q4 ∷
   rw⁻ 19 q23 ∷
   rw 20 q6 ∷
   re 18 3 (CK02⁻ ∷ []) ∷
   rw⁻ 19 q22 ∷
   rw⁻ 16 q22 ∷
   re 18 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 18 q23 ∷
   rw 19 q6 ∷
   re 17 3 (CK02⁻ ∷ []) ∷
   rw⁻ 18 q22 ∷
   rw⁻ 15 q25 ∷
   rw 16 q26 ∷
   rw⁻ 17 q25 ∷
   rw⁻ 14 q20 ∷
   re 16 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 15 q1 ∷
   rw⁻ 16 q21 ∷
   rw 17 q3 ∷
   re 15 3 (CK02⁻ ∷ []) ∷
   rw⁻ 16 q20 ∷
   rw⁻ 13 q22 ∷
   re 15 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 14 q4 ∷
   rw⁻ 15 q23 ∷
   rw 16 q6 ∷
   re 14 3 (CK02⁻ ∷ []) ∷
   rw⁻ 15 q22 ∷
   rw⁻ 12 q22 ∷
   re 14 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 14 q23 ∷
   rw 15 q6 ∷
   re 13 3 (CK02⁻ ∷ []) ∷
   rw⁻ 14 q22 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 12 q4 ∷
   rw⁻ 13 q23 ∷
   rw 14 q6 ∷
   re 12 3 (CK02⁻ ∷ []) ∷
   rw⁻ 13 q22 ∷
   rw⁻ 10 q25 ∷
   rw 11 q26 ∷
   rw⁻ 12 q25 ∷
   rw⁻ 9 q20 ∷
   re 11 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 10 q1 ∷
   rw⁻ 11 q21 ∷
   rw 12 q3 ∷
   re 10 3 (CK02⁻ ∷ []) ∷
   rw⁻ 11 q20 ∷
   rw⁻ 8 q25 ∷
   rw 9 q26 ∷
   rw⁻ 10 q25 ∷
   rw⁻ 7 q20 ∷
   re 9 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ∷
   rw 8 q1 ∷
   rw⁻ 9 q21 ∷
   rw 10 q3 ∷
   re 8 3 (CK02⁻ ∷ []) ∷
   rw⁻ 9 q20 ∷
   rw 6 q24 ∷
   rw 9 q9 ∷
   rw 8 q27 ∷
   rw 7 q28 ∷
   rw 6 q27 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CK13 ∷ []) ∷
   rw 6 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q30 ∷
   re 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q15 ∷
   rw 10 q11 ∷
   re 8 3 (CK03 ∷ []) ∷
   rw 9 q16 ∷
   rw 8 q9 ∷
   rw 7 q27 ∷
   rw 6 q28 ∷
   rw 5 q27 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw 5 q29 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q30 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q11 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw 8 q16 ∷
   rw 7 q9 ∷
   rw 6 q27 ∷
   rw 5 q28 ∷
   rw 4 q27 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q17 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q32 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q30 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q19 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q9 ∷
   rw 5 q27 ∷
   rw 4 q28 ∷
   rw 3 q27 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (CK13 ∷ []) ∷
   rw 3 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q30 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q15 ∷
   rw 7 q11 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q9 ∷
   rw 4 q27 ∷
   rw 3 q28 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q17 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q32 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q30 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q19 ∷
   rw 6 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q9 ∷
   rw 3 q27 ∷
   rw 2 q28 ∷
   rw 1 q27 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 1 q17 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q32 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q30 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q19 ∷
   rw 5 q11 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷ []) Eq.refl
