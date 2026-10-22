{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D498 (W : Ws) where

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
  q2 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q3 : Eqn
  q3 = wE 1053 W
  q4 : Eqn
  q4 = wE 65 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q6 : Eqn
  q6 = wE 48 W
  q7 : Eqn
  q7 = wE 1262 W
  q8 : Eqn
  q8 = wE 1263 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 772 W
  q13 : Eqn
  q13 = wE 1311 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 101 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CS02]: 185 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS02 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS02 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02 ∷ []) (CS02 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q1 ∷
   rw⁻ 29 q2 ∷
   rw 30 q3 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw 28 q6 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 25 3 (CS02 ∷ []) ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q4 ∷
   rw⁻ 25 q5 ∷
   rw 26 q6 ∷
   re 24 3 (CS02 ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 23 3 (CS02 ∷ []) ∷
   rw 22 q7 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q4 ∷
   rw⁻ 22 q5 ∷
   rw 23 q6 ∷
   re 21 3 (CS02 ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q4 ∷
   rw⁻ 21 q5 ∷
   rw 22 q6 ∷
   re 20 3 (CS02 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q4 ∷
   rw⁻ 20 q5 ∷
   rw 21 q6 ∷
   re 19 3 (CS02 ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q4 ∷
   rw⁻ 19 q5 ∷
   rw 20 q6 ∷
   re 18 3 (CS02 ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 18 q5 ∷
   rw 19 q6 ∷
   re 17 3 (CS02 ∷ []) ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q4 ∷
   rw⁻ 17 q5 ∷
   rw 18 q6 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 15 q8 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   rw 16 q3 ∷
   re 14 3 (CS02 ∷ []) ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   re 13 3 (CS02 ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q4 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   re 12 3 (CS02 ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q4 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 10 q8 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   rw 11 q3 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 8 q8 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   rw 9 q3 ∷
   re 7 3 (CS02 ∷ []) ∷
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
   rw 4 q10 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q14 ∷
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
   rw 2 q10 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q11 ∷
   rw 3 q14 ∷
   rw 4 q11 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 1 q10 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q17 ∷
   rw 0 q14 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q11 ∷
   rw 2 q14 ∷
   rw 3 q11 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q21 : Eqn
  q21 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q22 : Eqn
  q22 = wE 1257 W
  q23 : Eqn
  q23 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q24 : Eqn
  q24 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q25 : Eqn
  q25 = wE 157 W
  q26 : Eqn
  q26 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q27 : Eqn
  q27 = wE 158 W
  q28 : Eqn
  q28 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q29 : Eqn
  q29 = wE 1265 W
  q30 : Eqn
  q30 = eqn (S0 ∷ CX12 ∷ []) (CX12 ∷ S0 ∷ []) (low₁-comm (S) (CX₀₁))
  q31 : Eqn
  q31 = wE 1312 W
  q32 : Eqn
  q32 = wE 66 W
  q33 : Eqn
  q33 = wE 1260 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CX12]: 391 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CX12 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CX12 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ []) (CX12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (rw 29 q18 ∷
   re 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 27 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 25 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   rw 22 q20 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   rw 15 q21 ∷
   re 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   rw 10 q21 ∷
   re 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   rw 8 q21 ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   rw 6 q20 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q19 ∷
   rw 1 q22 ∷
   rw 2 q18 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q18 ∷
   re 2 3 (CK13 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CK13 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw⁻ 6 q23 ∷
   rw 9 q18 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q18 ∷
   re 9 3 (CK03 ∷ []) ∷
   rw⁻ 10 q24 ∷
   rw 13 q18 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q18 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q18 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q18 ∷
   re 14 3 (CK03 ∷ []) ∷
   rw⁻ 15 q24 ∷
   rw 18 q18 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q18 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q18 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q18 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q18 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q18 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw⁻ 22 q23 ∷
   rw 25 q18 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q18 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q18 ∷
   re 25 3 (CK03 ∷ []) ∷
   rw 28 q18 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q18 ∷
   re 27 3 (CK03 ∷ []) ∷
   rw 30 q18 ∷
   re 28 3 (CK03 ∷ []) ∷
   rw 29 q19 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q18 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q25 ∷
   rw 30 q26 ∷
   rw 29 q27 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q18 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q25 ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 5 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q25 ∷
   rw 28 q28 ∷
   rw 27 q27 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q18 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q25 ∷
   rw 27 q26 ∷
   rw 26 q27 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 26 5 (CK03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q25 ∷
   rw 26 q28 ∷
   rw 25 q27 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q25 ∷
   rw 25 q28 ∷
   rw 24 q27 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q29 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q25 ∷
   rw 23 q28 ∷
   rw 22 q27 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q25 ∷
   rw 22 q28 ∷
   rw 21 q27 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q25 ∷
   rw 21 q28 ∷
   rw 20 q27 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q25 ∷
   rw 20 q28 ∷
   rw 19 q27 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 20 q25 ∷
   rw 19 q28 ∷
   rw 18 q27 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 19 q25 ∷
   rw 18 q28 ∷
   rw 17 q27 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 15 q30 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 17 q25 ∷
   rw 16 q26 ∷
   rw 15 q27 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 15 5 (CK03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 16 q25 ∷
   rw 15 q28 ∷
   rw 14 q27 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 15 q25 ∷
   rw 14 q28 ∷
   rw 13 q27 ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 14 q25 ∷
   rw 13 q28 ∷
   rw 12 q27 ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q30 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 12 q25 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 10 5 (CK03 ∷ []) ∷
   rw 8 q30 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   re 11 3 (CX13 ∷ []) ∷
   rw 10 q25 ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 8 5 (CK03 ∷ []) ∷
   rw 6 q29 ∷
   rw 5 q31 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 30 q18 ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 26 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   rw 23 q23 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   rw 16 q24 ∷
   re 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   rw 11 q24 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   rw 9 q24 ∷
   re 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 10 q19 ∷
   rw 7 q23 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   re 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   re 3 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 2 q33 ∷
   rw 3 q18 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q18 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 8 q18 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 10 q18 ∷
   re 8 3 (CK13 ∷ []) ∷
   rw⁻ 9 q21 ∷
   rw 12 q18 ∷
   re 10 3 (CK13 ∷ []) ∷
   rw⁻ 11 q21 ∷
   rw 14 q18 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q18 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q18 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q18 ∷
   re 15 3 (CK13 ∷ []) ∷
   rw⁻ 16 q21 ∷
   rw 19 q18 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q18 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q18 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q18 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q18 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q18 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw⁻ 23 q20 ∷
   rw 26 q18 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q18 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q18 ∷
   re 26 3 (CK13 ∷ []) ∷
   rw 29 q18 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q18 ∷
   re 28 3 (CK13 ∷ []) ∷
   rw 31 q18 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw 30 q19 ∷ []) Eq.refl
