{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D466 (W : Ws) where

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
  q1 = eqn (X0 ∷ CK21 ∷ []) (CK21 ∷ X0 ∷ []) (low₁-comm (X) (CK₁₀))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 279 W
  q4 : Eqn
  q4 = eqn (CK01 ∷ CK32 ∷ []) (CK32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CK₁₀))
  q5 : Eqn
  q5 = wE 280 W
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
  q11 = wE 5 W
  q12 : Eqn
  q12 = wE 1106 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 772 W
  q15 : Eqn
  q15 = wE 74 W
  q16 : Eqn
  q16 = wE 903 W
  q17 : Eqn
  q17 = wE 317 W
  q18 : Eqn
  q18 = wE 329 W
  q19 : Eqn
  q19 = wE 30 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = eqn (X0 ∷ S2 ∷ []) (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑)))
  q22 : Eqn
  q22 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q23 : Eqn
  q23 = wE 702 W
  q24 : Eqn
  q24 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q26 : Eqn
  q26 = wE 1221 W
  q27 : Eqn
  q27 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = wE 1222 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [X0 CK03 X0]: 365 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-CK03-X0 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-CK03-X0 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw⁻ 28 q1 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 30 q3 ∷
   rw⁻ 31 q4 ∷
   rw 32 q5 ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 29 5 (CK03 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw⁻ 27 q1 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q3 ∷
   rw⁻ 30 q4 ∷
   rw 31 q5 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   re 27 3 (CK31 ∷ []) ∷
   rw 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw 29 q5 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   rw 26 q11 ∷
   rw 25 q12 ∷
   re 24 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q13 ∷
   rw 25 q14 ∷
   rw⁻ 24 q13 ∷
   re 25 3 (CK13 ∷ []) ∷
   rw 23 q12 ∷
   rw 22 q15 ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   re 24 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 23 q13 ∷
   rw 24 q18 ∷
   rw 25 q13 ∷
   re 23 3 (CK03 ∷ []) ∷
   rw 24 q17 ∷
   rw 25 q19 ∷
   rw 26 q20 ∷
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
   rw⁻ 15 q21 ∷
   rw 18 q11 ∷
   re 17 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q13 ∷
   rw 18 q14 ∷
   rw⁻ 17 q13 ∷
   re 18 3 (CK13 ∷ []) ∷
   rw⁻ 16 q22 ∷
   rw 17 q23 ∷
   re 17 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 16 q13 ∷
   rw 17 q18 ∷
   rw 18 q13 ∷
   re 16 3 (CK03 ∷ []) ∷
   rw 17 q22 ∷
   rw 18 q20 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 14 q1 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CK31 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   rw⁻ 10 q21 ∷
   rw 13 q11 ∷
   re 12 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q13 ∷
   rw 13 q14 ∷
   rw⁻ 12 q13 ∷
   re 13 3 (CK13 ∷ []) ∷
   rw⁻ 11 q22 ∷
   rw 12 q23 ∷
   re 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 11 q13 ∷
   rw 12 q18 ∷
   rw 13 q13 ∷
   re 11 3 (CK03 ∷ []) ∷
   rw 12 q22 ∷
   rw 13 q20 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 9 q1 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CK31 ∷ []) ∷
   rw 11 q3 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 10 5 (CK03 ∷ []) ∷
   rw⁻ 11 q1 ∷
   rw⁻ 8 q21 ∷
   rw 11 q11 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q13 ∷
   rw 11 q14 ∷
   rw⁻ 10 q13 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw⁻ 9 q22 ∷
   rw 10 q23 ∷
   re 10 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 9 q13 ∷
   rw 10 q18 ∷
   rw 11 q13 ∷
   re 9 3 (CK03 ∷ []) ∷
   rw 10 q22 ∷
   rw 11 q20 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 7 q1 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CK31 ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 8 5 (CK03 ∷ []) ∷
   rw⁻ 9 q1 ∷
   rw 10 q11 ∷
   rw 9 q12 ∷
   re 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q13 ∷
   rw 9 q14 ∷
   rw⁻ 8 q13 ∷
   re 9 3 (CK13 ∷ []) ∷
   rw 7 q12 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q13 ∷
   rw 8 q18 ∷
   rw 9 q13 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q19 ∷
   rw 10 q20 ∷
   rw 9 q2 ∷
   rw 8 q24 ∷
   re 7 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q24 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw⁻ 5 q24 ∷
   rw 8 q2 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q25 ∷
   rw 9 q6 ∷
   rw 8 q2 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q24 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw⁻ 4 q24 ∷
   rw 7 q2 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw⁻ 7 q25 ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q24 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (CK03 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw⁻ 6 q27 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw⁻ 5 q25 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   rw 4 q24 ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q24 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (CK03 ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q27 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   rw 3 q24 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q24 ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   rw⁻ 0 q24 ∷
   rw 3 q2 ∷
   re 1 3 (CK03 ∷ []) ∷
   rw⁻ 2 q24 ∷
   rw⁻ 3 q27 ∷
   rw 4 q6 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1223 W
  q30 : Eqn
  q30 = eqn (CK01 ∷ CZ23 ∷ []) (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ))
  q31 : Eqn
  q31 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))
  q33 : Eqn
  q33 = wE 6 W
  q34 : Eqn
  q34 = wE 908 W
  q35 : Eqn
  q35 = wE 39 W
  q36 : Eqn
  q36 = eqn (S0 ∷ CZ23 ∷ []) (CZ23 ∷ S0 ∷ []) (low₁-comm (S) ((CZ ↑)))
  q37 : Eqn
  q37 = wE 911 W
  q38 : Eqn
  q38 = wE 909 W
  q39 : Eqn
  q39 = wE 1224 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [CZ23]: 43 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CZ23 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CZ23 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw 0 q29 ∷
   rw 28 q30 ∷
   rw 27 q30 ∷
   rw 26 q31 ∷
   rw 25 q30 ∷
   rw 24 q31 ∷
   rw 23 q31 ∷
   rw 24 q11 ∷
   rw⁻ 23 q32 ∷
   rw 22 q33 ∷
   rw 23 q34 ∷
   rw 22 q32 ∷
   rw 23 q35 ∷
   rw 24 q20 ∷
   rw 21 q31 ∷
   rw 20 q31 ∷
   rw 19 q31 ∷
   rw 18 q31 ∷
   rw 17 q31 ∷
   rw 16 q31 ∷
   rw 15 q36 ∷
   rw 14 q30 ∷
   rw 13 q31 ∷
   rw 12 q31 ∷
   rw 11 q31 ∷
   rw 10 q36 ∷
   rw 9 q30 ∷
   rw 8 q36 ∷
   rw 7 q30 ∷
   rw 8 q11 ∷
   rw⁻ 7 q32 ∷
   rw 6 q33 ∷
   rw 7 q34 ∷
   rw 6 q32 ∷
   rw 7 q35 ∷
   rw 8 q20 ∷
   rw 5 q37 ∷
   rw 4 q37 ∷
   rw 3 q38 ∷
   rw 2 q37 ∷
   rw 1 q38 ∷
   rw 0 q38 ∷
   rw 1 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1225 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [CS02]: 1 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CS02 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CS02 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS02 ∷ []) (CS02 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw 0 q40 ∷ []) Eq.refl
