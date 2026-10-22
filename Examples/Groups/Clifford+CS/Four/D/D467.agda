{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D467 (W : Ws) where

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
  q2 = wE 279 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q4 : Eqn
  q4 = wE 280 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 65 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q8 : Eqn
  q8 = wE 48 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 74 W
  q13 : Eqn
  q13 = wE 695 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 30 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q18 : Eqn
  q18 = wE 210 W
  q19 : Eqn
  q19 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q20 : Eqn
  q20 = wE 1226 W
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = wE 95 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [CS03]: 291 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CS03 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CS03 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CS03 ∷ []) (CS03 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 30 q3 ∷
   rw 31 q4 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q4 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   re 26 3 (CK31 ∷ []) ∷
   rw 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw 28 q4 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   rw 24 q9 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q10 ∷
   rw 24 q11 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 22 q12 ∷
   rw 23 q13 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q10 ∷
   rw 23 q14 ∷
   rw 24 q10 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q15 ∷
   rw 24 q16 ∷
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
   rw 17 q9 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q10 ∷
   rw 17 q11 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q17 ∷
   rw 16 q18 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q10 ∷
   rw 16 q14 ∷
   rw 17 q10 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q17 ∷
   rw 17 q16 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q2 ∷
   rw⁻ 16 q3 ∷
   rw 17 q4 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
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
   rw 12 q9 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q11 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 10 q17 ∷
   rw 11 q18 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q14 ∷
   rw 12 q10 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q17 ∷
   rw 12 q16 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 11 q3 ∷
   rw 12 q4 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 10 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 8 q17 ∷
   rw 9 q18 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q14 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q17 ∷
   rw 10 q16 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 8 q2 ∷
   rw⁻ 9 q3 ∷
   rw 10 q4 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 8 q9 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q14 ∷
   rw 8 q10 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw 7 q5 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q19 ∷
   rw 5 q20 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 6 q5 ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw⁻ 4 q21 ∷
   rw 5 q5 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 4 q5 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 2 q21 ∷
   rw 3 q5 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q21 ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1223 W
  q24 : Eqn
  q24 = eqn (CK01 ∷ CX23 ∷ []) (CX23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q27 : Eqn
  q27 = wE 6 W
  q28 : Eqn
  q28 = wE 914 W
  q29 : Eqn
  q29 = wE 39 W
  q30 : Eqn
  q30 = eqn (S0 ∷ CX23 ∷ []) (CX23 ∷ S0 ∷ []) (low₁-comm (S) ((CX₀₁ ↑)))
  q31 : Eqn
  q31 = wE 917 W
  q32 : Eqn
  q32 = wE 915 W
  q33 : Eqn
  q33 = wE 1224 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [CX23]: 43 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CX23 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-CX23 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw 0 q23 ∷
   rw 28 q24 ∷
   rw 27 q24 ∷
   rw 26 q25 ∷
   rw 25 q24 ∷
   rw 24 q25 ∷
   rw 23 q25 ∷
   rw 24 q9 ∷
   rw⁻ 23 q26 ∷
   rw 22 q27 ∷
   rw 23 q28 ∷
   rw 22 q26 ∷
   rw 23 q29 ∷
   rw 24 q16 ∷
   rw 21 q25 ∷
   rw 20 q25 ∷
   rw 19 q25 ∷
   rw 18 q25 ∷
   rw 17 q25 ∷
   rw 16 q25 ∷
   rw 15 q30 ∷
   rw 14 q24 ∷
   rw 13 q25 ∷
   rw 12 q25 ∷
   rw 11 q25 ∷
   rw 10 q30 ∷
   rw 9 q24 ∷
   rw 8 q30 ∷
   rw 7 q24 ∷
   rw 8 q9 ∷
   rw⁻ 7 q26 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 6 q26 ∷
   rw 7 q29 ∷
   rw 8 q16 ∷
   rw 5 q31 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷ []) Eq.refl
