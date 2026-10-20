{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D420 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 583 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q8 : Eqn
  q8 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q12 : Eqn
  q12 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q16 : Eqn
  q16 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q17 : Eqn
  q17 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q18 : Eqn
  q18 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q19 : Eqn
  q19 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q22 : Eqn
  q22 = eqn (CX13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CX13 ∷ []) (wn 1150 W)
  q23 : Eqn
  q23 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q24 : Eqn
  q24 = eqn (CS12 ∷ S3 ∷ []) (S3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (S))
  q25 : Eqn
  q25 = eqn (CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CK10 ∷ []) (wn 1032 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS01 ∷ []) (wn 1033 W)
  q27 : Eqn
  q27 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q28 : Eqn
  q28 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 586 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CS12 X2]: 897 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q7 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q7 ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q10 ∷
   rw 29 q11 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q12 ∷
   rw 28 q9 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q10 ∷
   rw 30 q13 ∷
   rw 31 q10 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q14 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 30 5 (CK30 ∷ []) ∷
   rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q10 ∷
   rw 31 q11 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q12 ∷
   rw 30 q9 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q10 ∷
   rw 32 q13 ∷
   rw 33 q10 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q14 ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q14 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 29 5 (CK30 ∷ []) ∷
   rw 31 q8 ∷
   rw⁻ 30 q9 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q10 ∷
   rw 30 q11 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 30 q12 ∷
   rw 29 q9 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q10 ∷
   rw 31 q13 ∷
   rw 32 q10 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q14 ∷
   rw 28 q8 ∷
   rw⁻ 27 q9 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q10 ∷
   rw 27 q18 ∷
   rw⁻ 26 q10 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q19 ∷
   rw 26 q9 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q10 ∷
   rw 28 q20 ∷
   rw 29 q10 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q14 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q15 ∷
   rw 29 q21 ∷
   rw 28 q17 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q10 ∷
   rw 29 q18 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q19 ∷
   rw 28 q9 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q10 ∷
   rw 30 q20 ∷
   rw 31 q10 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q14 ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q14 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q17 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 27 5 (CK30 ∷ []) ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q14 ∷
   rw 26 q8 ∷
   rw⁻ 25 q9 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q10 ∷
   rw 25 q18 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q19 ∷
   rw 24 q9 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q10 ∷
   rw 26 q20 ∷
   rw 27 q10 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q14 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 28 q15 ∷
   rw 27 q21 ∷
   rw 26 q17 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q8 ∷
   rw⁻ 27 q9 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q10 ∷
   rw 27 q18 ∷
   rw⁻ 26 q10 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q19 ∷
   rw 26 q9 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q10 ∷
   rw 28 q20 ∷
   rw 29 q10 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q14 ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q10 ∷
   rw 24 q18 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q19 ∷
   rw 23 q9 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q10 ∷
   rw 25 q20 ∷
   rw 26 q10 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q14 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q15 ∷
   rw 26 q21 ∷
   rw 25 q17 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q10 ∷
   rw 26 q18 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q19 ∷
   rw 25 q9 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q10 ∷
   rw 27 q20 ∷
   rw 28 q10 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q14 ∷
   rw 22 q22 ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q10 ∷
   rw 22 q18 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q19 ∷
   rw 21 q9 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q10 ∷
   rw 23 q20 ∷
   rw 24 q10 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q14 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q15 ∷
   rw 24 q21 ∷
   rw 23 q17 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q10 ∷
   rw 24 q18 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q19 ∷
   rw 23 q9 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q10 ∷
   rw 25 q20 ∷
   rw 26 q10 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q14 ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q10 ∷
   rw 21 q18 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q19 ∷
   rw 20 q9 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q10 ∷
   rw 22 q20 ∷
   rw 23 q10 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q14 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q15 ∷
   rw 23 q21 ∷
   rw 22 q17 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q10 ∷
   rw 23 q18 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q19 ∷
   rw 22 q9 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q10 ∷
   rw 24 q20 ∷
   rw 25 q10 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q14 ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q10 ∷
   rw 20 q18 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q19 ∷
   rw 19 q9 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q10 ∷
   rw 21 q20 ∷
   rw 22 q10 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q14 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q15 ∷
   rw 22 q21 ∷
   rw 21 q17 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q10 ∷
   rw 22 q18 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q19 ∷
   rw 21 q9 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q10 ∷
   rw 23 q20 ∷
   rw 24 q10 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q14 ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q10 ∷
   rw 19 q18 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q19 ∷
   rw 18 q9 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q10 ∷
   rw 20 q20 ∷
   rw 21 q10 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q14 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q15 ∷
   rw 21 q21 ∷
   rw 20 q17 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q10 ∷
   rw 21 q18 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q19 ∷
   rw 20 q9 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q10 ∷
   rw 22 q20 ∷
   rw 23 q10 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q14 ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q10 ∷
   rw 18 q18 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q19 ∷
   rw 17 q9 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q10 ∷
   rw 19 q20 ∷
   rw 20 q10 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q14 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q15 ∷
   rw 20 q21 ∷
   rw 19 q17 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q10 ∷
   rw 20 q18 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q19 ∷
   rw 19 q9 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q10 ∷
   rw 21 q20 ∷
   rw 22 q10 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q14 ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q10 ∷
   rw 17 q18 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q19 ∷
   rw 16 q9 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q10 ∷
   rw 18 q20 ∷
   rw 19 q10 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q14 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q15 ∷
   rw 19 q21 ∷
   rw 18 q17 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q10 ∷
   rw 19 q18 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q19 ∷
   rw 18 q9 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q10 ∷
   rw 20 q20 ∷
   rw 21 q10 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q14 ∷
   rw⁻ 15 q23 ∷
   rw⁻ 16 q24 ∷
   rw⁻ 17 q23 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q10 ∷
   rw 15 q11 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q12 ∷
   rw 14 q9 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q10 ∷
   rw 16 q13 ∷
   rw 17 q10 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q14 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 16 5 (CK30 ∷ []) ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q10 ∷
   rw 17 q11 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 17 q12 ∷
   rw 16 q9 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q10 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q14 ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q10 ∷
   rw 14 q18 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   rw 13 q9 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q10 ∷
   rw 15 q20 ∷
   rw 16 q10 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q14 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q15 ∷
   rw 16 q21 ∷
   rw 15 q17 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 15 5 (CS03 ∷ []) ∷
   rw 17 q8 ∷
   rw⁻ 16 q9 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q10 ∷
   rw 16 q18 ∷
   rw⁻ 15 q10 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q19 ∷
   rw 15 q9 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q10 ∷
   rw 17 q20 ∷
   rw 18 q10 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q14 ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q10 ∷
   rw 13 q18 ∷
   rw⁻ 12 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q19 ∷
   rw 12 q9 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q20 ∷
   rw 15 q10 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q14 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q15 ∷
   rw 15 q21 ∷
   rw 14 q17 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q10 ∷
   rw 15 q18 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q19 ∷
   rw 14 q9 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q10 ∷
   rw 16 q20 ∷
   rw 17 q10 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q14 ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q18 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q19 ∷
   rw 11 q9 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q20 ∷
   rw 14 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q14 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 15 q15 ∷
   rw 14 q21 ∷
   rw 13 q17 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q10 ∷
   rw 14 q18 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   rw 13 q9 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q10 ∷
   rw 15 q20 ∷
   rw 16 q10 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q14 ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q23 ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q12 ∷
   rw 9 q9 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q13 ∷
   rw 12 q10 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q14 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 11 5 (CK30 ∷ []) ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q11 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 12 q12 ∷
   rw 11 q9 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q13 ∷
   rw 14 q10 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q14 ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q23 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 8 q12 ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q13 ∷
   rw 10 q10 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   re 9 5 (CK30 ∷ []) ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q12 ∷
   rw 9 q9 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q13 ∷
   rw 12 q10 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q14 ∷
   rw 6 q22 ∷
   rw 5 q25 ∷
   rw 4 q25 ∷
   rw 3 q26 ∷
   rw 2 q25 ∷
   rw 1 q26 ∷
   rw 0 q26 ∷
   rw 32 q1 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 18 q27 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q27 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw 11 q27 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   rw 6 q3 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q3 ∷
   rw 4 q28 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q3 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 22 q3 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q3 ∷
   rw 27 q1 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 31 q2 ∷
   rw 32 q4 ∷ []) Eq.refl
