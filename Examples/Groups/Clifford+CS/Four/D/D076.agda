{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D076 (W : Ws) where

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
  q1 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q2 : Eqn
  q2 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q3 : Eqn
  q3 = wE 411 W
  q4 : Eqn
  q4 = eqn (S1 ∷ CS23 ∷ []) (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS))
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 140 W
  q9 : Eqn
  q9 = wE 588 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 410 W
  q14 : Eqn
  q14 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CS23]: 113 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS23 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS23 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS23 ∷ []) (CS23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q1 ∷
   rw 27 q1 ∷
   rw 26 q2 ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw 21 q2 ∷
   rw 20 q2 ∷
   rw 19 q2 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   rw 16 q2 ∷
   rw 15 q4 ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q4 ∷
   rw 9 q1 ∷
   rw 8 q4 ∷
   rw 7 q1 ∷
   rw 6 q3 ∷
   rw 7 q5 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q8 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q9 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q11 ∷
   rw 6 q5 ∷
   rw⁻ 5 q6 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q9 ∷
   rw 4 q6 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q11 ∷
   rw 5 q5 ∷
   rw⁻ 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q12 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q13 ∷
   rw 3 q6 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q14 ∷
   rw 6 q7 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q11 ∷
   rw 4 q5 ∷
   rw⁻ 3 q6 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q8 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q9 ∷
   rw 2 q6 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q5 ∷
   rw⁻ 2 q6 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q12 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q13 ∷
   rw 1 q6 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q14 ∷
   rw 4 q7 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q11 ∷
   rw 2 q5 ∷
   rw⁻ 1 q6 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q7 ∷
   rw 1 q12 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q13 ∷
   rw 0 q6 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q14 ∷
   rw 3 q7 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q11 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q20 : Eqn
  q20 = wE 583 W
  q21 : Eqn
  q21 = wE 151 W
  q22 : Eqn
  q22 = wE 157 W
  q23 : Eqn
  q23 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q24 : Eqn
  q24 = wE 158 W
  q25 : Eqn
  q25 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q26 : Eqn
  q26 = wE 589 W
  q27 : Eqn
  q27 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q28 : Eqn
  q28 = wE 590 W
  q29 : Eqn
  q29 = wE 591 W
  q30 : Eqn
  q30 = wE 464 W
  q31 : Eqn
  q31 = wE 586 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CX12]: 351 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CX12 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CX12 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ []) (CX12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw 15 q19 ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw 10 q19 ∷
   rw 9 q16 ∷
   rw 8 q19 ∷
   rw 7 q16 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q20 ∷
   rw⁻ 0 q17 ∷
   rw⁻ 1 q17 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 4 q16 ∷
   rw⁻ 5 q16 ∷
   rw 8 q15 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q21 ∷
   rw 11 q15 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q21 ∷
   rw 13 q15 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q15 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q15 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q21 ∷
   rw 18 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q15 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q18 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q22 ∷
   rw 30 q23 ∷
   rw 29 q24 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q22 ∷
   rw 29 q23 ∷
   rw 28 q24 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q22 ∷
   rw 28 q25 ∷
   rw 27 q24 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q22 ∷
   rw 27 q23 ∷
   rw 26 q24 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 26 5 (CK30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q22 ∷
   rw 26 q25 ∷
   rw 25 q24 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q22 ∷
   rw 25 q25 ∷
   rw 24 q24 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q26 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q22 ∷
   rw 23 q25 ∷
   rw 22 q24 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q22 ∷
   rw 22 q25 ∷
   rw 21 q24 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q22 ∷
   rw 21 q25 ∷
   rw 20 q24 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q22 ∷
   rw 20 q25 ∷
   rw 19 q24 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 20 q22 ∷
   rw 19 q25 ∷
   rw 18 q24 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 19 q22 ∷
   rw 18 q25 ∷
   rw 17 q24 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw⁻ 15 q27 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 17 q22 ∷
   rw 16 q23 ∷
   rw 15 q24 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 16 q22 ∷
   rw 15 q25 ∷
   rw 14 q24 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 15 q22 ∷
   rw 14 q25 ∷
   rw 13 q24 ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q18 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 14 q22 ∷
   rw 13 q25 ∷
   rw 12 q24 ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw⁻ 10 q27 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 12 q22 ∷
   rw 11 q23 ∷
   rw 10 q24 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 10 5 (CK30 ∷ []) ∷
   rw⁻ 8 q27 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   re 11 3 (CX13 ∷ []) ∷
   rw 10 q22 ∷
   rw 9 q23 ∷
   rw 8 q24 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   re 8 5 (CK30 ∷ []) ∷
   rw 6 q26 ∷
   rw 5 q28 ∷
   rw 4 q28 ∷
   rw 3 q29 ∷
   rw 2 q28 ∷
   rw 1 q29 ∷
   rw 0 q29 ∷
   rw 30 q15 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q18 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   rw 16 q30 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   rw 11 q30 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q18 ∷
   rw 9 q30 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q18 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw 6 q16 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   rw 1 q17 ∷
   rw 2 q31 ∷
   rw 3 q15 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q15 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q15 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw⁻ 8 q16 ∷
   rw⁻ 9 q19 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q19 ∷
   rw⁻ 12 q17 ∷
   rw⁻ 13 q17 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q17 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q17 ∷
   rw⁻ 20 q17 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q17 ∷
   rw 25 q15 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw⁻ 24 q17 ∷
   rw⁻ 25 q17 ∷
   rw⁻ 26 q16 ∷
   rw⁻ 27 q17 ∷
   rw⁻ 28 q16 ∷
   rw⁻ 29 q16 ∷
   rw 30 q18 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q33 : Eqn
  q33 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q34 : Eqn
  q34 = wE 592 W
  q35 : Eqn
  q35 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q37 : Eqn
  q37 = wE 593 W
  q38 : Eqn
  q38 = wE 433 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CSd23]: 113 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd23 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd23 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q32 ∷
   rw 27 q32 ∷
   rw 26 q33 ∷
   rw 25 q32 ∷
   rw 24 q33 ∷
   rw 23 q33 ∷
   rw 22 q34 ∷
   rw 21 q33 ∷
   rw 20 q33 ∷
   rw 19 q33 ∷
   rw 18 q33 ∷
   rw 17 q33 ∷
   rw 16 q33 ∷
   rw 15 q35 ∷
   rw 14 q32 ∷
   rw 13 q33 ∷
   rw 12 q33 ∷
   rw 11 q33 ∷
   rw 10 q35 ∷
   rw 9 q32 ∷
   rw 8 q35 ∷
   rw 7 q32 ∷
   rw 6 q34 ∷
   rw 7 q5 ∷
   rw⁻ 6 q36 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q8 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q37 ∷
   rw 5 q36 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q11 ∷
   rw 6 q5 ∷
   rw⁻ 5 q36 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q37 ∷
   rw 4 q36 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q11 ∷
   rw 5 q5 ∷
   rw⁻ 4 q36 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q12 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q38 ∷
   rw 3 q36 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q14 ∷
   rw 6 q7 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q11 ∷
   rw 4 q5 ∷
   rw⁻ 3 q36 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q8 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q37 ∷
   rw 2 q36 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q5 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q12 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q38 ∷
   rw 1 q36 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q14 ∷
   rw 4 q7 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q11 ∷
   rw 2 q5 ∷
   rw⁻ 1 q36 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q7 ∷
   rw 1 q12 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q38 ∷
   rw 0 q36 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q14 ∷
   rw 3 q7 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q11 ∷ []) Eq.refl
