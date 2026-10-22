{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D080 (W : Ws) where

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
  q2 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 583 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 21 W
  q9 : Eqn
  q9 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 51 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q12 : Eqn
  q12 = wE 608 W
  q13 : Eqn
  q13 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (S))
  q14 : Eqn
  q14 = wE 609 W
  q15 : Eqn
  q15 = wE 200 W
  q16 : Eqn
  q16 = wE 464 W
  q17 : Eqn
  q17 = wE 586 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CSd12]: 351 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
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
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q8 ∷
   rw 28 q11 ∷
   rw 27 q10 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 26 5 (CK30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 27 q8 ∷
   rw 26 q11 ∷
   rw 25 q10 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 26 q8 ∷
   rw 25 q11 ∷
   rw 24 q10 ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q12 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q8 ∷
   rw 23 q11 ∷
   rw 22 q10 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q8 ∷
   rw 22 q11 ∷
   rw 21 q10 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q8 ∷
   rw 21 q11 ∷
   rw 20 q10 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q8 ∷
   rw 20 q11 ∷
   rw 19 q10 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q8 ∷
   rw 19 q11 ∷
   rw 18 q10 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 19 q8 ∷
   rw 18 q11 ∷
   rw 17 q10 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw⁻ 15 q13 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q8 ∷
   rw 15 q11 ∷
   rw 14 q10 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q8 ∷
   rw 14 q11 ∷
   rw 13 q10 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q8 ∷
   rw 13 q11 ∷
   rw 12 q10 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw⁻ 10 q13 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 10 5 (CK30 ∷ []) ∷
   rw⁻ 8 q13 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   re 8 5 (CK30 ∷ []) ∷
   rw 6 q12 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q15 ∷
   rw 30 q1 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q16 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw 11 q16 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q16 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 2 q17 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 22 q3 ∷
   rw 25 q1 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 29 q2 ∷
   rw 30 q4 ∷ []) Eq.refl
