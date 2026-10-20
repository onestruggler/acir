{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D213 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q2 : Eqn
  q2 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q6 : Eqn
  q6 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q7 : Eqn
  q7 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q8 : Eqn
  q8 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q12 : Eqn
  q12 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q16 : Eqn
  q16 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q17 : Eqn
  q17 = eqn (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) (wn 361 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q19 : Eqn
  q19 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q20 : Eqn
  q20 = eqn (CK21 ∷ S3 ∷ []) (S3 ∷ CK21 ∷ []) (low₃-comm ((CK₁₀ ↑)) (S))
  q21 : Eqn
  q21 = eqn (CS12 ∷ S3 ∷ []) (S3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (S))
  q22 : Eqn
  q22 = eqn (CK21⁻ ∷ S3 ∷ []) (S3 ∷ CK21⁻ ∷ []) (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q23 : Eqn
  q23 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q24 : Eqn
  q24 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q26 : Eqn
  q26 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q27 : Eqn
  q27 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q28 : Eqn
  q28 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 CS12 CS12 CKd21 X2] part1: 500 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part1 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part1 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 25 q1 ∷
   rw 24 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 28 3 (CK31⁻ ∷ []) ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   re 25 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q14 ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q10 ∷
   rw 20 q11 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q12 ∷
   rw 19 q9 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q10 ∷
   rw 21 q13 ∷
   rw 22 q10 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q14 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 23 q15 ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q18 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q18 ∷
   rw 24 q1 ∷
   rw 23 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q6 ∷
   rw 24 q7 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 26 q8 ∷
   rw⁻ 25 q9 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q10 ∷
   rw 25 q11 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q12 ∷
   rw 24 q9 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q10 ∷
   rw 26 q13 ∷
   rw 27 q10 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q14 ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q10 ∷
   rw 19 q11 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q12 ∷
   rw 18 q9 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q10 ∷
   rw 20 q13 ∷
   rw 21 q10 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q14 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q18 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q18 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q7 ∷
   re 23 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q10 ∷
   rw 24 q11 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q12 ∷
   rw 23 q9 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q10 ∷
   rw 25 q13 ∷
   rw 26 q10 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q14 ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q10 ∷
   rw 18 q11 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q12 ∷
   rw 17 q9 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q10 ∷
   rw 19 q13 ∷
   rw 20 q10 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q14 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q18 ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q18 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q10 ∷
   rw 23 q11 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q12 ∷
   rw 22 q9 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q10 ∷
   rw 24 q13 ∷
   rw 25 q10 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q14 ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q10 ∷
   rw 17 q11 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q12 ∷
   rw 16 q9 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q10 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q14 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 20 q15 ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q18 ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q18 ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q10 ∷
   rw 22 q11 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q12 ∷
   rw 21 q9 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q10 ∷
   rw 23 q13 ∷
   rw 24 q10 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q14 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q20 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q19 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q10 ∷
   rw 15 q23 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q24 ∷
   rw 14 q9 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q10 ∷
   rw 16 q25 ∷
   rw 17 q10 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q14 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 18 q15 ∷
   rw 17 q26 ∷
   rw 16 q17 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q18 ∷
   rw 18 q27 ∷
   rw 17 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q18 ∷
   rw 19 q27 ∷
   rw 18 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CK30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 21 q5 ∷
   rw 20 q28 ∷
   rw 19 q7 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CK30 ∷ []) ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q10 ∷
   rw 20 q23 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 20 q24 ∷
   rw 19 q9 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q10 ∷
   rw 21 q25 ∷
   rw 22 q10 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q14 ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q10 ∷
   rw 14 q11 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q12 ∷
   rw 13 q9 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q10 ∷
   rw 15 q13 ∷
   rw 16 q10 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q14 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 17 q15 ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q18 ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q18 ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CK31⁻ ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q10 ∷
   rw 19 q11 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q12 ∷
   rw 18 q9 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q10 ∷
   rw 20 q13 ∷
   rw 21 q10 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q14 ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q10 ∷
   rw 13 q11 ∷
   rw⁻ 12 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q12 ∷
   rw 12 q9 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q13 ∷
   rw 15 q10 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q14 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 16 q15 ∷
   rw 15 q16 ∷
   rw 14 q17 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q18 ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q18 ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   re 17 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q10 ∷
   rw 18 q11 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q12 ∷
   rw 17 q9 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q10 ∷
   rw 19 q13 ∷
   rw 20 q10 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q14 ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷ []) Eq.refl
