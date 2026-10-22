{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D172 (W : Ws) where

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
  q2 = wE 49 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 20 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 629 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 21 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q15 : Eqn
  q15 = wE 51 W
  q16 : Eqn
  q16 = wE 360 W
  q17 : Eqn
  q17 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q18 : Eqn
  q18 = wE 362 W
  q19 : Eqn
  q19 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q20 : Eqn
  q20 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (S))
  q21 : Eqn
  q21 = eqn (CK21⁻ ∷ S3 ∷ []) (S3 ∷ CK21⁻ ∷ []) (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q22 : Eqn
  q22 = eqn (CS12 ∷ S3 ∷ []) (S3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (S))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 630 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q27 : Eqn
  q27 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q28 : Eqn
  q28 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd12 CKd21 CS12 CS12 X2] part1: 500 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part1 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part1 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 25 q1 ∷
   rw 24 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q5 ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q6 ∷
   rw⁻ 26 q7 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q8 ∷
   rw 26 q9 ∷
   rw⁻ 25 q8 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q10 ∷
   rw 25 q7 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q8 ∷
   rw 27 q11 ∷
   rw 28 q8 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q12 ∷
   rw 21 q6 ∷
   rw⁻ 20 q7 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q8 ∷
   rw 20 q9 ∷
   rw⁻ 19 q8 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q10 ∷
   rw 19 q7 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   rw 21 q11 ∷
   rw 22 q8 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q12 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q13 ∷
   rw 22 q14 ∷
   rw 21 q15 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q5 ∷
   rw 24 q1 ∷
   rw 23 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 26 q6 ∷
   rw⁻ 25 q7 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q8 ∷
   rw 25 q9 ∷
   rw⁻ 24 q8 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q10 ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   rw 26 q11 ∷
   rw 27 q8 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q12 ∷
   rw 20 q6 ∷
   rw⁻ 19 q7 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q8 ∷
   rw 19 q9 ∷
   rw⁻ 18 q8 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q10 ∷
   rw 18 q7 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   rw 20 q11 ∷
   rw 21 q8 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q12 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   rw 21 q18 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q5 ∷
   rw 24 q1 ∷
   rw 23 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q6 ∷
   rw⁻ 24 q7 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q8 ∷
   rw 24 q9 ∷
   rw⁻ 23 q8 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q10 ∷
   rw 23 q7 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q8 ∷
   rw 25 q11 ∷
   rw 26 q8 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q12 ∷
   rw 19 q6 ∷
   rw⁻ 18 q7 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q8 ∷
   rw 18 q9 ∷
   rw⁻ 17 q8 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q10 ∷
   rw 17 q7 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   rw 19 q11 ∷
   rw 20 q8 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q12 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q13 ∷
   rw 20 q14 ∷
   rw 19 q15 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   rw 20 q18 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q6 ∷
   rw⁻ 23 q7 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q8 ∷
   rw 23 q9 ∷
   rw⁻ 22 q8 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q10 ∷
   rw 22 q7 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   rw 24 q11 ∷
   rw 25 q8 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q12 ∷
   rw 18 q6 ∷
   rw⁻ 17 q7 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q8 ∷
   rw 17 q9 ∷
   rw⁻ 16 q8 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q10 ∷
   rw 16 q7 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q8 ∷
   rw 18 q11 ∷
   rw 19 q8 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q12 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q13 ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   rw 19 q18 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q5 ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q6 ∷
   rw⁻ 22 q7 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q8 ∷
   rw 22 q9 ∷
   rw⁻ 21 q8 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q10 ∷
   rw 21 q7 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q8 ∷
   rw 23 q11 ∷
   rw 24 q8 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q12 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q20 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q22 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q19 ∷
   rw 16 q6 ∷
   rw⁻ 15 q7 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q8 ∷
   rw 15 q23 ∷
   rw⁻ 14 q8 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q24 ∷
   rw 14 q7 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   rw 16 q25 ∷
   rw 17 q8 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q12 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw 18 q13 ∷
   rw 17 q26 ∷
   rw 16 q15 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw 19 q16 ∷
   rw 18 q27 ∷
   rw 17 q18 ∷
   re 17 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q28 ∷
   rw 18 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CK30 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q5 ∷
   rw 20 q28 ∷
   rw 19 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CK30 ∷ []) ∷
   rw 21 q6 ∷
   rw⁻ 20 q7 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q8 ∷
   rw 20 q23 ∷
   rw⁻ 19 q8 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 20 q24 ∷
   rw 19 q7 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   rw 21 q25 ∷
   rw 22 q8 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q12 ∷
   rw 15 q6 ∷
   rw⁻ 14 q7 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q8 ∷
   rw 14 q9 ∷
   rw⁻ 13 q8 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q10 ∷
   rw 13 q7 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 15 q11 ∷
   rw 16 q8 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q12 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q13 ∷
   rw 16 q14 ∷
   rw 15 q15 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   rw 16 q18 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q5 ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q6 ∷
   rw⁻ 19 q7 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q8 ∷
   rw 19 q9 ∷
   rw⁻ 18 q8 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q10 ∷
   rw 18 q7 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   rw 20 q11 ∷
   rw 21 q8 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q12 ∷
   rw 14 q6 ∷
   rw⁻ 13 q7 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q8 ∷
   rw 13 q9 ∷
   rw⁻ 12 q8 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q10 ∷
   rw 12 q7 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   rw 14 q11 ∷
   rw 15 q8 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q13 ∷
   rw 15 q14 ∷
   rw 14 q15 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   rw 15 q18 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q5 ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q5 ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q6 ∷
   rw⁻ 18 q7 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q8 ∷
   rw 18 q9 ∷
   rw⁻ 17 q8 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q10 ∷
   rw 17 q7 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   rw 19 q11 ∷
   rw 20 q8 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q12 ∷
   rw 13 q6 ∷
   rw⁻ 12 q7 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷ []) Eq.refl
