{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D117 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 630 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 359 W
  q10 : Eqn
  q10 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q11 : Eqn
  q11 = wE 361 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 629 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q17 : Eqn
  q17 = wE 631 W
  q18 : Eqn
  q18 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q19 : Eqn
  q19 = eqn (CK21 ∷ S3 ∷ []) (S3 ∷ CK21 ∷ []) (low₃-comm ((CK₁₀ ↑)) (S))
  q20 : Eqn
  q20 = wE 496 W
  q21 : Eqn
  q21 = wE 497 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 X2]: 719 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q5 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q7 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CK30 ∷ []) ∷
   rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q7 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q7 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 29 5 (CK30 ∷ []) ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q7 ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q3 ∷
   rw 27 q13 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q14 ∷
   rw 26 q2 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   rw 28 q15 ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q7 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 30 q9 ∷
   rw 29 q16 ∷
   rw 28 q11 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q13 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q14 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q15 ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q7 ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q7 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 27 5 (CK30 ∷ []) ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q7 ∷
   rw 26 q1 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q3 ∷
   rw 25 q13 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q14 ∷
   rw 24 q2 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   rw 26 q15 ∷
   rw 27 q3 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q7 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 28 q9 ∷
   rw 27 q16 ∷
   rw 26 q11 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q3 ∷
   rw 27 q13 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q14 ∷
   rw 26 q2 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   rw 28 q15 ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q7 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q13 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q14 ∷
   rw 23 q2 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 25 q15 ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q7 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 27 q9 ∷
   rw 26 q16 ∷
   rw 25 q11 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q3 ∷
   rw 26 q13 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q14 ∷
   rw 25 q2 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 27 q15 ∷
   rw 28 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q7 ∷
   rw 22 q17 ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q3 ∷
   rw 22 q13 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q14 ∷
   rw 21 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q15 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q7 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q8 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 25 q9 ∷
   rw 24 q16 ∷
   rw 23 q11 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q12 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q13 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q14 ∷
   rw 23 q2 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 25 q15 ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q7 ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q3 ∷
   rw 21 q13 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q14 ∷
   rw 20 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 22 q15 ∷
   rw 23 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q7 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q8 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 24 q9 ∷
   rw 23 q16 ∷
   rw 22 q11 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q12 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q13 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q14 ∷
   rw 22 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   rw 24 q15 ∷
   rw 25 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q7 ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q3 ∷
   rw 20 q13 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q14 ∷
   rw 19 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q15 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q7 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q8 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 23 q9 ∷
   rw 22 q16 ∷
   rw 21 q11 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q3 ∷
   rw 22 q13 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q14 ∷
   rw 21 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q15 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q7 ∷
   rw 20 q1 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q13 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q14 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q15 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q7 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 22 q9 ∷
   rw 21 q16 ∷
   rw 20 q11 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q12 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q3 ∷
   rw 21 q13 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q14 ∷
   rw 20 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 22 q15 ∷
   rw 23 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q7 ∷
   rw 19 q1 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 18 q13 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q14 ∷
   rw 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q15 ∷
   rw 20 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q7 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q8 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 21 q9 ∷
   rw 20 q16 ∷
   rw 19 q11 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q3 ∷
   rw 20 q13 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q14 ∷
   rw 19 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q15 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q7 ∷
   rw 18 q1 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q13 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q14 ∷
   rw 16 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q15 ∷
   rw 19 q3 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q7 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q16 ∷
   rw 18 q11 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q13 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q14 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q15 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q7 ∷
   rw⁻ 15 q18 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw 16 q1 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q4 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q6 ∷
   rw 17 q3 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q7 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q8 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 18 q9 ∷
   rw 17 q10 ∷
   rw 16 q11 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   re 16 5 (CK30 ∷ []) ∷
   rw 18 q1 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q4 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 17 q5 ∷
   rw 16 q2 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q6 ∷
   rw 19 q3 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q7 ∷
   rw 15 q1 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q13 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q14 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q15 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q7 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 17 q9 ∷
   rw 16 q16 ∷
   rw 15 q11 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 15 5 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 16 q13 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q14 ∷
   rw 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 17 q15 ∷
   rw 18 q3 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q7 ∷
   rw 14 q1 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 13 q13 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q14 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q15 ∷
   rw 15 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q7 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 16 q9 ∷
   rw 15 q16 ∷
   rw 14 q11 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q13 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q14 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q15 ∷
   rw 17 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q7 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q13 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q14 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q15 ∷
   rw 14 q3 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q7 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   re 16 3 (CK31 ∷ []) ∷
   rw 15 q9 ∷
   rw 14 q16 ∷
   rw 13 q11 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q13 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q14 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q15 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q7 ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q19 ∷
   rw⁻ 12 q18 ∷
   rw 11 q1 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q7 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q8 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   re 11 5 (CK30 ∷ []) ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q4 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q6 ∷
   rw 14 q3 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q7 ∷
   rw⁻ 8 q18 ∷
   rw⁻ 9 q19 ∷
   rw⁻ 10 q18 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 8 q4 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q6 ∷
   rw 10 q3 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q7 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   re 9 5 (CK30 ∷ []) ∷
   rw 11 q1 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q7 ∷
   rw 6 q17 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷ []) Eq.refl
