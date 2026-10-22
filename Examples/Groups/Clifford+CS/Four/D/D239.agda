{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D239 (W : Ws) where

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
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 629 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 20 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q11 : Eqn
  q11 = wE 49 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 359 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q15 : Eqn
  q15 = wE 361 W
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 630 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q20 : Eqn
  q20 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q21 : Eqn
  q21 = wE 746 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS12 CS12 CK21 CS12 X2] part0: 500 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CK21-CS12-X2-part0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CK21-CS12-X2-part0 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ X2 ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q7 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 36 q13 ∷
   rw 35 q14 ∷
   rw 34 q15 ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 37 q9 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q5 ∷
   rw 35 q2 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   rw 37 q6 ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q7 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 35 q13 ∷
   rw 34 q14 ∷
   rw 33 q15 ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q8 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 36 q9 ∷
   rw 35 q10 ∷
   rw 34 q11 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q5 ∷
   rw 34 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   rw 36 q6 ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q7 ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q16 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q17 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q18 ∷
   rw 31 q3 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q7 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q19 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q9 ∷
   rw 32 q19 ∷
   rw 31 q11 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 34 q13 ∷
   rw 33 q20 ∷
   rw 32 q15 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 35 q9 ∷
   rw 34 q19 ∷
   rw 33 q11 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 33 5 (CK30 ∷ []) ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q3 ∷
   rw 34 q16 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 34 q17 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 35 q18 ∷
   rw 36 q3 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q7 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q7 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 33 q13 ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 33 q5 ∷
   rw 32 q2 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   rw 34 q6 ∷
   rw 35 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q7 ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q5 ∷
   rw 26 q2 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   rw 28 q6 ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q7 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 32 q13 ∷
   rw 31 q14 ∷
   rw 30 q15 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 5 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q3 ∷
   rw 32 q4 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 32 q5 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 33 q6 ∷
   rw 34 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 33 q7 ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q7 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 31 q13 ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q7 ∷
   rw 24 q21 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q2 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q7 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 28 q9 ∷
   rw 27 q10 ∷
   rw 26 q11 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 29 q13 ∷
   rw 28 q14 ∷
   rw 27 q15 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q5 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q7 ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q7 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q8 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q11 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 28 q13 ∷ []) Eq.refl
