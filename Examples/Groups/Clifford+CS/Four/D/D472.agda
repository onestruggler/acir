{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D472 (W : Ws) where

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
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 464 W
  q4 : Eqn
  q4 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = wE 1223 W
  q7 : Eqn
  q7 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 6 W
  q14 : Eqn
  q14 = wE 892 W
  q15 : Eqn
  q15 = wE 39 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = eqn (S0 ∷ CX32 ∷ []) (CX32 ∷ S0 ∷ []) (low₁-comm (S) ((CX₁₀ ↑)))
  q18 : Eqn
  q18 = wE 893 W
  q19 : Eqn
  q19 = wE 894 W
  q20 : Eqn
  q20 = wE 1224 W
  q21 : Eqn
  q21 = wE 151 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [CX32]: 235 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CX32 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CX32 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (rw 29 q1 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw 24 q1 ∷
   re 22 3 (CX30 ∷ []) ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q4 ∷
   rw 29 q2 ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 24 q10 ∷
   rw⁻ 23 q11 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q12 ∷
   rw 23 q13 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 23 q14 ∷
   rw 22 q11 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   rw 24 q15 ∷
   rw 25 q12 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q16 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q9 ∷
   rw 15 q17 ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q17 ∷
   rw 9 q8 ∷
   rw 8 q17 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   rw⁻ 7 q11 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 7 q13 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 7 q14 ∷
   rw 6 q11 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q18 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 30 q1 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   rw 24 q5 ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q7 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q7 ∷
   rw 10 q4 ∷
   rw 9 q7 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 2 q20 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 9 q21 ∷
   rw 12 q1 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 11 q21 ∷
   rw 14 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 16 q21 ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 30 q2 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 279 W
  q23 : Eqn
  q23 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))
  q24 : Eqn
  q24 = wE 280 W
  q25 : Eqn
  q25 = wE 65 W
  q26 : Eqn
  q26 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q27 : Eqn
  q27 = wE 48 W
  q28 : Eqn
  q28 = wE 76 W
  q29 : Eqn
  q29 = wE 74 W
  q30 : Eqn
  q30 = wE 608 W
  q31 : Eqn
  q31 = wE 29 W
  q32 : Eqn
  q32 = wE 30 W
  q33 : Eqn
  q33 = eqn (CS02⁻ ∷ S3 ∷ []) (S3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (S))
  q34 : Eqn
  q34 = wE 1227 W
  q35 : Eqn
  q35 = wE 88 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [CSd02]: 129 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CSd02 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CSd02 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (re 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 28 q22 ∷
   rw⁻ 29 q23 ∷
   rw 30 q24 ∷
   re 28 3 (CS02⁻ ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 27 q22 ∷
   rw⁻ 28 q23 ∷
   rw 29 q24 ∷
   re 27 3 (CS02⁻ ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 26 q25 ∷
   rw⁻ 27 q26 ∷
   rw 28 q27 ∷
   re 26 3 (CS02⁻ ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 25 q22 ∷
   rw⁻ 26 q23 ∷
   rw 27 q24 ∷
   re 25 3 (CS02⁻ ∷ []) ∷
   re 25 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 24 q25 ∷
   rw⁻ 25 q26 ∷
   rw 26 q27 ∷
   re 24 3 (CS02⁻ ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 23 q25 ∷
   rw⁻ 24 q26 ∷
   rw 25 q27 ∷
   re 23 3 (CS02⁻ ∷ []) ∷
   rw 24 q10 ∷
   rw 23 q28 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q12 ∷
   rw 23 q29 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 23 q30 ∷
   rw 22 q31 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   rw 24 q32 ∷
   rw 25 q12 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q16 ∷
   re 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 21 q25 ∷
   rw⁻ 22 q26 ∷
   rw 23 q27 ∷
   re 21 3 (CS02⁻ ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 20 q25 ∷
   rw⁻ 21 q26 ∷
   rw 22 q27 ∷
   re 20 3 (CS02⁻ ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 19 q25 ∷
   rw⁻ 20 q26 ∷
   rw 21 q27 ∷
   re 19 3 (CS02⁻ ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 18 q25 ∷
   rw⁻ 19 q26 ∷
   rw 20 q27 ∷
   re 18 3 (CS02⁻ ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 17 q25 ∷
   rw⁻ 18 q26 ∷
   rw 19 q27 ∷
   re 17 3 (CS02⁻ ∷ []) ∷
   re 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 16 q25 ∷
   rw⁻ 17 q26 ∷
   rw 18 q27 ∷
   re 16 3 (CS02⁻ ∷ []) ∷
   rw⁻ 15 q33 ∷
   re 15 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 14 q22 ∷
   rw⁻ 15 q23 ∷
   rw 16 q24 ∷
   re 14 3 (CS02⁻ ∷ []) ∷
   re 14 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 13 q25 ∷
   rw⁻ 14 q26 ∷
   rw 15 q27 ∷
   re 13 3 (CS02⁻ ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 12 q25 ∷
   rw⁻ 13 q26 ∷
   rw 14 q27 ∷
   re 12 3 (CS02⁻ ∷ []) ∷
   re 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 11 q25 ∷
   rw⁻ 12 q26 ∷
   rw 13 q27 ∷
   re 11 3 (CS02⁻ ∷ []) ∷
   rw⁻ 10 q33 ∷
   re 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 9 q22 ∷
   rw⁻ 10 q23 ∷
   rw 11 q24 ∷
   re 9 3 (CS02⁻ ∷ []) ∷
   rw⁻ 8 q33 ∷
   re 8 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 7 q22 ∷
   rw⁻ 8 q23 ∷
   rw 9 q24 ∷
   re 7 3 (CS02⁻ ∷ []) ∷
   rw 8 q10 ∷
   rw 7 q28 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 7 q29 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 7 q30 ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q32 ∷
   rw 9 q12 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q34 ∷
   rw 4 q34 ∷
   rw 3 q35 ∷
   rw 2 q34 ∷
   rw 1 q35 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q37 : Eqn
  q37 = wE 1236 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [X0 CKd03 X0]: 109 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CKd03-X0 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CKd03-X0 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX03 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ [])
  (rw 32 q1 ∷
   rw 31 q36 ∷
   re 30 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   rw 29 q36 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q37 ∷
   rw⁻ 0 q36 ∷
   rw 3 q1 ∷
   re 1 3 (CK03⁻ ∷ []) ∷
   rw⁻ 2 q36 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CX03 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 11 q21 ∷
   rw 14 q1 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 13 q21 ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 18 q21 ∷
   rw 21 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 32 q2 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 1106 W
  q39 : Eqn
  q39 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q42 : Eqn
  q42 = wE 27 W
  q43 : Eqn
  q43 = wE 122 W
  q44 : Eqn
  q44 = wE 127 W
  q45 : Eqn
  q45 = wE 7 W
  q46 : Eqn
  q46 = wE 337 W
  q47 : Eqn
  q47 = wE 926 W
  q48 : Eqn
  q48 = wE 317 W
  q49 : Eqn
  q49 = wE 24 W
  q50 : Eqn
  q50 = wE 25 W
  q51 : Eqn
  q51 = wE 124 W

-- pass [TOFF302] [X0 TOFF302 X0]: 123 steps
lem-pass-TOFF302-vs-X0-TOFF302-X0 : ⟪ (Toff302 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff302 ∷ X0 ∷ Toff302 ∷ []) ⟫ʷ
lem-pass-TOFF302-vs-X0-TOFF302-X0 = derive (Toff302 ∷ X0 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ X0 ∷ Toff302 ∷ [])
  (rw 4 q10 ∷
   rw 3 q38 ∷
   re 2 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 3 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 4 q32 ∷
   rw 5 q41 ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q42 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q39 ∷
   rw 9 q43 ∷
   rw 10 q16 ∷
   rw 9 q44 ∷
   rw⁻ 8 q39 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q12 ∷
   rw 8 q45 ∷
   rw⁻ 7 q12 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q29 ∷
   rw⁻ 5 q41 ∷
   rw 4 q29 ∷
   rw⁻ 3 q40 ∷
   rw⁻ 2 q39 ∷
   rw 3 q46 ∷
   re 3 8 (Toff312 ∷ []) ∷
   rw 1 q38 ∷
   re 0 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q32 ∷
   rw 3 q41 ∷
   rw 4 q32 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 6 q42 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q39 ∷
   rw 7 q43 ∷
   rw 8 q16 ∷
   rw 7 q44 ∷
   rw⁻ 6 q39 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q45 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q29 ∷
   rw⁻ 3 q41 ∷
   rw 2 q29 ∷
   rw⁻ 1 q40 ∷
   rw⁻ 0 q39 ∷
   rw 1 q46 ∷
   re 1 8 (Toff312 ∷ []) ∷
   rw 1 q47 ∷
   rw 0 q48 ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 3 q32 ∷
   rw 4 q41 ∷
   rw 5 q32 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q42 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q39 ∷
   rw 8 q43 ∷
   rw 1 q10 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 4 q49 ∷
   rw 5 q41 ∷
   rw 6 q49 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q50 ∷
   rw 9 q12 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q39 ∷
   rw 9 q51 ∷
   rw 2 q46 ∷
   re 2 8 (Toff312 ∷ []) ∷
   re 1 3 (Toff302 ∷ []) ∷
   rw 2 q48 ∷
   re 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 5 q32 ∷
   rw 6 q41 ∷
   rw 7 q32 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q42 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q39 ∷
   rw 10 q43 ∷
   rw 3 q10 ∷
   rw 4 q39 ∷
   rw 5 q40 ∷
   rw 6 q49 ∷
   rw 7 q41 ∷
   rw 8 q49 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q50 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q39 ∷
   rw 11 q51 ∷
   rw 4 q46 ∷
   re 4 8 (Toff312 ∷ []) ∷
   re 3 3 (Toff302 ∷ []) ∷
   rw 4 q16 ∷ []) Eq.refl
