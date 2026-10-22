{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D078 (W : Ws) where

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
  q1 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q2 : Eqn
  q2 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 532 W
  q6 : Eqn
  q6 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q7 : Eqn
  q7 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = wE 601 W
  q14 : Eqn
  q14 = wE 142 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 602 W
  q18 : Eqn
  q18 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd23 X3]: 179 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
   rw 22 q5 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   rw 15 q6 ∷
   rw 16 q7 ∷
   rw 17 q6 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 6 q5 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q14 ∷
   rw 10 q11 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q15 ∷
   rw 8 q8 ∷
   rw⁻ 7 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q9 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q13 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q14 ∷
   rw 9 q11 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q9 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q16 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q18 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   rw 6 q8 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q9 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q13 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q14 ∷
   rw 7 q11 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q15 ∷
   rw 5 q8 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q9 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q16 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q9 ∷
   rw 2 q10 ∷
   rw 3 q9 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q18 ∷
   rw 6 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q15 ∷
   rw 4 q8 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q9 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 1 q16 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q17 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q18 ∷
   rw 5 q11 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q15 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = wE 3 W
  q23 : Eqn
  q23 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q24 : Eqn
  q24 = wE 583 W
  q25 : Eqn
  q25 = wE 151 W
  q26 : Eqn
  q26 = wE 353 W
  q27 : Eqn
  q27 = eqn (CK10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S • CK₀₁)))
  q28 : Eqn
  q28 = wE 358 W
  q29 : Eqn
  q29 = eqn (CS01 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S • CK₀₁)))
  q30 : Eqn
  q30 = wE 603 W
  q31 : Eqn
  q31 = eqn (CK12⁻ ∷ S3 ∷ []) (S3 ∷ CK12⁻ ∷ []) (low₃-comm (((S • CK₀₁) ↑)) (S))
  q32 : Eqn
  q32 = wE 604 W
  q33 : Eqn
  q33 = wE 605 W
  q34 : Eqn
  q34 = wE 464 W
  q35 : Eqn
  q35 = wE 586 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CKd12]: 351 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CKd12 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CKd12 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CK12⁻ ∷ []) (CK12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q19 ∷
   rw 28 q20 ∷
   rw 27 q20 ∷
   rw 26 q21 ∷
   rw 25 q20 ∷
   rw 24 q21 ∷
   rw 23 q21 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q22 ∷
   rw 21 q21 ∷
   rw 20 q21 ∷
   rw 19 q21 ∷
   rw 18 q21 ∷
   rw 17 q21 ∷
   rw 16 q21 ∷
   rw 15 q23 ∷
   rw 14 q20 ∷
   rw 13 q21 ∷
   rw 12 q21 ∷
   rw 11 q21 ∷
   rw 10 q23 ∷
   rw 9 q20 ∷
   rw 8 q23 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q24 ∷
   rw⁻ 0 q21 ∷
   rw⁻ 1 q21 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 5 q20 ∷
   rw 8 q19 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw 9 q19 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q25 ∷
   rw 11 q19 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q25 ∷
   rw 13 q19 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q19 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q19 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q25 ∷
   rw 18 q19 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q19 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q22 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   re 32 3 (CK13⁻ ∷ []) ∷
   rw 31 q26 ∷
   rw 30 q27 ∷
   rw 29 q28 ∷
   re 29 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q22 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   re 31 3 (CK13⁻ ∷ []) ∷
   rw 30 q26 ∷
   rw 29 q27 ∷
   rw 28 q28 ∷
   re 28 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q22 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   re 30 3 (CK13⁻ ∷ []) ∷
   rw 29 q26 ∷
   rw 28 q29 ∷
   rw 27 q28 ∷
   re 27 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q22 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 29 3 (CK13⁻ ∷ []) ∷
   rw 28 q26 ∷
   rw 27 q27 ∷
   rw 26 q28 ∷
   re 26 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q22 ∷
   re 26 5 (CK30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CK13⁻ ∷ []) ∷
   rw 27 q26 ∷
   rw 26 q29 ∷
   rw 25 q28 ∷
   re 25 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q22 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CK13⁻ ∷ []) ∷
   rw 26 q26 ∷
   rw 25 q29 ∷
   rw 24 q28 ∷
   re 24 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q22 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q30 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CK13⁻ ∷ []) ∷
   rw 24 q26 ∷
   rw 23 q29 ∷
   rw 22 q28 ∷
   re 22 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q22 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CK13⁻ ∷ []) ∷
   rw 23 q26 ∷
   rw 22 q29 ∷
   rw 21 q28 ∷
   re 21 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q22 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CK13⁻ ∷ []) ∷
   rw 22 q26 ∷
   rw 21 q29 ∷
   rw 20 q28 ∷
   re 20 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q22 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CK13⁻ ∷ []) ∷
   rw 21 q26 ∷
   rw 20 q29 ∷
   rw 19 q28 ∷
   re 19 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q22 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CK13⁻ ∷ []) ∷
   rw 20 q26 ∷
   rw 19 q29 ∷
   rw 18 q28 ∷
   re 18 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q22 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CK13⁻ ∷ []) ∷
   rw 19 q26 ∷
   rw 18 q29 ∷
   rw 17 q28 ∷
   re 17 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q22 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw⁻ 15 q31 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CK13⁻ ∷ []) ∷
   rw 17 q26 ∷
   rw 16 q27 ∷
   rw 15 q28 ∷
   re 15 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q22 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CK13⁻ ∷ []) ∷
   rw 16 q26 ∷
   rw 15 q29 ∷
   rw 14 q28 ∷
   re 14 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q22 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 16 3 (CK13⁻ ∷ []) ∷
   rw 15 q26 ∷
   rw 14 q29 ∷
   rw 13 q28 ∷
   re 13 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q22 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 15 3 (CK13⁻ ∷ []) ∷
   rw 14 q26 ∷
   rw 13 q29 ∷
   rw 12 q28 ∷
   re 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q22 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw⁻ 10 q31 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CK13⁻ ∷ []) ∷
   rw 12 q26 ∷
   rw 11 q27 ∷
   rw 10 q28 ∷
   re 10 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q22 ∷
   re 10 5 (CK30 ∷ []) ∷
   rw⁻ 8 q31 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 11 3 (CK13⁻ ∷ []) ∷
   rw 10 q26 ∷
   rw 9 q27 ∷
   rw 8 q28 ∷
   re 8 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   re 8 5 (CK30 ∷ []) ∷
   rw 6 q30 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q33 ∷
   rw 0 q33 ∷
   rw 30 q19 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q22 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q22 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q22 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q22 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q22 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q22 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q22 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q22 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q22 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q22 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q22 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q22 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q22 ∷
   rw 16 q34 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q22 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q22 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q22 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q22 ∷
   rw 11 q34 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q22 ∷
   rw 9 q34 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q22 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q22 ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   rw 4 q21 ∷
   rw 3 q20 ∷
   rw 2 q21 ∷
   rw 1 q21 ∷
   rw 2 q35 ∷
   rw 3 q19 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q19 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q19 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 6 q19 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q19 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q19 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q19 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw⁻ 8 q20 ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw⁻ 14 q21 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 16 q23 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q21 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 21 q21 ∷
   rw⁻ 22 q21 ∷
   rw 25 q19 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw⁻ 24 q21 ∷
   rw⁻ 25 q21 ∷
   rw⁻ 26 q20 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 28 q20 ∷
   rw⁻ 29 q20 ∷
   rw 30 q22 ∷ []) Eq.refl
