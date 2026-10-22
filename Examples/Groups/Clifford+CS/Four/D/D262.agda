{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D262 (W : Ws) where

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
  q3 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q4 : Eqn
  q4 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q5 : Eqn
  q5 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q6 : Eqn
  q6 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q8 : Eqn
  q8 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q9 : Eqn
  q9 = wE 849 W
  q10 : Eqn
  q10 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q11 : Eqn
  q11 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q12 : Eqn
  q12 = eqn (S1 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = eqn (S1 ∷ CS23 ∷ []) (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 850 W
  q22 : Eqn
  q22 = wE 142 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = wE 7 W
  q25 : Eqn
  q25 = wE 851 W
  q26 : Eqn
  q26 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd23 CKd32 CS23 CS23 X3]: 278 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-CKd32-CS23-CS23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-CKd32-CS23-CS23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q4 ∷
   rw 33 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q4 ∷
   rw 32 q1 ∷
   rw 26 q5 ∷
   rw 27 q6 ∷
   rw 28 q7 ∷
   rw 29 q8 ∷
   rw 30 q8 ∷
   rw 31 q5 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q4 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   rw 24 q5 ∷
   rw 25 q6 ∷
   rw 26 q7 ∷
   rw 27 q8 ∷
   rw 28 q8 ∷
   rw 29 q5 ∷
   rw 23 q5 ∷
   rw 24 q6 ∷
   rw 25 q7 ∷
   rw 26 q8 ∷
   rw 27 q8 ∷
   rw 28 q5 ∷
   rw 22 q9 ∷
   rw 21 q5 ∷
   rw 22 q6 ∷
   rw 23 q7 ∷
   rw 24 q8 ∷
   rw 25 q8 ∷
   rw 26 q5 ∷
   rw 20 q5 ∷
   rw 21 q6 ∷
   rw 22 q7 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q5 ∷
   rw 19 q5 ∷
   rw 20 q6 ∷
   rw 21 q7 ∷
   rw 22 q8 ∷
   rw 23 q8 ∷
   rw 24 q5 ∷
   rw 18 q5 ∷
   rw 19 q6 ∷
   rw 20 q7 ∷
   rw 21 q8 ∷
   rw 22 q8 ∷
   rw 23 q5 ∷
   rw 17 q5 ∷
   rw 18 q6 ∷
   rw 19 q7 ∷
   rw 20 q8 ∷
   rw 21 q8 ∷
   rw 22 q5 ∷
   rw 16 q5 ∷
   rw 17 q6 ∷
   rw 18 q7 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q5 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q10 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q4 ∷
   rw 19 q1 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q8 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 12 q5 ∷
   rw 13 q6 ∷
   rw 14 q7 ∷
   rw 15 q8 ∷
   rw 16 q8 ∷
   rw 17 q5 ∷
   rw 11 q5 ∷
   rw 12 q6 ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   rw 16 q5 ∷
   rw 10 q10 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q13 ∷
   rw 14 q13 ∷
   rw 15 q10 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q4 ∷
   rw 14 q1 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q10 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q3 ∷
   rw 10 q4 ∷
   rw 11 q4 ∷
   rw 12 q1 ∷
   rw 6 q9 ∷
   rw 12 q14 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q15 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q19 ∷
   rw 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q15 ∷
   rw 6 q18 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   rw 12 q22 ∷
   rw 13 q19 ∷
   re 11 3 (CK30 ∷ []) ∷
   rw 12 q23 ∷
   rw 11 q14 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q15 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q21 ∷
   rw 4 q15 ∷
   rw 5 q18 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q19 ∷
   rw 11 q22 ∷
   rw 12 q19 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q14 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q15 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 4 q24 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q25 ∷
   rw 3 q15 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   rw 6 q16 ∷
   rw 7 q16 ∷
   rw 8 q15 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   rw 10 q26 ∷
   rw 11 q19 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q23 ∷
   rw 9 q14 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q16 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q15 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q19 ∷
   rw 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q21 ∷
   rw 2 q15 ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   rw 5 q16 ∷
   rw 6 q16 ∷
   rw 7 q15 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 9 q22 ∷
   rw 10 q19 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q14 ∷
   rw⁻ 7 q15 ∷
   rw⁻ 6 q16 ∷
   rw⁻ 5 q16 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q18 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 2 q24 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q25 ∷
   rw 1 q15 ∷
   rw 2 q18 ∷
   rw 3 q17 ∷
   rw 4 q16 ∷
   rw 5 q16 ∷
   rw 6 q15 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   rw 8 q26 ∷
   rw 9 q19 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q23 ∷
   rw 7 q14 ∷
   rw⁻ 6 q15 ∷
   rw⁻ 5 q16 ∷
   rw⁻ 4 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw⁻ 1 q15 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q19 ∷
   rw 1 q24 ∷
   rw⁻ 0 q19 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q25 ∷
   rw 0 q15 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   rw 4 q16 ∷
   rw 5 q15 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q26 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q23 ∷ []) Eq.refl
