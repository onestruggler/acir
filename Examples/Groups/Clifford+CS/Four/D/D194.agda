{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D194 (W : Ws) where

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
  q1 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q2 : Eqn
  q2 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q3 : Eqn
  q3 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q6 : Eqn
  q6 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q7 : Eqn
  q7 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q8 : Eqn
  q8 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = eqn (CX31 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CX31 ∷ []) (wn 758 W)
  q10 : Eqn
  q10 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q11 : Eqn
  q11 = eqn (S1 ∷ CK32 ∷ []) (CK32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CK₁₀))
  q12 : Eqn
  q12 = eqn (S1 ∷ CS23 ∷ []) (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS))
  q13 : Eqn
  q13 = eqn (S1 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q21 : Eqn
  q21 = eqn (CS13 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ []) (wn 760 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q24 : Eqn
  q24 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q25 : Eqn
  q25 = eqn (CK31 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CK31 ∷ []) (wn 759 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK32 CS23 CS23 CKd32 X3]: 290 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-CS23-CS23-CKd32-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-CS23-CS23-CKd32-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q3 ∷
   rw 33 q3 ∷
   rw 34 q4 ∷
   rw 35 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q3 ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q1 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q7 ∷
   rw 31 q7 ∷
   rw 32 q8 ∷
   rw 33 q5 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q3 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   rw 24 q9 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q3 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q3 ∷
   rw 25 q3 ∷
   rw 26 q4 ∷
   rw 27 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q3 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q3 ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q3 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q1 ∷
   rw 15 q1 ∷
   rw 16 q2 ∷
   rw 17 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q1 ∷
   rw 14 q10 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q12 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q7 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q3 ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q1 ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q3 ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q1 ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q3 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q1 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q1 ∷
   rw 8 q1 ∷
   rw 9 q2 ∷
   rw 10 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q1 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q3 ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q1 ∷
   rw 6 q9 ∷
   rw 12 q14 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q15 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q19 ∷
   rw 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q15 ∷
   rw 6 q18 ∷
   rw 7 q17 ∷
   rw 8 q17 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   rw 12 q22 ∷
   rw 13 q19 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q23 ∷
   rw 11 q14 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q15 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q21 ∷
   rw 4 q15 ∷
   rw 5 q18 ∷
   rw 6 q17 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q19 ∷
   rw 11 q22 ∷
   rw 12 q19 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q14 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q15 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 4 q24 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q25 ∷
   rw 3 q15 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   rw 8 q15 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   rw 10 q26 ∷
   rw 11 q19 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q23 ∷
   rw 9 q14 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q15 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q19 ∷
   rw 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 3 q21 ∷
   rw 2 q15 ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   rw 5 q17 ∷
   rw 6 q16 ∷
   rw 7 q15 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 9 q22 ∷
   rw 10 q19 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q14 ∷
   rw⁻ 7 q15 ∷
   rw⁻ 6 q16 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q18 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q21 ∷
   rw 1 q15 ∷
   rw 2 q18 ∷
   rw 3 q17 ∷
   rw 4 q17 ∷
   rw 5 q16 ∷
   rw 6 q15 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   rw 8 q22 ∷
   rw 9 q19 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q23 ∷
   rw 7 q14 ∷
   rw⁻ 6 q15 ∷
   rw⁻ 5 q16 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw⁻ 1 q15 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q19 ∷
   rw 1 q20 ∷
   rw⁻ 0 q19 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q21 ∷
   rw 0 q15 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   rw 3 q17 ∷
   rw 4 q16 ∷
   rw 5 q15 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q22 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q23 ∷ []) Eq.refl
