{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D077 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 594 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CKd31 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd31-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CK31⁻ ∷ []) ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw 27 q1 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q10 : Eqn
  q10 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q11 : Eqn
  q11 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q13 : Eqn
  q13 = eqn (CX31 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CX31 ∷ []) (wn 595 W)
  q14 : Eqn
  q14 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q15 : Eqn
  q15 = eqn (S1 ∷ CS23 ∷ []) (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS))
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q21 : Eqn
  q21 = eqn (CK31 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CK31 ∷ []) (wn 596 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q24 : Eqn
  q24 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q25 : Eqn
  q25 = eqn (CS13 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CS13 ∷ []) (wn 597 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS23 X3]: 179 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q9 ∷
   rw 29 q10 ∷
   rw 30 q9 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q9 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q11 ∷
   rw 24 q12 ∷
   rw 25 q11 ∷
   rw 22 q13 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 17 q11 ∷
   rw 18 q12 ∷
   rw 19 q11 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q11 ∷
   rw 15 q14 ∷
   rw 16 q15 ∷
   rw 17 q14 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q9 ∷
   rw 13 q11 ∷
   rw 14 q12 ∷
   rw 15 q11 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q11 ∷
   rw 10 q14 ∷
   rw 11 q15 ∷
   rw 12 q14 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q9 ∷
   rw 8 q14 ∷
   rw 9 q15 ∷
   rw 10 q14 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 6 q13 ∷
   rw 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q17 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q19 ∷
   rw 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 7 q17 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 9 q22 ∷
   rw 10 q19 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q16 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q17 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q21 ∷
   rw 4 q17 ∷
   rw 5 q18 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   rw 8 q22 ∷
   rw 9 q19 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q23 ∷
   rw 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q19 ∷
   rw 4 q24 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q25 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q26 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q16 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q17 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q19 ∷
   rw 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q21 ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q22 ∷
   rw 7 q19 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q23 ∷
   rw 5 q16 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q18 ∷
   rw⁻ 2 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q19 ∷
   rw 2 q24 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q25 ∷
   rw 1 q17 ∷
   rw 2 q18 ∷
   rw 3 q17 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q19 ∷
   rw 5 q26 ∷
   rw 6 q19 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q23 ∷
   rw 4 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw⁻ 1 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q19 ∷
   rw 1 q24 ∷
   rw⁻ 0 q19 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q25 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q26 ∷
   rw 5 q19 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q23 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 583 W)
  q28 : Eqn
  q28 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ CK13 ∷ []) (CK23 ∷ Sw12 ∷ []) (wn 352 W)
  q30 : Eqn
  q30 = eqn (CK10 ∷ CK23 ∷ []) (CK23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₀₁))
  q31 : Eqn
  q31 = eqn (Sw12 ∷ CK23 ∷ []) (CK13 ∷ Sw12 ∷ []) (wn 357 W)
  q32 : Eqn
  q32 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q33 : Eqn
  q33 = eqn (CX13 ∷ CK12 ∷ []) (CK12 ∷ CX13 ∷ []) (wn 598 W)
  q34 : Eqn
  q34 = eqn (CK12 ∷ S3 ∷ []) (S3 ∷ CK12 ∷ []) (low₃-comm ((CK₀₁ ↑)) (S))
  q35 : Eqn
  q35 = eqn (CK10 ∷ CK12 ∷ []) (CK12 ∷ CK10 ∷ []) (wn 599 W)
  q36 : Eqn
  q36 = eqn (CS01 ∷ CK12 ∷ []) (CK12 ∷ CS01 ∷ []) (wn 600 W)
  q37 : Eqn
  q37 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q38 : Eqn
  q38 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 586 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CK12]: 351 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CK12 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CK12 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CK12 ∷ []) (CK12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 29 q1 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q27 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q28 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q28 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q28 ∷
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
   rw 29 q3 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CK13 ∷ []) ∷
   rw 31 q29 ∷
   rw 30 q30 ∷
   rw 29 q31 ∷
   re 29 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK13 ∷ []) ∷
   rw 30 q29 ∷
   rw 29 q30 ∷
   rw 28 q31 ∷
   re 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CK13 ∷ []) ∷
   rw 29 q29 ∷
   rw 28 q32 ∷
   rw 27 q31 ∷
   re 27 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw 28 q29 ∷
   rw 27 q30 ∷
   rw 26 q31 ∷
   re 26 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 26 5 (CK30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK13 ∷ []) ∷
   rw 27 q29 ∷
   rw 26 q32 ∷
   rw 25 q31 ∷
   re 25 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CK13 ∷ []) ∷
   rw 26 q29 ∷
   rw 25 q32 ∷
   rw 24 q31 ∷
   re 24 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q33 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CK13 ∷ []) ∷
   rw 24 q29 ∷
   rw 23 q32 ∷
   rw 22 q31 ∷
   re 22 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CK13 ∷ []) ∷
   rw 23 q29 ∷
   rw 22 q32 ∷
   rw 21 q31 ∷
   re 21 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CK13 ∷ []) ∷
   rw 22 q29 ∷
   rw 21 q32 ∷
   rw 20 q31 ∷
   re 20 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CK13 ∷ []) ∷
   rw 21 q29 ∷
   rw 20 q32 ∷
   rw 19 q31 ∷
   re 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CK13 ∷ []) ∷
   rw 20 q29 ∷
   rw 19 q32 ∷
   rw 18 q31 ∷
   re 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CK13 ∷ []) ∷
   rw 19 q29 ∷
   rw 18 q32 ∷
   rw 17 q31 ∷
   re 17 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw⁻ 15 q34 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CK13 ∷ []) ∷
   rw 17 q29 ∷
   rw 16 q30 ∷
   rw 15 q31 ∷
   re 15 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CK13 ∷ []) ∷
   rw 16 q29 ∷
   rw 15 q32 ∷
   rw 14 q31 ∷
   re 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CK13 ∷ []) ∷
   rw 15 q29 ∷
   rw 14 q32 ∷
   rw 13 q31 ∷
   re 13 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CK13 ∷ []) ∷
   rw 14 q29 ∷
   rw 13 q32 ∷
   rw 12 q31 ∷
   re 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw⁻ 10 q34 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CK13 ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 10 q31 ∷
   re 10 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   re 10 5 (CK30 ∷ []) ∷
   rw⁻ 8 q34 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   rw 8 q31 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 8 5 (CK30 ∷ []) ∷
   rw 6 q33 ∷
   rw 5 q35 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q35 ∷
   rw 1 q36 ∷
   rw 0 q36 ∷
   rw 30 q1 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 11 q37 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 9 q37 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 2 q38 ∷
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
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw 25 q1 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw 30 q3 ∷ []) Eq.refl
