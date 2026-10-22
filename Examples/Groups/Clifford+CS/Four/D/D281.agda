{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D281 (W : Ws) where

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
  q1 = wE 866 W

-- groups [CSd23 CKd32 CS23 CS23] [X3 TOFF123 X3]: 1 steps
lem-groups-CSd23-CKd32-CS23-CS23-vs-X3-TOFF123-X3 : ⟪ (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-groups-CSd23-CKd32-CS23-CS23-vs-X3-TOFF123-X3 = derive (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ [])
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = wE 867 W

-- groups [CX31] [X3 TOFF123 X3]: 1 steps
lem-groups-CX31-vs-X3-TOFF123-X3 : ⟪ (CX31 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CX31 ∷ []) ⟫ʷ
lem-groups-CX31-vs-X3-TOFF123-X3 = derive (CX31 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CX31 ∷ [])
  (rw 0 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q4 : Eqn
  q4 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q6 : Eqn
  q6 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q7 : Eqn
  q7 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q8 : Eqn
  q8 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q10 : Eqn
  q10 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q11 : Eqn
  q11 = wE 849 W
  q12 : Eqn
  q12 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q13 : Eqn
  q13 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q14 : Eqn
  q14 = eqn (S1 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q15 : Eqn
  q15 = eqn (S1 ∷ CS23 ∷ []) (CS23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CS))
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 851 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 140 W
  q27 : Eqn
  q27 = wE 850 W
  q28 : Eqn
  q28 = wE 142 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CSd23 CKd32 CS23 CS23 X3]: 290 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-CKd32-CS23-CS23-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-CKd32-CS23-CS23-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   rw 35 q3 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw 33 q6 ∷
   rw 34 q3 ∷
   rw 28 q7 ∷
   rw 29 q8 ∷
   rw 30 q9 ∷
   rw 31 q10 ∷
   rw 32 q10 ∷
   rw 33 q7 ∷
   rw 27 q3 ∷
   rw 28 q4 ∷
   rw 29 q5 ∷
   rw 30 q6 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   rw 25 q3 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q6 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   rw 24 q11 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q5 ∷
   rw 26 q6 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q5 ∷
   rw 25 q6 ∷
   rw 26 q6 ∷
   rw 27 q3 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q5 ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q5 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q5 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q5 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q5 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q5 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q3 ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q5 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q3 ∷
   rw 14 q12 ∷
   rw 15 q13 ∷
   rw 16 q14 ∷
   rw 17 q15 ∷
   rw 18 q15 ∷
   rw 19 q12 ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q10 ∷
   rw 18 q7 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q6 ∷
   rw 16 q6 ∷
   rw 17 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q3 ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q5 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q3 ∷
   rw 9 q3 ∷
   rw 10 q4 ∷
   rw 11 q5 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q3 ∷
   rw 8 q3 ∷
   rw 9 q4 ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 12 q6 ∷
   rw 13 q3 ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   rw 6 q11 ∷
   rw 12 q16 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 10 q18 ∷
   rw⁻ 9 q18 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 6 q17 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q21 ∷
   rw 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 6 q23 ∷
   rw 5 q17 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   rw 8 q18 ∷
   rw 9 q18 ∷
   rw 10 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 12 q24 ∷
   rw 13 q21 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q25 ∷
   rw 11 q16 ∷
   rw⁻ 10 q17 ∷
   rw⁻ 9 q18 ∷
   rw⁻ 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw⁻ 5 q17 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q21 ∷
   rw 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q23 ∷
   rw 4 q17 ∷
   rw 5 q20 ∷
   rw 6 q19 ∷
   rw 7 q18 ∷
   rw 8 q18 ∷
   rw 9 q17 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q24 ∷
   rw 12 q21 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q25 ∷
   rw 10 q16 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 8 q18 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 4 q17 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q21 ∷
   rw 4 q26 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q27 ∷
   rw 3 q17 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   rw 6 q18 ∷
   rw 7 q18 ∷
   rw 8 q17 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q28 ∷
   rw 11 q21 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q25 ∷
   rw 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 3 q17 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q21 ∷
   rw 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 3 q23 ∷
   rw 2 q17 ∷
   rw 3 q20 ∷
   rw 4 q19 ∷
   rw 5 q18 ∷
   rw 6 q18 ∷
   rw 7 q17 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q24 ∷
   rw 10 q21 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q25 ∷
   rw 8 q16 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw⁻ 2 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q21 ∷
   rw 2 q22 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q23 ∷
   rw 1 q17 ∷
   rw 2 q20 ∷
   rw 3 q19 ∷
   rw 4 q18 ∷
   rw 5 q18 ∷
   rw 6 q17 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q25 ∷
   rw 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q21 ∷
   rw 1 q22 ∷
   rw⁻ 0 q21 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q23 ∷
   rw 0 q17 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   rw 3 q18 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q24 ∷
   rw 8 q21 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q25 ∷ []) Eq.refl
