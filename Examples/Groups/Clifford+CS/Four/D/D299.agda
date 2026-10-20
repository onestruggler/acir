{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D299 (W : Ws) where

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
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ X1 ∷ CK12 ∷ X1 ∷ []) (X1 ∷ CK12 ∷ X1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (wn 899 W)
  q8 : Eqn
  q8 = eqn (CK10⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CZ))
  q9 : Eqn
  q9 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q10 : Eqn
  q10 = eqn (CK10 ∷ CZ23 ∷ []) (CZ23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CZ))
  q11 : Eqn
  q11 = eqn (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS12 ∷ []) (CS12 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (wn 900 W)
  q12 : Eqn
  q12 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q13 : Eqn
  q13 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q14 : Eqn
  q14 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = eqn (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (wn 901 W)
  q16 : Eqn
  q16 = eqn (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (X1 ∷ CK12⁻ ∷ X1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) (wn 902 W)

-- groups [CK10 CS01 CS01 CKd10] [X1 CK13 X1 CZ23 CS12 CS13 CX23 CSd13 CX23 X1 CKd13 X1]: 81 steps
lem-groups-CK10-CS01-CS01-CKd10-vs-X1-CK13-X1-CZ23-CS12-CS13-CX23-CSd13-CX23-X1-CKd13-X1 : ⟪ (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-groups-CK10-CS01-CS01-CKd10-vs-X1-CK13-X1-CZ23-CS12-CS13-CX23-CSd13-CX23-X1-CKd13-X1 = derive (CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK10⁻ ∷ [])
  (rw 7 q1 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 4 q2 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CK13 ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q4 ∷
   rw 7 q3 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q4 ∷
   rw 10 q3 ∷
   rw 9 q12 ∷
   rw 8 q13 ∷
   rw 7 q13 ∷
   rw 6 q14 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 8 q15 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q4 ∷
   rw 12 q3 ∷
   rw 11 q12 ∷
   rw 10 q13 ∷
   rw 9 q13 ∷
   rw 8 q14 ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 14 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 13 q2 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 10 q16 ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (CK13⁻ ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q4 ∷
   rw 16 q3 ∷ []) Eq.refl
