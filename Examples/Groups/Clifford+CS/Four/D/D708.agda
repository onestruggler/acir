{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D708 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D681 W using (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D698 W using (lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1682 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q7 : Eqn
  q7 = eqn (X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) (wn 1490 W)
  q8 : Eqn
  q8 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)

-- pass [X3 CS30 X3] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 49 steps
lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 4 q1 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q8 ∷
   rw 8 q1 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   rw 5 q6 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q4 ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q2 ∷
   rw 6 q6 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q4 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1681 W)
  q10 : Eqn
  q10 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ []) (S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1667 W)
  q12 : Eqn
  q12 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q13 : Eqn
  q13 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q14 : Eqn
  q14 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ []) (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1668 W)

-- pass [X3 CSd30 X3] [X1 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X1]: 53 steps
lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 5 q1 ∷
   rw 4 q10 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 1 q3 ∷
   rw 2 q11 ∷
   rw⁻ 1 q10 ∷
   rw 2 q6 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q6 ∷
   rw 5 q4 ∷
   rw 2 q12 ∷
   rw 10 q1 ∷
   rw 9 q13 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 6 q3 ∷
   rw 7 q14 ∷
   rw⁻ 6 q13 ∷
   rw 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q4 ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw⁻ 7 q2 ∷
   rw 8 q6 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CK13⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (wn 2082 W)
  q16 : Eqn
  q16 = eqn (X1 ∷ CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q17 : Eqn
  q17 = eqn (X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK13⁻ ∷ []) (wn 2083 W)

-- pass [CKd13] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ []) ⟫ʷ
lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ [])
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 5 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-CCZ123

-- pass [CCZ123] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 1 steps
lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (CK13 ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (wn 2084 W)
  q20 : Eqn
  q20 = eqn (X1 ∷ CK13 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q21 : Eqn
  q21 = eqn (X1 ∷ CK13 ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK13 ∷ []) (wn 2085 W)

-- pass [CK13] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CK13 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CK13 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ [])
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 5 q21 ∷ []) Eq.refl
