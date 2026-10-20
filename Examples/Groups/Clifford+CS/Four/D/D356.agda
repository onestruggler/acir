{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D356 (W : Ws) where

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
  q1 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q2 : Eqn
  q2 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q3 : Eqn
  q3 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q4 : Eqn
  q4 = eqn (S0 ∷ CK23 ∷ []) (CK23 ∷ S0 ∷ []) (low₁-comm (S) ((CK₀₁ ↑)))
  q5 : Eqn
  q5 = eqn (CK01 ∷ X2 ∷ []) (X2 ∷ CK01 ∷ []) (low-comm (CK₀₁) (X))
  q6 : Eqn
  q6 = eqn (CK01 ∷ CK23 ∷ []) (CK23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CK₀₁))
  q7 : Eqn
  q7 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q10 : Eqn
  q10 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q11 : Eqn
  q11 = eqn (CX21 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ X2 ∷ CX21 ∷ []) (wn 683 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q14 : Eqn
  q14 = eqn (CS12 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ X2 ∷ CS12 ∷ []) (wn 685 W)
  q15 : Eqn
  q15 = eqn (S2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ X2 ∷ S2 ∷ []) (wn 971 W)
  q16 : Eqn
  q16 = eqn (CK21 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ X2 ∷ CK21 ∷ []) (wn 684 W)

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01] [X2 CK23 X2]: 208 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-CK23-X2 : ⟪ (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-CK23-X2 = derive (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (rw 73 q1 ∷
   rw 74 q2 ∷
   rw 75 q1 ∷
   rw 72 q1 ∷
   rw 73 q2 ∷
   rw 74 q1 ∷
   rw 71 q1 ∷
   rw 72 q2 ∷
   rw 73 q1 ∷
   rw 70 q1 ∷
   rw 71 q2 ∷
   rw 72 q1 ∷
   rw 69 q1 ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   rw 68 q1 ∷
   rw 69 q2 ∷
   rw 70 q1 ∷
   rw 67 q3 ∷
   rw 68 q4 ∷
   rw 69 q3 ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw 68 q5 ∷
   rw 65 q1 ∷
   rw 66 q2 ∷
   rw 67 q1 ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   rw 63 q1 ∷
   rw 64 q2 ∷
   rw 65 q1 ∷
   rw 62 q3 ∷
   rw 63 q4 ∷
   rw 64 q3 ∷
   rw 61 q5 ∷
   rw 62 q6 ∷
   rw 63 q5 ∷
   rw 60 q3 ∷
   rw 61 q4 ∷
   rw 62 q3 ∷
   rw 59 q5 ∷
   rw 60 q6 ∷
   rw 61 q5 ∷
   rw 62 q7 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 60 q9 ∷
   rw⁻ 59 q8 ∷
   rw 58 q10 ∷
   rw 59 q11 ∷
   rw 58 q8 ∷
   rw 59 q9 ∷
   rw 60 q8 ∷
   rw 61 q12 ∷
   rw 62 q13 ∷
   rw 57 q3 ∷
   rw 58 q4 ∷
   rw 59 q3 ∷
   rw 56 q5 ∷
   rw 57 q6 ∷
   rw 58 q5 ∷
   rw 55 q3 ∷
   rw 56 q4 ∷
   rw 57 q3 ∷
   rw 54 q3 ∷
   rw 55 q4 ∷
   rw 56 q3 ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   rw 51 q5 ∷
   rw 52 q6 ∷
   rw 53 q5 ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   rw 48 q3 ∷
   rw 49 q4 ∷
   rw 50 q3 ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   rw 43 q1 ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   rw 40 q1 ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 39 q1 ∷
   rw 40 q2 ∷
   rw 41 q1 ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q5 ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q3 ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   rw 33 q2 ∷
   rw 34 q1 ∷
   rw 31 q1 ∷
   rw 32 q2 ∷
   rw 33 q1 ∷
   rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   rw 25 q2 ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 19 q7 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 16 q8 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 15 q8 ∷
   rw 16 q9 ∷
   rw 17 q8 ∷
   rw 18 q12 ∷
   rw 19 q13 ∷
   rw 14 q14 ∷
   rw 13 q14 ∷
   rw 12 q14 ∷
   rw 11 q14 ∷
   rw 10 q14 ∷
   rw 9 q14 ∷
   rw 8 q15 ∷
   rw 7 q16 ∷
   rw 6 q14 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q16 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 972 W)

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01] [X2 CK21 X2]: 1 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-CK21-X2 : ⟪ (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-CK21-X2 = derive (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q17 ∷ []) Eq.refl
