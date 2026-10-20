{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D193 (W : Ws) where

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
  q1 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q4 : Eqn
  q4 = eqn (CK01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK01 ∷ []) (low-comm (CK₀₁) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q8 : Eqn
  q8 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q10 : Eqn
  q10 = eqn (CX20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CX20 ∷ []) (wn 789 W)
  q11 : Eqn
  q11 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q12 : Eqn
  q12 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q13 : Eqn
  q13 = eqn (S0 ∷ CK31⁻ ∷ []) (CK31⁻ ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)))
  q14 : Eqn
  q14 = eqn (CK32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CK32 ∷ []) (wn 790 W)
  q15 : Eqn
  q15 = eqn (CS23 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ []) (wn 791 W)

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 CKd31 X3]: 351 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd31-X3 : ⟪ (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd31-X3 = derive (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ [])
  (rw 28 q1 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CK31⁻ ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CK03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CK31⁻ ∷ []) ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CK31⁻ ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 30 5 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 28 3 (CK31⁻ ∷ []) ∷
   rw 29 q1 ∷
   rw 26 q7 ∷
   re 28 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CK31⁻ ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 28 q7 ∷
   rw 25 q1 ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CK31⁻ ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CK03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 27 q1 ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CK31⁻ ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 26 q7 ∷
   rw 23 q7 ∷
   re 25 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CK31⁻ ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 25 q7 ∷
   rw 26 q2 ∷
   rw 25 q9 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 23 q9 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   rw 25 q2 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 24 q11 ∷
   rw 27 q2 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q6 ∷
   rw 21 q7 ∷
   re 23 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q8 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 23 q7 ∷
   rw 20 q7 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q8 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 21 3 (CK31⁻ ∷ []) ∷
   rw 22 q7 ∷
   rw 19 q7 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q8 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw 21 q7 ∷
   rw 18 q7 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q8 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 20 q7 ∷
   rw 17 q7 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q8 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 19 q7 ∷
   rw 16 q7 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q8 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw 18 q7 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CK03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 17 5 (CK03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 15 3 (CK31⁻ ∷ []) ∷
   rw 16 q1 ∷
   rw 13 q7 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 18 q3 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q7 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q8 ∷
   rw 15 q5 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 13 3 (CK31⁻ ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q7 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   rw 14 q5 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 12 3 (CK31⁻ ∷ []) ∷
   rw 13 q7 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q12 ∷
   rw 9 q1 ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CK03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CK31⁻ ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 12 5 (CK03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 10 3 (CK31⁻ ∷ []) ∷
   rw 11 q1 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   rw 7 q1 ∷
   re 9 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CK31⁻ ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 10 5 (CK03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 8 3 (CK31⁻ ∷ []) ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q10 ∷
   rw 6 q11 ∷
   rw 9 q2 ∷
   re 7 3 (CK31⁻ ∷ []) ∷
   rw 8 q11 ∷
   rw 11 q2 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q6 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q17 : Eqn
  q17 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q18 : Eqn
  q18 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wn 100 W)
  q19 : Eqn
  q19 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q21 : Eqn
  q21 = eqn (CS13 ∷ CZ12 ∷ []) (CZ12 ∷ CS13 ∷ []) (wn 190 W)
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) (wn 107 W)
  q23 : Eqn
  q23 = eqn (CX10 ∷ CZ23 ∷ []) (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ))
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) (wn 108 W)
  q25 : Eqn
  q25 = eqn (CS01⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS01⁻ ∷ []) (wn 109 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ CZ12 ∷ []) (CZ12 ∷ CS01 ∷ []) (wn 110 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CCZ012 ∷ []) (wn 104 W)

-- comm CCZ013 CZ12: 85 steps
lem-comm-CCZ013-CZ12 : ⟪ (CCZ013 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CZ12 = derive (CCZ013 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ013 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q16 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q16 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q17 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q18 ∷
   rw⁻ 0 q19 ∷
   rw 3 q2 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 2 q20 ∷
   rw 5 q2 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q6 ∷
   rw 4 q21 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 7 3 (CZ13 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q23 ∷
   rw 4 q24 ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   re 4 5 (CX30 ∷ []) ∷
   rw 2 q25 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 5 3 (CZ13 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q23 ∷
   rw 2 q24 ∷
   re 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 1 q6 ∷
   re 2 5 (CX30 ∷ []) ∷
   rw 0 q26 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q20 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q19 ∷
   rw 2 q27 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q17 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ []) (wn 792 W)

-- pass [CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12] [X3 TOFF123 X3]: 1 steps
lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 : ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 = derive (CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (wn 793 W)

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12] [X3 TOFF123 X3]: 1 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 : ⟪ (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 = derive (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl
