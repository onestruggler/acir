{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D280 (W : Ws) where

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
  q1 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 360 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = wE 362 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q8 : Eqn
  q8 = eqn (S0 ∷ CK31⁻ ∷ []) (CK31⁻ ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)))
  q9 : Eqn
  q9 = eqn (CK02 ∷ X3 ∷ []) (X3 ∷ CK02 ∷ []) (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (CK01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK01 ∷ []) (low-comm (CK₀₁) ((S ↑ • CK₁₀)))
  q11 : Eqn
  q11 = wE 173 W
  q12 : Eqn
  q12 = wE 789 W
  q13 : Eqn
  q13 = wE 175 W
  q14 : Eqn
  q14 = wE 791 W
  q15 : Eqn
  q15 = wE 865 W
  q16 : Eqn
  q16 = wE 790 W

-- pass [CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02] [X3 CKd31 X3]: 804 steps
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd31-X3 : ⟪ (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CKd31-X3 = derive (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 73 q1 ∷
   re 75 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   re 79 3 (CK31⁻ ∷ []) ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 76 q5 ∷
   re 76 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q6 ∷
   re 74 3 (CK31⁻ ∷ []) ∷
   rw 75 q1 ∷
   rw 72 q1 ∷
   re 74 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   re 78 3 (CK31⁻ ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   re 75 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q6 ∷
   re 73 3 (CK31⁻ ∷ []) ∷
   rw 74 q1 ∷
   rw 71 q1 ∷
   re 73 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   re 77 3 (CK31⁻ ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   rw 74 q5 ∷
   re 74 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q6 ∷
   re 72 3 (CK31⁻ ∷ []) ∷
   rw 73 q1 ∷
   rw 70 q1 ∷
   re 72 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   re 76 3 (CK31⁻ ∷ []) ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   rw 73 q5 ∷
   re 73 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q6 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q6 ∷
   re 71 3 (CK31⁻ ∷ []) ∷
   rw 72 q1 ∷
   rw 69 q1 ∷
   re 71 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q2 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q2 ∷
   re 75 3 (CK31⁻ ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   rw 72 q5 ∷
   re 72 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q6 ∷
   re 70 3 (CK31⁻ ∷ []) ∷
   rw 71 q1 ∷
   rw 68 q1 ∷
   re 70 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   re 74 3 (CK31⁻ ∷ []) ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   rw 71 q5 ∷
   re 71 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q6 ∷
   re 69 3 (CK31⁻ ∷ []) ∷
   rw 70 q1 ∷
   rw 67 q7 ∷
   rw 68 q8 ∷
   rw 69 q7 ∷
   rw 66 q9 ∷
   re 68 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 68 3 (CK03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   re 72 3 (CK31⁻ ∷ []) ∷
   rw 71 q3 ∷
   rw 70 q10 ∷
   rw 69 q5 ∷
   re 69 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   re 69 5 (CK03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 71 q6 ∷
   re 67 3 (CK31⁻ ∷ []) ∷
   rw 68 q9 ∷
   rw 65 q1 ∷
   re 67 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   re 71 3 (CK31⁻ ∷ []) ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   rw 68 q5 ∷
   re 68 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q6 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q6 ∷
   re 66 3 (CK31⁻ ∷ []) ∷
   rw 67 q1 ∷
   rw 64 q1 ∷
   re 66 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q2 ∷
   re 70 3 (CK31⁻ ∷ []) ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   re 67 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q6 ∷
   re 65 3 (CK31⁻ ∷ []) ∷
   rw 66 q1 ∷
   rw 63 q1 ∷
   re 65 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   re 69 3 (CK31⁻ ∷ []) ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   rw 66 q5 ∷
   re 66 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q6 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q6 ∷
   re 64 3 (CK31⁻ ∷ []) ∷
   rw 65 q1 ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q7 ∷
   rw 61 q9 ∷
   re 63 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   re 63 3 (CK03 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   re 67 3 (CK31⁻ ∷ []) ∷
   rw 66 q3 ∷
   rw 65 q10 ∷
   rw 64 q5 ∷
   re 64 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q6 ∷
   re 64 5 (CK03 ∷ []) ∷
   re 64 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   re 62 3 (CK31⁻ ∷ []) ∷
   rw 63 q9 ∷
   rw 60 q7 ∷
   rw 61 q8 ∷
   rw 62 q7 ∷
   rw 59 q9 ∷
   re 61 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 61 3 (CK03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CK31⁻ ∷ []) ∷
   rw 64 q3 ∷
   rw 63 q10 ∷
   rw 62 q5 ∷
   re 62 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   re 62 5 (CK03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 64 q6 ∷
   re 60 3 (CK31⁻ ∷ []) ∷
   rw 61 q9 ∷
   rw 62 q2 ∷
   rw 61 q11 ∷
   re 60 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q6 ∷
   rw 59 q11 ∷
   re 58 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 60 q6 ∷
   rw 59 q12 ∷
   rw 58 q13 ∷
   rw 61 q2 ∷
   re 59 3 (CK31⁻ ∷ []) ∷
   rw 60 q13 ∷
   rw 63 q2 ∷
   re 61 3 (CX30 ∷ []) ∷
   rw 62 q6 ∷
   rw 57 q7 ∷
   rw 58 q8 ∷
   rw 59 q7 ∷
   rw 56 q9 ∷
   re 58 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 58 3 (CK03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CK31⁻ ∷ []) ∷
   rw 61 q3 ∷
   rw 60 q10 ∷
   rw 59 q5 ∷
   re 59 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 58 q6 ∷
   re 59 5 (CK03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   re 57 3 (CK31⁻ ∷ []) ∷
   rw 58 q9 ∷
   rw 55 q7 ∷
   rw 56 q8 ∷
   rw 57 q7 ∷
   rw 54 q7 ∷
   rw 55 q8 ∷
   rw 56 q7 ∷
   rw 53 q7 ∷
   rw 54 q8 ∷
   rw 55 q7 ∷
   rw 52 q7 ∷
   rw 53 q8 ∷
   rw 54 q7 ∷
   rw 51 q9 ∷
   re 53 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 53 3 (CK03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CK31⁻ ∷ []) ∷
   rw 56 q3 ∷
   rw 55 q10 ∷
   rw 54 q5 ∷
   re 54 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   re 54 5 (CK03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 56 q6 ∷
   re 52 3 (CK31⁻ ∷ []) ∷
   rw 53 q9 ∷
   rw 50 q7 ∷
   rw 51 q8 ∷
   rw 52 q7 ∷
   rw 49 q7 ∷
   rw 50 q8 ∷
   rw 51 q7 ∷
   rw 48 q7 ∷
   rw 49 q8 ∷
   rw 50 q7 ∷
   rw 47 q1 ∷
   re 49 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 53 3 (CK31⁻ ∷ []) ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   re 50 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   re 48 3 (CK31⁻ ∷ []) ∷
   rw 49 q1 ∷
   rw 46 q1 ∷
   re 48 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 52 3 (CK31⁻ ∷ []) ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   re 49 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q6 ∷
   re 47 3 (CK31⁻ ∷ []) ∷
   rw 48 q1 ∷
   rw 45 q1 ∷
   re 47 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 51 3 (CK31⁻ ∷ []) ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   re 48 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   re 46 3 (CK31⁻ ∷ []) ∷
   rw 47 q1 ∷
   rw 44 q1 ∷
   re 46 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 50 3 (CK31⁻ ∷ []) ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   rw 47 q5 ∷
   re 47 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   re 45 3 (CK31⁻ ∷ []) ∷
   rw 46 q1 ∷
   rw 43 q1 ∷
   re 45 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 49 3 (CK31⁻ ∷ []) ∷
   rw 48 q3 ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   re 46 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   re 44 3 (CK31⁻ ∷ []) ∷
   rw 45 q1 ∷
   rw 42 q1 ∷
   re 44 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 48 3 (CK31⁻ ∷ []) ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   rw 45 q5 ∷
   re 45 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   re 43 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CK31⁻ ∷ []) ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   re 44 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   re 42 3 (CK31⁻ ∷ []) ∷
   rw 43 q1 ∷
   rw 40 q1 ∷
   re 42 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 46 3 (CK31⁻ ∷ []) ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   re 43 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 41 3 (CK31⁻ ∷ []) ∷
   rw 42 q1 ∷
   rw 39 q1 ∷
   re 41 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CK31⁻ ∷ []) ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 40 3 (CK31⁻ ∷ []) ∷
   rw 41 q1 ∷
   rw 38 q7 ∷
   rw 39 q8 ∷
   rw 40 q7 ∷
   rw 37 q9 ∷
   re 39 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 39 3 (CK03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 43 3 (CK31⁻ ∷ []) ∷
   rw 42 q3 ∷
   rw 41 q10 ∷
   rw 40 q5 ∷
   re 40 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   re 40 5 (CK03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 38 3 (CK31⁻ ∷ []) ∷
   rw 39 q9 ∷
   rw 36 q7 ∷
   rw 37 q8 ∷
   rw 38 q7 ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   rw 34 q7 ∷
   rw 35 q8 ∷
   rw 36 q7 ∷
   rw 33 q1 ∷
   re 35 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 39 3 (CK31⁻ ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   rw 36 q5 ∷
   re 36 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   re 34 3 (CK31⁻ ∷ []) ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   re 34 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 38 3 (CK31⁻ ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   re 35 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   re 33 3 (CK31⁻ ∷ []) ∷
   rw 34 q1 ∷
   rw 31 q1 ∷
   re 33 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 37 3 (CK31⁻ ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   re 34 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 32 3 (CK31⁻ ∷ []) ∷
   rw 33 q1 ∷
   rw 30 q1 ∷
   re 32 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CK31⁻ ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 31 3 (CK31⁻ ∷ []) ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   re 31 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CK31⁻ ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 30 3 (CK31⁻ ∷ []) ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CK31⁻ ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CK31⁻ ∷ []) ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CK31⁻ ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 28 3 (CK31⁻ ∷ []) ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   re 28 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CK31⁻ ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CK31⁻ ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   re 26 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CK31⁻ ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   re 25 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CK31⁻ ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CK31⁻ ∷ []) ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   re 23 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CK31⁻ ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 21 3 (CK31⁻ ∷ []) ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CK31⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CK31⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CK31⁻ ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CK31⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 18 q11 ∷
   re 17 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw 16 q11 ∷
   re 15 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   rw 18 q2 ∷
   re 16 3 (CK31⁻ ∷ []) ∷
   rw 17 q13 ∷
   rw 20 q2 ∷
   re 18 3 (CX30 ∷ []) ∷
   rw 19 q6 ∷
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
