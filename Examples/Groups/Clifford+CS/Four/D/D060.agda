{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D060 (W : Ws) where

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
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CK31⁻ ∷ []) (CK32⁻ ∷ Sw12 ∷ []) (wn 360 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CK32⁻ ∷ []) (CK31⁻ ∷ Sw12 ∷ []) (wn 362 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q8 : Eqn
  q8 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = eqn (CX32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CX32 ∷ []) (wn 500 W)
  q10 : Eqn
  q10 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q11 : Eqn
  q11 = eqn (S2 ∷ CK31⁻ ∷ []) (CK31⁻ ∷ S2 ∷ []) (wn 501 W)
  q12 : Eqn
  q12 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q13 : Eqn
  q13 = eqn (CS02 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) (wn 503 W)
  q14 : Eqn
  q14 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q15 : Eqn
  q15 = eqn (CK20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ []) (wn 502 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CKd31 X3]: 469 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd31-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 30 q1 ∷
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
   rw 28 q7 ∷
   re 30 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CK31⁻ ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q8 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CK31⁻ ∷ []) ∷
   rw 30 q7 ∷
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
   rw 24 q9 ∷
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
   rw 15 q1 ∷
   re 17 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CK31⁻ ∷ []) ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 16 3 (CK31⁻ ∷ []) ∷
   rw 17 q1 ∷
   rw 14 q10 ∷
   rw 15 q11 ∷
   rw 16 q10 ∷
   rw 13 q7 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 15 3 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CK31⁻ ∷ []) ∷
   rw 18 q3 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 16 5 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q1 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   re 15 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 13 3 (CK31⁻ ∷ []) ∷
   rw 14 q1 ∷
   rw 11 q1 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 12 3 (CK31⁻ ∷ []) ∷
   rw 13 q1 ∷
   rw 10 q1 ∷
   re 12 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 16 3 (CK31⁻ ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 11 3 (CK31⁻ ∷ []) ∷
   rw 12 q1 ∷
   rw 9 q1 ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CK31⁻ ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 10 3 (CK31⁻ ∷ []) ∷
   rw 11 q1 ∷
   rw 8 q1 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 11 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw 10 q1 ∷
   rw 7 q1 ∷
   re 9 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CK31⁻ ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 8 3 (CK31⁻ ∷ []) ∷
   rw 9 q1 ∷
   rw 6 q9 ∷
   rw 9 q2 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 8 q2 ∷
   re 6 3 (CK31⁻ ∷ []) ∷
   rw 7 q14 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   rw 8 q2 ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   rw 7 q2 ∷
   re 5 3 (CK31⁻ ∷ []) ∷
   rw 6 q14 ∷
   rw 9 q2 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q12 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 4 q15 ∷
   rw 3 q14 ∷
   rw 6 q2 ∷
   re 4 3 (CK31⁻ ∷ []) ∷
   rw 5 q14 ∷
   rw 8 q2 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q12 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 5 q2 ∷
   re 3 3 (CK31⁻ ∷ []) ∷
   rw 4 q14 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   rw 4 q12 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q13 ∷
   rw 1 q14 ∷
   rw 4 q2 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 3 q14 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   rw 3 q12 ∷
   re 2 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q12 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 3 q2 ∷
   re 1 3 (CK31⁻ ∷ []) ∷
   rw 2 q14 ∷
   rw 5 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q6 ∷ []) Eq.refl
