{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D378 (W : Ws) where

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
  q1 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 583 W)
  q2 : Eqn
  q2 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q3 : Eqn
  q3 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q4 : Eqn
  q4 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q5 : Eqn
  q5 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q9 : Eqn
  q9 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q10 : Eqn
  q10 = eqn (CX12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CX12 ∷ []) (wn 1034 W)
  q11 : Eqn
  q11 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q12 : Eqn
  q12 = eqn (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ []) (wn 211 W)
  q13 : Eqn
  q13 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q14 : Eqn
  q14 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = eqn (CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CK10 ∷ []) (wn 1035 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (CS01 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01 ∷ []) (wn 1036 W)
  q19 : Eqn
  q19 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 586 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd13 X3]: 397 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd13-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q1 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q7 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q7 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 29 q2 ∷
   rw 26 q8 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q4 ∷
   rw 30 q9 ∷
   rw 29 q6 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q7 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 28 q8 ∷
   rw 25 q2 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q7 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q7 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 27 q2 ∷
   rw 24 q8 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q4 ∷
   rw 28 q9 ∷
   rw 27 q6 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q7 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q7 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 26 q8 ∷
   rw 23 q8 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q4 ∷
   rw 27 q9 ∷
   rw 26 q6 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 25 q8 ∷
   rw 22 q10 ∷
   rw 21 q8 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 26 q4 ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q7 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q7 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 23 q8 ∷
   rw 20 q8 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 25 q4 ∷
   rw 24 q9 ∷
   rw 23 q6 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q7 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 22 q8 ∷
   rw 19 q8 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q4 ∷
   rw 23 q9 ∷
   rw 22 q6 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 21 q8 ∷
   rw 18 q8 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q4 ∷
   rw 22 q9 ∷
   rw 21 q6 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q7 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw 20 q8 ∷
   rw 17 q8 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q4 ∷
   rw 21 q9 ∷
   rw 20 q6 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q7 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 19 q8 ∷
   rw 16 q8 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q4 ∷
   rw 20 q9 ∷
   rw 19 q6 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 18 q8 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q11 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 16 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   rw 17 q6 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 16 q2 ∷
   rw 13 q8 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw 18 q4 ∷
   rw 17 q9 ∷
   rw 16 q6 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 15 q8 ∷
   rw 12 q8 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw 17 q4 ∷
   rw 16 q9 ∷
   rw 15 q6 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q8 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw 16 q4 ∷
   rw 15 q9 ∷
   rw 14 q6 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 13 q8 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q11 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   re 11 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   re 12 5 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   rw 7 q2 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   re 10 5 (CK30 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q10 ∷
   rw 9 q3 ∷
   rw 8 q13 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   rw 8 q3 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q16 ∷
   rw⁻ 8 q14 ∷
   rw 9 q7 ∷
   rw 8 q3 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   rw 4 q16 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 6 q16 ∷
   rw⁻ 7 q14 ∷
   rw 8 q7 ∷
   rw 7 q3 ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 4 q13 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 3 q16 ∷
   rw 6 q3 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw 5 q16 ∷
   rw⁻ 6 q17 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q13 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 2 q16 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 4 q16 ∷
   rw⁻ 5 q14 ∷
   rw 6 q7 ∷
   rw 5 q3 ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q13 ∷
   rw 1 q17 ∷
   rw 2 q18 ∷
   rw 1 q16 ∷
   rw 4 q3 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 3 q16 ∷
   rw⁻ 4 q17 ∷
   rw 5 q7 ∷
   rw 4 q3 ∷
   rw 3 q13 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q13 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   rw 0 q16 ∷
   rw 3 q3 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw 4 q7 ∷
   rw 3 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 1017 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CSd12 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 451 W)

-- pass [X3 CKd31 X3] [TOFF213]: 1 steps
lem-pass-X3-CKd31-X3-vs-TOFF213 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF213 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (CCZ123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) (wn 1037 W)

-- pass [CCZ123] [X3 CSd23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CSd23-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CSd23-X3 = derive (CCZ123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) (wn 1038 W)

-- pass [CCZ123] [X3 CKd32 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CKd32-X3 : ⟪ (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd32-X3 = derive (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) (wn 1039 W)

-- pass [CCZ123] [X3 CS23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-X3 = derive (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ []) (wn 266 W)

-- pass [CCZ123] [CS23]: 1 steps
lem-pass-CCZ123-vs-CS23 : ⟪ (CCZ123 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CS23 = derive (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ [])
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CZ12 ∷ CS23 ∷ []) (CS23 ∷ CZ12 ∷ []) (wn 1040 W)

-- pass [CZ12] [CS23]: 1 steps
lem-pass-CZ12-vs-CS23 : ⟪ (CZ12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CS23 = derive (CZ12 ∷ CS23 ∷ []) (CS23 ∷ CZ12 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ []) (wn 269 W)

-- pass [CCZ123] [CSd23]: 1 steps
lem-pass-CCZ123-vs-CSd23 : ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CSd23 = derive (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q29 : Eqn
  q29 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q30 : Eqn
  q30 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wn 100 W)
  q31 : Eqn
  q31 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q32 : Eqn
  q32 = eqn (CS13 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS13 ∷ []) (wn 433 W)
  q33 : Eqn
  q33 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q36 : Eqn
  q36 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q37 : Eqn
  q37 = eqn (CX31 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CX31 ∷ []) (wn 592 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q40 : Eqn
  q40 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q41 : Eqn
  q41 = eqn (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CCZ012 ∷ []) (wn 104 W)

-- comm CCZ013 CSd23: 97 steps
lem-comm-CCZ013-CSd23 : ⟪ (CCZ013 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd23 = derive (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ [])
  (rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q3 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q28 ∷
   rw 4 q3 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q28 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q28 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q28 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q29 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q30 ∷
   rw⁻ 0 q17 ∷
   rw 3 q3 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 2 q31 ∷
   rw 5 q3 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q3 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q32 ∷
   rw 5 q33 ∷
   rw⁻ 4 q34 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q35 ∷
   rw 4 q36 ∷
   rw⁻ 3 q35 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 4 q37 ∷
   rw 3 q34 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q38 ∷
   rw 6 q35 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q39 ∷
   rw 2 q40 ∷
   rw 3 q33 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q35 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q37 ∷
   rw 1 q34 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q38 ∷
   rw 4 q35 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q39 ∷
   rw 0 q9 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q17 ∷
   rw 2 q41 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q28 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q28 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 3 q28 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q28 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 2 q29 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (CZ12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ12 ∷ []) (wn 1041 W)

-- pass [CZ12] [CSd23]: 1 steps
lem-pass-CZ12-vs-CSd23 : ⟪ (CZ12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CSd23 = derive (CZ12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ12 ∷ [])
  (rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (CZ01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ01 ∷ []) (low-comm (CZ) ((CS • CS • CS)))

-- pass [CZ01] [CSd23]: 1 steps
lem-pass-CZ01-vs-CSd23 : ⟪ (CZ01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CZ01 ∷ []) ⟫ʷ
lem-pass-CZ01-vs-CSd23 = derive (CZ01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ01 ∷ [])
  (rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (CCZ123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CCZ123 ∷ []) (wn 1042 W)

-- pass [CCZ123] [X3 CK32 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CK32-X3 : ⟪ (CCZ123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CK32-X3 = derive (CCZ123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 448 W)

-- pass [X3 CK31 X3] [TOFF213]: 1 steps
lem-pass-X3-CK31-X3-vs-TOFF213 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF213 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q45 ∷ []) Eq.refl
