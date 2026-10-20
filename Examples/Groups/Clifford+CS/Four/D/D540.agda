{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D540 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D013 W using (lem-pass-CCZ023-vs-CS23 ; lem-pass-CCZ023-vs-CZ23 ; lem-pass-CS23-vs-CS01 ; lem-pass-S0-vs-CS01 ; lem-pass-S0-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ023-vs-CS01)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q10 : Eqn
  q10 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q11 : Eqn
  q11 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q13 : Eqn
  q13 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q14 : Eqn
  q14 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q15 : Eqn
  q15 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q16 : Eqn
  q16 = eqn (S1 ∷ Toff123 ∷ []) (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) (wn 1468 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q22 : Eqn
  q22 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q23 : Eqn
  q23 = eqn (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS01)
  q24 : Eqn
  q24 = eqn (CS23 ∷ CS01 ∷ []) (CS01 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS01)
  q25 : Eqn
  q25 = eqn (S0 ∷ CS01 ∷ []) (CS01 ∷ S0 ∷ []) (lem-pass-S0-vs-CS01)
  q26 : Eqn
  q26 = eqn (CCZ123 ∷ Toff123 ∷ []) (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) (wn 1469 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))
  q28 : Eqn
  q28 = eqn (CS23 ∷ Toff123 ∷ []) (Toff123 ∷ CS23 ∷ []) (wn 1374 W)
  q29 : Eqn
  q29 = eqn (CCZ023 ∷ CS23 ∷ []) (CS23 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS23)
  q30 : Eqn
  q30 = eqn (CCZ023 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ23)
  q31 : Eqn
  q31 = eqn (CS23 ∷ CS23 ∷ CZ23 ∷ []) [] (wn 1470 W)
  q32 : Eqn
  q32 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q33 : Eqn
  q33 = eqn (S0 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd01)

-- pass [S0] [TOFF023 CS01 TOFF023 CSd01]: 401 steps
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (S0 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 = derive (S0 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ S0 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q6 ∷
   rw 7 q12 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q13 ∷
   rw⁻ 4 q5 ∷
   rw 3 q13 ∷
   rw⁻ 2 q3 ∷
   rw 1 q11 ∷
   rw 2 q14 ∷
   re 2 8 (Toff123 ∷ []) ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q17 ∷
   rw 2 q3 ∷
   rw 3 q18 ∷
   rw 4 q5 ∷
   rw 5 q18 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q20 ∷
   rw 1 q14 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q3 ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q22 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q9 ∷
   rw 3 q23 ∷
   rw 2 q24 ∷
   rw 1 q25 ∷
   rw 6 q1 ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q2 ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 11 q12 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q13 ∷
   rw⁻ 8 q5 ∷
   rw 7 q13 ∷
   rw⁻ 6 q3 ∷
   rw 5 q11 ∷
   rw 6 q14 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 5 q26 ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 4 q1 ∷
   rw 5 q17 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q17 ∷
   rw 12 q20 ∷
   rw 5 q14 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   rw 5 q27 ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   rw 7 q3 ∷
   rw 8 q18 ∷
   rw 9 q5 ∷
   rw 10 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 12 q19 ∷
   rw 13 q6 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q22 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q9 ∷
   rw 5 q1 ∷
   re 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 4 q11 ∷
   rw 5 q14 ∷
   re 5 8 (Toff123 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 4 q28 ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 3 q1 ∷
   rw 4 q17 ∷
   rw 5 q3 ∷
   rw 6 q18 ∷
   rw 7 q5 ∷
   rw 8 q18 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   rw 11 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q17 ∷
   rw 11 q20 ∷
   rw 4 q14 ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff023 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 4 q1 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 3 q11 ∷
   rw 4 q14 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw 2 q15 ∷
   rw 3 q16 ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 2 q1 ∷
   rw 3 q17 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q17 ∷
   rw 10 q20 ∷
   rw 3 q14 ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff023 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q3 ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q22 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q9 ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 4 q31 ∷
   rw 6 q1 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 6 q22 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 5 q32 ∷
   rw 4 q9 ∷
   rw 3 q33 ∷ []) Eq.refl
