{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D514 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D013 W using (lem-pass-CS23-vs-CS01)
open import Examples.Groups.Clifford+CS.Four.D.D014 W using (lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS31-X3-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D015 W using (lem-pass-X3-CK31-X3-vs-CS02 ; lem-pass-X3-CK31-X3-vs-CSd02 ; lem-pass-X3-CK31-X3-vs-TOFF013 ; lem-pass-X3-CS31-X3-vs-CSd02 ; lem-pass-X3-CS31-X3-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D021 W using (lem-pass-CS23-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D022 W using (lem-comm-CCZ013-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D023 W using (lem-pass-X3-CK32-X3-vs-CS01 ; lem-pass-X3-CK32-X3-vs-CSd01 ; lem-pass-X3-CK32-X3-vs-TOFF023)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q11 : Eqn
  q11 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q12 : Eqn
  q12 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q13 : Eqn
  q13 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q14 : Eqn
  q14 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q15 : Eqn
  q15 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q16 : Eqn
  q16 = eqn (X3 ∷ Toff123 ∷ X3 ∷ []) (CX21 ∷ Toff123 ∷ []) (wn 1373 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q22 : Eqn
  q22 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q23 : Eqn
  q23 = eqn (CS23 ∷ CX21 ∷ []) (CX21 ∷ CS23 ∷ []) (wn 1327 W)
  q24 : Eqn
  q24 = eqn (CS23 ∷ Toff123 ∷ []) (Toff123 ∷ CS23 ∷ []) (wn 1374 W)
  q25 : Eqn
  q25 = eqn (CX21 ∷ Toff123 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) (wn 1375 W)
  q26 : Eqn
  q26 = eqn (CS23 ∷ CS01 ∷ []) (CS01 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS01)
  q27 : Eqn
  q27 = eqn (CS23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd01)

-- pass [CS23] [X3 TOFF023 X3 CS01 X3 TOFF023 X3 CSd01]: 398 steps
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 : ⟪ (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 = derive (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ CS23 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q7 ∷
   rw 8 q13 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q14 ∷
   rw⁻ 5 q6 ∷
   rw 4 q14 ∷
   rw⁻ 3 q4 ∷
   rw 2 q12 ∷
   rw 3 q15 ∷
   re 3 8 (Toff123 ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 2 q16 ∷
   rw 1 q17 ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 2 q1 ∷
   rw 3 q18 ∷
   rw 4 q4 ∷
   rw 5 q19 ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q20 ∷
   rw 10 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q18 ∷
   rw 10 q21 ∷
   rw 3 q15 ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff023 ∷ []) ∷
   rw 3 q10 ∷
   rw 2 q1 ∷
   rw 1 q22 ∷
   rw⁻ 0 q4 ∷
   rw 1 q23 ∷
   rw 0 q17 ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q1 ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q7 ∷
   rw 8 q13 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q14 ∷
   rw⁻ 5 q6 ∷
   rw 4 q14 ∷
   rw⁻ 3 q4 ∷
   rw 2 q12 ∷
   rw 3 q15 ∷
   re 3 8 (Toff123 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 2 q24 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q18 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   rw 5 q6 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q20 ∷
   rw 9 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q15 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 2 q1 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q13 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q14 ∷
   rw⁻ 4 q6 ∷
   rw 3 q14 ∷
   rw⁻ 2 q4 ∷
   rw 1 q12 ∷
   rw 2 q15 ∷
   re 2 8 (Toff123 ∷ []) ∷
   rw 0 q22 ∷
   rw 1 q25 ∷
   rw 0 q2 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q18 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   rw 5 q6 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q20 ∷
   rw 9 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q15 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 3 q26 ∷
   rw 8 q1 ∷
   rw⁻ 7 q2 ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   rw 12 q12 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q13 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q14 ∷
   rw⁻ 9 q6 ∷
   rw 8 q14 ∷
   rw⁻ 7 q4 ∷
   rw 6 q12 ∷
   rw 7 q15 ∷
   re 7 8 (Toff123 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 6 q1 ∷
   rw 7 q18 ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q20 ∷
   rw 14 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q18 ∷
   rw 14 q21 ∷
   rw 7 q15 ∷
   re 7 8 (Toff123 ∷ []) ∷
   re 6 3 (Toff023 ∷ []) ∷
   rw 7 q10 ∷
   rw 6 q1 ∷
   rw 5 q22 ∷
   rw⁻ 4 q4 ∷
   rw 5 q23 ∷
   rw 4 q17 ∷
   rw 5 q4 ∷
   rw 6 q10 ∷
   rw 7 q1 ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   rw 12 q12 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q13 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q14 ∷
   rw⁻ 9 q6 ∷
   rw 8 q14 ∷
   rw⁻ 7 q4 ∷
   rw 6 q12 ∷
   rw 7 q15 ∷
   re 7 8 (Toff123 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 6 q24 ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 5 q1 ∷
   rw 6 q18 ∷
   rw 7 q4 ∷
   rw 8 q19 ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q20 ∷
   rw 13 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q18 ∷
   rw 13 q21 ∷
   rw 6 q15 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q10 ∷
   rw 6 q1 ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 11 q13 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q14 ∷
   rw⁻ 8 q6 ∷
   rw 7 q14 ∷
   rw⁻ 6 q4 ∷
   rw 5 q12 ∷
   rw 6 q15 ∷
   re 6 8 (Toff123 ∷ []) ∷
   rw 4 q22 ∷
   rw 5 q25 ∷
   rw 4 q2 ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 5 q1 ∷
   rw 6 q18 ∷
   rw 7 q4 ∷
   rw 8 q19 ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q20 ∷
   rw 13 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q18 ∷
   rw 13 q21 ∷
   rw 6 q15 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q10 ∷
   rw 7 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ123)

-- pass [CCZ013] [CCZ123]: 1 steps
lem-pass-CCZ013-vs-CCZ123 : ⟪ (CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CCZ123 = derive (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-TOFF023)
  q30 : Eqn
  q30 = eqn (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01)
  q31 : Eqn
  q31 = eqn (X3 ∷ CK32 ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CSd01)

-- pass [X3 CK32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 0 q29 ∷
   rw 1 q30 ∷
   rw 2 q29 ∷
   rw 3 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q33 : Eqn
  q33 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q34 : Eqn
  q34 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q35 : Eqn
  q35 = eqn (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q36 : Eqn
  q36 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q37 : Eqn
  q37 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q38 : Eqn
  q38 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)

-- pass [X3 CK31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 3 q33 ∷
   rw⁻ 4 q35 ∷
   rw 10 q36 ∷
   rw 9 q37 ∷
   rw 8 q38 ∷
   rw 7 q37 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF013)
  q40 : Eqn
  q40 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS02)
  q41 : Eqn
  q41 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CSd02)

-- pass [X3 CS31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q39 ∷
   rw 3 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF013)
  q43 : Eqn
  q43 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02)
  q44 : Eqn
  q44 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CSd02)

-- pass [X3 CK31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q42 ∷
   rw 3 q44 ∷ []) Eq.refl
