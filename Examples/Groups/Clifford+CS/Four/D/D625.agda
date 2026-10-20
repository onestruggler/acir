{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D625 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CS13-vs-CS03 ; lem-pass-CS13-vs-CSd03 ; lem-pass-CS13-vs-S0 ; lem-pass-CS13-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D016 W using (lem-pass-S1-vs-CS13 ; lem-pass-Sd1-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D021 W using (lem-pass-CS23-vs-CS02 ; lem-pass-CS23-vs-CS03 ; lem-pass-CS23-vs-CSd02 ; lem-pass-CS23-vs-CSd03 ; lem-pass-CS23-vs-S0 ; lem-pass-CS23-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D023 W using (lem-pass-CS03-vs-CSd23 ; lem-pass-CS13-vs-CS01 ; lem-pass-CS13-vs-CSd01 ; lem-pass-CS23-vs-S2 ; lem-pass-CS23-vs-S3 ; lem-pass-CS23-vs-Sd2 ; lem-pass-CS23-vs-Sd3 ; lem-pass-CS23-vs-iI ; lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 ; lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-CS13-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D597 W using (lem-pass-CS03-vs-TOFF201 ; lem-pass-CS13-vs-TOFF023 ; lem-pass-CS23-vs-TOFF012 ; lem-pass-CS23-vs-TOFF013 ; lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 ; lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0)

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
  q22 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q23 : Eqn
  q23 = eqn (CX10 ∷ CS23 ∷ []) (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS))
  q24 : Eqn
  q24 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q25 : Eqn
  q25 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF023)
  q26 : Eqn
  q26 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q27 : Eqn
  q27 = eqn (CX21 ∷ Toff123 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) (wn 1375 W)
  q28 : Eqn
  q28 = eqn (S1 ∷ CS13 ∷ []) (CS13 ∷ S1 ∷ []) lem-pass-S1-vs-CS13
  q29 : Eqn
  q29 = eqn (CS13 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd01)
  q30 : Eqn
  q30 = eqn (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ []) lem-pass-Sd1-vs-CS13
  q31 : Eqn
  q31 = eqn (CS13 ∷ CS01 ∷ []) (CS01 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS01)

-- pass [CS13] [X3 TOFF023 X3 S1 CSd01 X3 TOFF023 X3 Sd1 CS01]: 272 steps
lem-pass-CS13-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 : ⟪ (CS13 ∷ X3 ∷ Toff023 ∷ X3 ∷ S1 ∷ CS01⁻ ∷ X3 ∷ Toff023 ∷ X3 ∷ S1⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ S1 ∷ CS01⁻ ∷ X3 ∷ Toff023 ∷ X3 ∷ S1⁻ ∷ CS01 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 = derive (CS13 ∷ X3 ∷ Toff023 ∷ X3 ∷ S1 ∷ CS01⁻ ∷ X3 ∷ Toff023 ∷ X3 ∷ S1⁻ ∷ CS01 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ S1 ∷ CS01⁻ ∷ X3 ∷ Toff023 ∷ X3 ∷ S1⁻ ∷ CS01 ∷ CS13 ∷ [])
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
   re 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ∷
   rw 0 q22 ∷
   rw⁻ 1 q23 ∷
   rw 2 q24 ∷
   re 0 3 (CX20 ∷ []) ∷
   rw 1 q25 ∷
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
   rw 0 q26 ∷
   rw 1 q27 ∷
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
   rw⁻ 3 q28 ∷
   rw 4 q29 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q7 ∷
   rw 13 q13 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q14 ∷
   rw⁻ 10 q6 ∷
   rw 9 q14 ∷
   rw⁻ 8 q4 ∷
   rw 7 q12 ∷
   rw 8 q15 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 7 q1 ∷
   rw 8 q18 ∷
   rw 9 q4 ∷
   rw 10 q19 ∷
   rw 11 q6 ∷
   rw 12 q19 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q20 ∷
   rw 15 q7 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q18 ∷
   rw 15 q21 ∷
   rw 8 q15 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   rw 8 q10 ∷
   re 6 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ∷
   rw 5 q22 ∷
   rw⁻ 6 q23 ∷
   rw 7 q24 ∷
   re 5 3 (CX20 ∷ []) ∷
   rw 6 q25 ∷
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
   rw 5 q26 ∷
   rw 6 q27 ∷
   rw 5 q2 ∷
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
   rw 7 q2 ∷
   rw 8 q10 ∷
   rw⁻ 8 q30 ∷
   rw 9 q31 ∷ []) Eq.refl

-- pass [CS13] [X3 TOFF023 X3]: 134 steps
lem-pass-CS13-vs-X3-TOFF023-X3 : ⟪ (CS13 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF023-X3 = derive (CS13 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS13 ∷ [])
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
   re 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ∷
   rw 0 q22 ∷
   rw⁻ 1 q23 ∷
   rw 2 q24 ∷
   re 0 3 (CX20 ∷ []) ∷
   rw 1 q25 ∷
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
   rw 0 q26 ∷
   rw 1 q27 ∷
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
   rw 3 q10 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q33 : Eqn
  q33 = eqn (CK32⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1674 W)
  q34 : Eqn
  q34 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0)
  q35 : Eqn
  q35 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ []) (wn 1675 W)

-- pass [CKd32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CK32⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (CK32⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 7 q35 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS23 ∷ ι ∷ []) (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI)
  q37 : Eqn
  q37 = eqn (CS23 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd0)
  q38 : Eqn
  q38 = eqn (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd3)
  q39 : Eqn
  q39 = eqn (CS23 ∷ CS03 ∷ []) (CS03 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS03)
  q40 : Eqn
  q40 = eqn (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF012)
  q41 : Eqn
  q41 = eqn (CS23 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S0)
  q42 : Eqn
  q42 = eqn (CS23 ∷ S3 ∷ []) (S3 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S3)
  q43 : Eqn
  q43 = eqn (CS23 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd03)

-- pass [CS23] [iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03 TOFF012]: 12 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 : ⟪ (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 = derive (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ CS23 ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 5 q36 ∷
   rw 6 q36 ∷
   rw 7 q36 ∷
   rw 8 q41 ∷
   rw 9 q42 ∷
   rw 10 q43 ∷
   rw 11 q40 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (CS23 ∷ CS03 ∷ []) (CS03 ∷ CS23 ∷ []) lem-pass-CS23-vs-CS03
  q45 : Eqn
  q45 = eqn (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ []) (lem-pass-CS03-vs-TOFF201)
  q46 : Eqn
  q46 = eqn (CS03 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-CSd23)

-- pass [CS03] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 = derive (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ [])
  (rw⁻ 0 q44 ∷
   rw 1 q45 ∷
   rw 2 q46 ∷
   rw 3 q45 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03)
  q48 : Eqn
  q48 = eqn (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ []) (lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03)
  q49 : Eqn
  q49 = eqn (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI-Sd0-Sd3-CS03)

-- pass [CS23 TOFF201 CSd23 TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw 3 q47 ∷
   rw 2 q48 ∷
   rw 1 q47 ∷
   rw 0 q49 ∷ []) Eq.refl

-- pass [CS23] [TOFF012 iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03]: 12 steps
lem-pass-CS23-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 : ⟪ (CS23 ∷ Toff012 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 = derive (CS23 ∷ Toff012 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ []) (Toff012 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ CS23 ∷ [])
  (rw 0 q40 ∷
   rw 1 q36 ∷
   rw 2 q37 ∷
   rw 3 q38 ∷
   rw 4 q39 ∷
   rw 5 q40 ∷
   rw 6 q36 ∷
   rw 7 q36 ∷
   rw 8 q36 ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q51 : Eqn
  q51 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q52 : Eqn
  q52 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q54 : Eqn
  q54 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q55 : Eqn
  q55 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q56 : Eqn
  q56 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q57 : Eqn
  q57 = eqn (X2 ∷ Toff012 ∷ X2 ∷ []) (CX10 ∷ Toff012 ∷ []) (wn 1362 W)
  q58 : Eqn
  q58 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q59 : Eqn
  q59 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF013)
  q60 : Eqn
  q60 = eqn (CX10 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) (wn 1364 W)
  q61 : Eqn
  q61 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q62 : Eqn
  q62 = eqn (CS23 ∷ S2 ∷ []) (S2 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S2)
  q63 : Eqn
  q63 = eqn (CS23 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd02)
  q64 : Eqn
  q64 = eqn (CS23 ∷ S2⁻ ∷ []) (S2⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd2)
  q65 : Eqn
  q65 = eqn (CS23 ∷ CS02 ∷ []) (CS02 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS02)

-- pass [CS23] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 248 steps
lem-pass-CS23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ CS23 ∷ [])
  (rw 4 q50 ∷
   rw 3 q51 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q52 ∷
   rw 5 q50 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q53 ∷
   rw 7 q50 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q53 ∷
   rw 9 q50 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 10 q55 ∷
   rw 9 q54 ∷
   rw 8 q52 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q55 ∷
   rw 6 q53 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q55 ∷
   rw 4 q53 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q55 ∷
   rw 2 q52 ∷
   rw 3 q56 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q51 ∷
   rw 2 q57 ∷
   rw⁻ 1 q58 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q52 ∷
   rw 5 q50 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q53 ∷
   rw 7 q50 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q53 ∷
   rw 9 q50 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 2 q50 ∷
   rw⁻ 3 q52 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q55 ∷
   rw⁻ 5 q53 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q55 ∷
   rw⁻ 7 q53 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q55 ∷
   rw⁻ 9 q52 ∷
   rw⁻ 10 q54 ∷
   rw 3 q56 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q55 ∷
   rw⁻ 0 q23 ∷
   rw 1 q59 ∷
   rw 2 q50 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q52 ∷
   rw 4 q50 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q53 ∷
   rw 6 q50 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q53 ∷
   rw 8 q50 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q52 ∷
   rw⁻ 8 q54 ∷
   rw 9 q55 ∷
   rw 8 q54 ∷
   rw 7 q52 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q55 ∷
   rw 5 q53 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q55 ∷
   rw 3 q53 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q55 ∷
   rw 1 q52 ∷
   rw 2 q56 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q58 ∷
   rw 1 q60 ∷
   rw 0 q61 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q52 ∷
   rw 4 q50 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q53 ∷
   rw 6 q50 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q53 ∷
   rw 8 q50 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q52 ∷
   rw⁻ 8 q54 ∷
   rw 1 q50 ∷
   rw⁻ 2 q52 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q55 ∷
   rw⁻ 4 q53 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q55 ∷
   rw⁻ 6 q53 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q55 ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 2 q56 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q61 ∷
   rw 3 q55 ∷
   rw 3 q62 ∷
   rw 4 q63 ∷
   rw 9 q50 ∷
   rw 8 q51 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q52 ∷
   rw 10 q50 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q53 ∷
   rw 12 q50 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q53 ∷
   rw 14 q50 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 15 q55 ∷
   rw 14 q54 ∷
   rw 13 q52 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q55 ∷
   rw 11 q53 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q55 ∷
   rw 9 q53 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q55 ∷
   rw 7 q52 ∷
   rw 8 q56 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 6 q51 ∷
   rw 7 q57 ∷
   rw⁻ 6 q58 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q52 ∷
   rw 10 q50 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q53 ∷
   rw 12 q50 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q53 ∷
   rw 14 q50 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 7 q50 ∷
   rw⁻ 8 q52 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q55 ∷
   rw⁻ 10 q53 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q55 ∷
   rw⁻ 12 q53 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q55 ∷
   rw⁻ 14 q52 ∷
   rw⁻ 15 q54 ∷
   rw 8 q56 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 8 q55 ∷
   rw⁻ 5 q23 ∷
   rw 6 q59 ∷
   rw 7 q50 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q52 ∷
   rw 9 q50 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q53 ∷
   rw 11 q50 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q53 ∷
   rw 13 q50 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q52 ∷
   rw⁻ 13 q54 ∷
   rw 14 q55 ∷
   rw 13 q54 ∷
   rw 12 q52 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q55 ∷
   rw 10 q53 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q55 ∷
   rw 8 q53 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q55 ∷
   rw 6 q52 ∷
   rw 7 q56 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q58 ∷
   rw 6 q60 ∷
   rw 5 q61 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q52 ∷
   rw 9 q50 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q53 ∷
   rw 11 q50 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q53 ∷
   rw 13 q50 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q52 ∷
   rw⁻ 13 q54 ∷
   rw 6 q50 ∷
   rw⁻ 7 q52 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q55 ∷
   rw⁻ 9 q53 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q55 ∷
   rw⁻ 11 q53 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q55 ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 7 q56 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q61 ∷
   rw 8 q55 ∷
   rw 8 q64 ∷
   rw 9 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (CS13 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0)
  q67 : Eqn
  q67 = eqn (CS13 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd03)
  q68 : Eqn
  q68 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF012)
  q69 : Eqn
  q69 = eqn (CS13 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd0)
  q70 : Eqn
  q70 = eqn (CS13 ∷ CS03 ∷ []) (CS03 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS03)

-- pass [CS13] [S0 CSd03 TOFF012 Sd0 CS03 TOFF012]: 6 steps
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 : ⟪ (CS13 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 = derive (CS13 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS13 ∷ [])
  (rw 0 q66 ∷
   rw 1 q67 ∷
   rw 2 q68 ∷
   rw 3 q69 ∷
   rw 4 q70 ∷
   rw 5 q68 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [S0 CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q72 ∷ []) Eq.refl

-- pass [CS13] [TOFF012 S0 CSd03 TOFF012 Sd0 CS03]: 6 steps
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 : ⟪ (CS13 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 = derive (CS13 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS13 ∷ [])
  (rw 0 q68 ∷
   rw 1 q66 ∷
   rw 2 q67 ∷
   rw 3 q68 ∷
   rw 4 q69 ∷
   rw 5 q70 ∷ []) Eq.refl
