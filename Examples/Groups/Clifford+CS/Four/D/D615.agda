{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D615 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D012 W using (lem-pass-CCZ123-vs-CS13 ; lem-pass-CCZ123-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D374 W using (lem-pass-CZ13-vs-CS13 ; lem-pass-CZ13-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ123-vs-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D522 W using (lem-pass-CCZ023-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D536 W using (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D544 W using (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D588 W using (lem-T-CZ03-T-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D590 W using (lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D591 W using (lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0 ; lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 ; lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)

private
  q1 : Eqn
  q1 = eqn (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13)
  q2 : Eqn
  q2 = eqn (CZ13 ∷ CS13 ∷ []) (CS13 ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CS13)
  q3 : Eqn
  q3 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q4 : Eqn
  q4 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q5 : Eqn
  q5 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q6 : Eqn
  q6 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q9 : Eqn
  q9 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q10 : Eqn
  q10 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q11 : Eqn
  q11 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q18 : Eqn
  q18 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q19 : Eqn
  q19 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q20 : Eqn
  q20 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q21 : Eqn
  q21 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q22 : Eqn
  q22 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q23 : Eqn
  q23 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q24 : Eqn
  q24 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q25 : Eqn
  q25 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q32 : Eqn
  q32 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q33 : Eqn
  q33 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q34 : Eqn
  q34 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q35 : Eqn
  q35 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q36 : Eqn
  q36 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q37 : Eqn
  q37 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q38 : Eqn
  q38 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q39 : Eqn
  q39 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q40 : Eqn
  q40 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q42 : Eqn
  q42 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q44 : Eqn
  q44 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q45 : Eqn
  q45 = eqn (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023)
  q46 : Eqn
  q46 = eqn (CCZ023 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13)
  q47 : Eqn
  q47 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023)
  q48 : Eqn
  q48 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q49 : Eqn
  q49 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q50 : Eqn
  q50 = eqn (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13)
  q51 : Eqn
  q51 = eqn (CZ13 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CSd13)

-- pass [CZ13 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 516 steps
lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   rw 5 q13 ∷
   rw⁻ 4 q15 ∷
   rw 5 q4 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q17 ∷
   rw 12 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q10 ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 7 q19 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 9 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q32 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw⁻ 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 7 q37 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   rw 5 q25 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 5 q38 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   rw 4 q39 ∷
   rw 7 q19 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q40 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q29 ∷
   rw⁻ 10 q30 ∷
   rw 11 q31 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q39 ∷
   rw 5 q44 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q22 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q14 ∷
   rw 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q17 ∷
   rw 9 q12 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q28 ∷
   rw 1 q3 ∷
   rw 2 q45 ∷
   rw 2 q46 ∷
   rw 4 q47 ∷
   rw 5 q4 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q7 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q48 ∷
   rw⁻ 6 q14 ∷
   rw 5 q48 ∷
   rw⁻ 4 q15 ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q26 ∷
   rw 5 q14 ∷
   rw 6 q26 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q27 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q28 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q12 ∷
   rw 8 q7 ∷
   rw⁻ 7 q12 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q48 ∷
   rw⁻ 5 q14 ∷
   rw 4 q48 ∷
   rw⁻ 3 q15 ∷
   rw 4 q18 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 4 q49 ∷
   rw 3 q28 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   rw 4 q3 ∷
   rw 8 q4 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q6 ∷
   rw 8 q11 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q10 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 9 q13 ∷
   rw⁻ 8 q14 ∷
   rw 7 q13 ∷
   rw⁻ 6 q15 ∷
   rw 7 q4 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q14 ∷
   rw 11 q16 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q17 ∷
   rw 14 q12 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 9 q19 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q22 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q26 ∷
   rw 9 q14 ∷
   rw 10 q26 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q27 ∷
   rw 13 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q28 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q29 ∷
   rw 13 q30 ∷
   rw 11 q31 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q22 ∷
   rw 9 q32 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 12 q36 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q35 ∷
   rw 9 q37 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 7 q38 ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q34 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q35 ∷
   rw 6 q39 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q40 ∷
   rw 11 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q29 ∷
   rw⁻ 12 q30 ∷
   rw 13 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q41 ∷
   rw 8 q42 ∷
   rw 9 q43 ∷
   rw 10 q42 ∷
   rw 11 q39 ∷
   rw 7 q44 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   rw 8 q22 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q28 ∷
   rw 3 q3 ∷
   rw 4 q45 ∷
   rw 4 q46 ∷
   rw 6 q47 ∷
   rw 7 q4 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q7 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q48 ∷
   rw⁻ 8 q14 ∷
   rw 7 q48 ∷
   rw⁻ 6 q15 ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q12 ∷
   rw 10 q7 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q48 ∷
   rw⁻ 7 q14 ∷
   rw 6 q48 ∷
   rw⁻ 5 q15 ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 6 q49 ∷
   rw 5 q28 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q54 : Eqn
  q54 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1833 W)
  q55 : Eqn
  q55 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q56 : Eqn
  q56 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1677 W)
  q57 : Eqn
  q57 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1834 W)
  q58 : Eqn
  q58 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X3 CKd31 X3] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 31 steps
lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw 3 q52 ∷
   rw 2 q53 ∷
   re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q35 ∷
   rw 0 q53 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw 1 q55 ∷
   rw 4 q34 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 3 q55 ∷
   rw 4 q35 ∷
   rw 1 q56 ∷
   rw 2 q57 ∷
   rw 2 q58 ∷
   rw 6 q57 ∷
   rw 10 q34 ∷
   rw 9 q52 ∷
   rw 8 q53 ∷
   re 7 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 6 q53 ∷
   rw 7 q54 ∷
   rw⁻ 6 q52 ∷
   rw 7 q55 ∷
   rw 10 q34 ∷
   re 8 3 (CK31⁻ ∷ []) ∷
   rw 9 q55 ∷
   rw 10 q35 ∷
   rw 7 q56 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (CK21⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1478 W)
  q60 : Eqn
  q60 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q61 : Eqn
  q61 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ []) (wn 1479 W)

-- pass [CKd21] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CKd21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK21⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK21⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21⁻ ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 13 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CK21 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1476 W)
  q63 : Eqn
  q63 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q64 : Eqn
  q64 = eqn (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ []) (wn 1477 W)

-- pass [CK21] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CK21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ [])
  (rw 0 q62 ∷
   rw 1 q63 ∷
   rw 13 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1835 W)
  q66 : Eqn
  q66 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q67 : Eqn
  q67 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1836 W)

-- pass [X1 CSd10 X1] [Sd0 Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0 S0]: 3 steps
lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q65 ∷
   rw 3 q66 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1837 W)
  q69 : Eqn
  q69 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1838 W)

-- pass [X1 CSd10 X1] [Sd0 K0 K0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 Kd0 Kd0 S0]: 3 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q68 ∷
   rw 5 q66 ∷
   rw 9 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (CS01⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1817 W)
  q71 : Eqn
  q71 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0)
  q72 : Eqn
  q72 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 1839 W)
  q73 : Eqn
  q73 = eqn (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 1840 W)
  q74 : Eqn
  q74 = eqn (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01⁻ ∷ []) (wn 1818 W)

-- CA CSd10 Gad(t=0, W=(), d=SdKKKK, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ : ⟪ (CS01⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ = derive (CS01⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q70 ∷
   rw 1 q71 ∷
   rw 0 q72 ∷
   rw 10 q73 ∷
   rw 16 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 1841 W)
  q76 : Eqn
  q76 = eqn (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) (wn 1842 W)
  q77 : Eqn
  q77 = eqn (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ ι ∷ ι ∷ []) (wn 1843 W)
  q78 : Eqn
  q78 = eqn (ι ∷ Toff012 ∷ []) (Toff012 ∷ ι ∷ []) (wn 1738 W)
  q79 : Eqn
  q79 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q80 : Eqn
  q80 = eqn (ι ∷ CS02 ∷ []) (CS02 ∷ ι ∷ []) (wn 1739 W)
  q81 : Eqn
  q81 = eqn (ι ∷ CS02⁻ ∷ []) (CS02⁻ ∷ ι ∷ []) (wn 1740 W)
  q82 : Eqn
  q82 = eqn (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03)
  q83 : Eqn
  q83 = eqn (S0 ∷ S0 ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) [] (wn 1844 W)

-- spell Gad(t=0, W=(), d=SdKSdK, e=1) -> Gad(t=0, W=(), d=KdSd, e=1): 46 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩ : ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩ = derive (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ [])
  (rw 0 q75 ∷
   rw 12 q76 ∷
   rw 2 q77 ∷
   rw 5 q78 ∷
   rw 8 q34 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 6 q79 ∷
   rw 7 q80 ∷
   rw 8 q34 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q79 ∷
   rw 8 q35 ∷
   rw 7 q78 ∷
   rw 10 q34 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 8 q79 ∷
   rw 9 q81 ∷
   rw 10 q34 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw⁻ 9 q79 ∷
   rw 10 q35 ∷
   rw 4 q78 ∷
   rw 7 q34 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw 5 q79 ∷
   rw 6 q80 ∷
   rw 7 q34 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q79 ∷
   rw 7 q35 ∷
   rw 6 q78 ∷
   rw 9 q34 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw 7 q79 ∷
   rw 8 q81 ∷
   rw 9 q34 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q79 ∷
   rw 9 q35 ∷
   rw 3 q82 ∷
   rw 2 q82 ∷
   rw 6 q83 ∷ []) Eq.refl
