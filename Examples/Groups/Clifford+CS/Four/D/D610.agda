{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D610 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D370 W using (lem-pass-CZ12-vs-CS13 ; lem-pass-CZ12-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D374 W using (lem-pass-CZ13-vs-CS13 ; lem-pass-CZ13-vs-CSd13 ; lem-pass-Z1-vs-CS13 ; lem-pass-Z1-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D380 W using (lem-pass-CS03-vs-CZ13 ; lem-pass-CS03-vs-CZ23 ; lem-pass-CS03-vs-Z1 ; lem-pass-CS03-vs-Z2 ; lem-pass-CS03-vs-Z3 ; lem-pass-CS03-vs-iI ; lem-pass-CSd03-vs-CZ13 ; lem-pass-CSd03-vs-CZ23 ; lem-pass-CSd03-vs-Z1 ; lem-pass-CSd03-vs-Z2 ; lem-pass-CSd03-vs-Z3 ; lem-pass-CSd03-vs-iI ; lem-pass-TOFF012-vs-CZ12 ; lem-pass-TOFF012-vs-Z1 ; lem-pass-TOFF012-vs-Z2 ; lem-pass-TOFF012-vs-Z3 ; lem-pass-TOFF012-vs-iI)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ123-vs-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D522 W using (lem-pass-CCZ023-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D529 W using (lem-pass-CS03-vs-CZ12 ; lem-pass-CSd03-vs-CZ12)
open import Examples.Groups.Clifford+CS.Four.D.D536 W using (lem-pass-CCZ012-vs-CCZ013)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-pass-TOFF012-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D541 W using (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D588 W using (lem-T-CZ03-T-at1023 ; lem-pass-CS03-vs-CCZ123 ; lem-pass-CSd03-vs-CCZ123 ; lem-pass-TOFF012-vs-CZ13 ; lem-pass-TOFF012-vs-CZ23 ; lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2)

private
  q1 : Eqn
  q1 = eqn (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13)
  q2 : Eqn
  q2 = eqn (CZ13 ∷ CS13 ∷ []) (CS13 ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CS13)
  q3 : Eqn
  q3 = eqn (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS13)
  q4 : Eqn
  q4 = eqn (Z1 ∷ CS13 ∷ []) (CS13 ∷ Z1 ∷ []) (lem-pass-Z1-vs-CS13)
  q5 : Eqn
  q5 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q8 : Eqn
  q8 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q10 : Eqn
  q10 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q11 : Eqn
  q11 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q12 : Eqn
  q12 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q13 : Eqn
  q13 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q20 : Eqn
  q20 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q21 : Eqn
  q21 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q22 : Eqn
  q22 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q23 : Eqn
  q23 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q24 : Eqn
  q24 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q25 : Eqn
  q25 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q26 : Eqn
  q26 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q27 : Eqn
  q27 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q31 : Eqn
  q31 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q32 : Eqn
  q32 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q34 : Eqn
  q34 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q35 : Eqn
  q35 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q36 : Eqn
  q36 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q37 : Eqn
  q37 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q38 : Eqn
  q38 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q39 : Eqn
  q39 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q40 : Eqn
  q40 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q42 : Eqn
  q42 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q44 : Eqn
  q44 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q45 : Eqn
  q45 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q46 : Eqn
  q46 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q47 : Eqn
  q47 = eqn (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023)
  q48 : Eqn
  q48 = eqn (CZ12 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) (wn 1806 W)
  q49 : Eqn
  q49 = eqn (Z1 ∷ Toff102 ∷ []) (Toff102 ∷ Z1 ∷ CZ02 ∷ []) (wn 1807 W)
  q50 : Eqn
  q50 = eqn (CCZ023 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13)
  q51 : Eqn
  q51 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023)
  q52 : Eqn
  q52 = eqn (CZ02 ∷ CZ02 ∷ []) [] (wn 1808 W)
  q53 : Eqn
  q53 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q54 : Eqn
  q54 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q55 : Eqn
  q55 = eqn (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13)
  q56 : Eqn
  q56 = eqn (CZ13 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CSd13)
  q57 : Eqn
  q57 = eqn (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd13)
  q58 : Eqn
  q58 = eqn (Z1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Z1 ∷ []) (lem-pass-Z1-vs-CSd13)

-- pass [Z1 CZ12 CZ13 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 526 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 3 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 0 q4 ∷
   rw 4 q5 ∷
   rw 8 q6 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q12 ∷
   rw 7 q8 ∷
   rw 8 q13 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q14 ∷
   rw 11 q12 ∷
   rw⁻ 10 q14 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw 7 q15 ∷
   rw⁻ 6 q17 ∷
   rw 7 q6 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 10 q16 ∷
   rw 11 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q19 ∷
   rw 14 q14 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q20 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw 7 q10 ∷
   rw 6 q12 ∷
   rw 5 q8 ∷
   rw 6 q13 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 9 q21 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q24 ∷
   rw 12 q21 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q25 ∷
   rw 10 q21 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q26 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q28 ∷
   rw 9 q16 ∷
   rw 10 q28 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   rw 12 q29 ∷
   rw 13 q14 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q30 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q31 ∷
   rw 13 q32 ∷
   rw 11 q33 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q24 ∷
   rw 9 q34 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q24 ∷
   rw 7 q35 ∷
   rw 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q37 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q37 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q37 ∷
   rw 9 q39 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q24 ∷
   rw 10 q21 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q25 ∷
   rw 8 q21 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q26 ∷
   rw 6 q23 ∷
   rw 7 q27 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 7 q40 ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q36 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q38 ∷
   rw 11 q36 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q38 ∷
   rw 13 q36 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q37 ∷
   rw 6 q41 ∷
   rw 9 q21 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q42 ∷
   rw 11 q21 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q31 ∷
   rw⁻ 12 q32 ∷
   rw 13 q33 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q20 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q43 ∷
   rw 8 q44 ∷
   rw 9 q45 ∷
   rw 10 q44 ∷
   rw 11 q41 ∷
   rw 7 q46 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   rw 8 q24 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q30 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 7 q16 ∷
   rw 8 q18 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   rw 10 q19 ∷
   rw 11 q14 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q20 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q20 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q30 ∷
   rw 3 q5 ∷
   rw 4 q47 ∷
   rw 2 q48 ∷
   rw 1 q49 ∷
   rw 6 q50 ∷
   rw 8 q51 ∷
   rw 3 q52 ∷
   rw 7 q6 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q30 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q14 ∷
   rw 11 q9 ∷
   rw⁻ 10 q14 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q53 ∷
   rw⁻ 8 q16 ∷
   rw 7 q53 ∷
   rw⁻ 6 q17 ∷
   rw 7 q20 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q17 ∷
   rw 6 q28 ∷
   rw 7 q16 ∷
   rw 8 q28 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   rw 10 q29 ∷
   rw 11 q14 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q30 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q14 ∷
   rw 10 q9 ∷
   rw⁻ 9 q14 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q53 ∷
   rw⁻ 7 q16 ∷
   rw 6 q53 ∷
   rw⁻ 5 q17 ∷
   rw 6 q20 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 6 q54 ∷
   rw 5 q30 ∷
   rw 5 q55 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q58 ∷
   rw 6 q5 ∷
   rw 10 q6 ∷
   re 9 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q10 ∷
   rw 10 q12 ∷
   rw 9 q8 ∷
   rw 10 q13 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q14 ∷
   rw 13 q12 ∷
   rw⁻ 12 q14 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw 9 q15 ∷
   rw⁻ 8 q17 ∷
   rw 9 q6 ∷
   rw 10 q17 ∷
   rw 11 q18 ∷
   rw 12 q16 ∷
   rw 13 q18 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q14 ∷
   rw 15 q19 ∷
   rw 16 q14 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 10 q20 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   re 9 3 (CCZ023 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q12 ∷
   rw 7 q8 ∷
   rw 8 q13 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 11 q21 ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 17 q22 ∷
   rw 16 q23 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q24 ∷
   rw 14 q21 ∷
   re 15 3 (CX02 ∷ []) ∷
   rw 13 q25 ∷
   rw 12 q21 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q26 ∷
   rw 10 q23 ∷
   rw 11 q27 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q17 ∷
   rw 10 q28 ∷
   rw 11 q16 ∷
   rw 12 q28 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   rw 14 q29 ∷
   rw 15 q14 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q30 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q31 ∷
   rw 15 q32 ∷
   rw 13 q33 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 14 q24 ∷
   rw 11 q34 ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q24 ∷
   rw 9 q35 ∷
   rw 10 q36 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q37 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q37 ∷
   rw⁻ 14 q38 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q37 ∷
   rw 11 q39 ∷
   re 11 5 (CCZ012 ∷ []) ∷
   re 10 3 (CCZ013 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q24 ∷
   rw 12 q21 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q25 ∷
   rw 10 q21 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q26 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 9 q40 ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q36 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q38 ∷
   rw 13 q36 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q38 ∷
   rw 15 q36 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q37 ∷
   rw 8 q41 ∷
   rw 11 q21 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 10 q42 ∷
   rw 13 q21 ∷
   re 11 3 (CX02 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q31 ∷
   rw⁻ 14 q32 ∷
   rw 15 q33 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q18 ∷
   rw 11 q16 ∷
   rw 12 q18 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   rw 14 q19 ∷
   rw 15 q14 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q20 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q43 ∷
   rw 10 q44 ∷
   rw 11 q45 ∷
   rw 12 q44 ∷
   rw 13 q41 ∷
   rw 9 q46 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   rw 10 q24 ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q30 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q20 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q18 ∷
   rw 11 q16 ∷
   rw 12 q18 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   rw 14 q19 ∷
   rw 15 q14 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q20 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   rw 9 q30 ∷
   rw 5 q5 ∷
   rw 6 q47 ∷
   rw 4 q48 ∷
   rw 3 q49 ∷
   rw 8 q50 ∷
   rw 10 q51 ∷
   rw 5 q52 ∷
   rw 9 q6 ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q30 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q14 ∷
   rw 13 q9 ∷
   rw⁻ 12 q14 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q53 ∷
   rw⁻ 10 q16 ∷
   rw 9 q53 ∷
   rw⁻ 8 q17 ∷
   rw 9 q20 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q28 ∷
   rw 9 q16 ∷
   rw 10 q28 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q14 ∷
   rw 12 q29 ∷
   rw 13 q14 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q30 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q14 ∷
   rw 12 q9 ∷
   rw⁻ 11 q14 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q53 ∷
   rw⁻ 9 q16 ∷
   rw 8 q53 ∷
   rw⁻ 7 q17 ∷
   rw 8 q20 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   rw 8 q54 ∷
   rw 7 q30 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (wn 1535 W)
  q60 : Eqn
  q60 = eqn (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) (wn 1809 W)
  q61 : Eqn
  q61 = eqn (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) (low₃-comm (CCZ) ((K • iI)))
  q62 : Eqn
  q62 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wn 1810 W)
  q63 : Eqn
  q63 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CCZ013)
  q64 : Eqn
  q64 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wn 1811 W)
  q65 : Eqn
  q65 = eqn (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) (low₃-comm (CCZ) (K))
  q66 : Eqn
  q66 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q67 : Eqn
  q67 = eqn (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wn 1538 W)

-- pass [TOFF201] [CCZ013]: 13 steps
lem-pass-TOFF201-vs-CCZ013 : ⟪ (Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CCZ013 = derive (Toff201 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff201 ∷ [])
  (rw 0 q59 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 2 q60 ∷
   rw⁻ 3 q61 ∷
   rw 4 q62 ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 1 q63 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 q64 ∷
   rw⁻ 1 q65 ∷
   rw 2 q66 ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw 1 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (CS03 ∷ ι ∷ []) (ι ∷ CS03 ∷ []) (lem-pass-CS03-vs-iI)
  q69 : Eqn
  q69 = eqn (CS03 ∷ Z1 ∷ []) (Z1 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z1)
  q70 : Eqn
  q70 = eqn (CS03 ∷ Z2 ∷ []) (Z2 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z2)
  q71 : Eqn
  q71 = eqn (CS03 ∷ CZ12 ∷ []) (CZ12 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ12)
  q72 : Eqn
  q72 = eqn (CS03 ∷ Z3 ∷ []) (Z3 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z3)
  q73 : Eqn
  q73 = eqn (CS03 ∷ CZ13 ∷ []) (CZ13 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ13)
  q74 : Eqn
  q74 = eqn (CS03 ∷ CZ23 ∷ []) (CZ23 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ23)
  q75 : Eqn
  q75 = eqn (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CCZ123)

-- pass [CS03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (CS03 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ [])
  (rw 0 q68 ∷
   rw 1 q68 ∷
   rw 2 q69 ∷
   rw 3 q70 ∷
   rw 4 q71 ∷
   rw 5 q72 ∷
   rw 6 q73 ∷
   rw 7 q74 ∷
   rw 8 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI)
  q77 : Eqn
  q77 = eqn (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z1)
  q78 : Eqn
  q78 = eqn (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z2)
  q79 : Eqn
  q79 = eqn (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ12)
  q80 : Eqn
  q80 = eqn (Toff012 ∷ Z3 ∷ []) (Z3 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z3)
  q81 : Eqn
  q81 = eqn (Toff012 ∷ CZ13 ∷ []) (CZ13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ13)
  q82 : Eqn
  q82 = eqn (Toff012 ∷ CZ23 ∷ []) (CZ23 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ23)
  q83 : Eqn
  q83 = eqn (Toff012 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CCZ123)

-- pass [TOFF012] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ [])
  (rw 0 q76 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw 3 q78 ∷
   rw 4 q79 ∷
   rw 5 q80 ∷
   rw 6 q81 ∷
   rw 7 q82 ∷
   rw 8 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (CS03⁻ ∷ ι ∷ []) (ι ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-iI)
  q85 : Eqn
  q85 = eqn (CS03⁻ ∷ Z1 ∷ []) (Z1 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z1)
  q86 : Eqn
  q86 = eqn (CS03⁻ ∷ Z2 ∷ []) (Z2 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z2)
  q87 : Eqn
  q87 = eqn (CS03⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ12)
  q88 : Eqn
  q88 = eqn (CS03⁻ ∷ Z3 ∷ []) (Z3 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z3)
  q89 : Eqn
  q89 = eqn (CS03⁻ ∷ CZ13 ∷ []) (CZ13 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ13)
  q90 : Eqn
  q90 = eqn (CS03⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ23)
  q91 : Eqn
  q91 = eqn (CS03⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CCZ123)

-- pass [CSd03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ [])
  (rw 0 q84 ∷
   rw 1 q84 ∷
   rw 2 q85 ∷
   rw 3 q86 ∷
   rw 4 q87 ∷
   rw 5 q88 ∷
   rw 6 q89 ∷
   rw 7 q90 ∷
   rw 8 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q93 : Eqn
  q93 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q94 : Eqn
  q94 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1676 W)
  q95 : Eqn
  q95 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q96 : Eqn
  q96 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q97 : Eqn
  q97 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q98 : Eqn
  q98 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q99 : Eqn
  q99 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1677 W)
  q100 : Eqn
  q100 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q101 : Eqn
  q101 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1485 W)
  q102 : Eqn
  q102 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [X3 CKd30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q36 ∷
   rw 3 q92 ∷
   rw 2 q93 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q37 ∷
   rw 0 q93 ∷
   rw 1 q94 ∷
   rw⁻ 0 q92 ∷
   rw 1 q95 ∷
   rw 4 q36 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q95 ∷
   rw 4 q37 ∷
   rw 5 q6 ∷
   rw⁻ 4 q96 ∷
   rw⁻ 3 q97 ∷
   re 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q14 ∷
   rw 3 q98 ∷
   rw⁻ 2 q14 ∷
   re 3 3 (CK31⁻ ∷ []) ∷
   rw⁻ 1 q97 ∷
   rw 2 q99 ∷
   rw 1 q96 ∷
   rw 2 q97 ∷
   re 4 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   rw 4 q100 ∷
   rw 5 q14 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q97 ∷
   rw 5 q30 ∷
   rw 5 q36 ∷
   rw 4 q93 ∷
   re 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q37 ∷
   rw 2 q93 ∷
   rw 3 q101 ∷
   rw 2 q95 ∷
   rw 5 q36 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q95 ∷
   rw 5 q37 ∷
   rw 2 q102 ∷
   rw 9 q36 ∷
   rw 8 q93 ∷
   re 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q37 ∷
   rw 6 q93 ∷
   rw 7 q101 ∷
   rw 6 q95 ∷
   rw 9 q36 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q95 ∷
   rw 9 q37 ∷
   rw 10 q36 ∷
   rw 9 q92 ∷
   rw 8 q93 ∷
   re 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q37 ∷
   rw 6 q93 ∷
   rw 7 q94 ∷
   rw⁻ 6 q92 ∷
   rw 7 q95 ∷
   rw 10 q36 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q95 ∷
   rw 10 q37 ∷
   rw 11 q6 ∷
   rw⁻ 10 q96 ∷
   rw⁻ 9 q97 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q14 ∷
   rw 9 q98 ∷
   rw⁻ 8 q14 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw⁻ 7 q97 ∷
   rw 8 q99 ∷
   rw 7 q96 ∷
   rw 8 q97 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   rw 10 q100 ∷
   rw 11 q14 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q97 ∷
   rw 11 q30 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q104 : Eqn
  q104 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q105 : Eqn
  q105 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q106 : Eqn
  q106 = eqn (X3 ∷ CK30 ∷ X3 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2)
  q107 : Eqn
  q107 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK30] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 27 steps
lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CK30 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (CK30 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q103 ∷
   rw 1 q104 ∷
   rw 2 q36 ∷
   rw 1 q93 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q37 ∷
   rw 1 q105 ∷
   rw 0 q95 ∷
   rw 1 q95 ∷
   rw 4 q36 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q95 ∷
   rw 4 q37 ∷
   rw 1 q106 ∷
   rw 13 q36 ∷
   rw 12 q93 ∷
   rw 11 q93 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q37 ∷
   rw 9 q93 ∷
   rw 10 q107 ∷
   rw 9 q95 ∷
   rw 12 q36 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q37 ∷
   rw⁻ 0 q104 ∷
   rw⁻ 1 q103 ∷ []) Eq.refl
