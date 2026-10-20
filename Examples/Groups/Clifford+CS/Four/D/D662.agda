{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D662 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D378 W using (lem-pass-CCZ123-vs-CS23 ; lem-pass-CCZ123-vs-CSd23 ; lem-pass-CZ12-vs-CS23 ; lem-pass-CZ12-vs-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D387 W using (lem-pass-CZ01-vs-CS23)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ013-vs-CS23)
open import Examples.Groups.Clifford+CS.Four.D.D514 W using (lem-pass-CCZ013-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D642 W using (lem-pass-CCZ013-vs-TOFF201)

private
  q1 : Eqn
  q1 = eqn [] (Toff201 ∷ Toff201 ∷ []) (wn 1521 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q7 : Eqn
  q7 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q9 : Eqn
  q9 = eqn (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 333 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q16 : Eqn
  q16 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q17 : Eqn
  q17 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q18 : Eqn
  q18 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q21 : Eqn
  q21 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q22 : Eqn
  q22 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q23 : Eqn
  q23 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q28 : Eqn
  q28 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q29 : Eqn
  q29 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q30 : Eqn
  q30 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q31 : Eqn
  q31 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q32 : Eqn
  q32 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q33 : Eqn
  q33 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q34 : Eqn
  q34 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q36 : Eqn
  q36 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q37 : Eqn
  q37 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q38 : Eqn
  q38 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q39 : Eqn
  q39 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q40 : Eqn
  q40 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q44 : Eqn
  q44 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q45 : Eqn
  q45 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q46 : Eqn
  q46 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q47 : Eqn
  q47 = eqn (CZ12 ∷ Toff201 ∷ []) (Toff201 ∷ CZ01 ∷ CZ12 ∷ []) (wn 1991 W)
  q48 : Eqn
  q48 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) lem-pass-CCZ013-vs-CCZ123
  q49 : Eqn
  q49 = eqn (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS23)
  q50 : Eqn
  q50 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CS23)
  q51 : Eqn
  q51 = eqn (CZ12 ∷ CS23 ∷ []) (CS23 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS23)
  q52 : Eqn
  q52 = eqn (CZ01 ∷ CS23 ∷ []) (CS23 ∷ CZ01 ∷ []) (lem-pass-CZ01-vs-CS23)
  q53 : Eqn
  q53 = eqn (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-TOFF201)
  q54 : Eqn
  q54 = eqn (CZ01 ∷ Toff201 ∷ []) (Toff201 ∷ CZ01 ∷ []) (wn 1992 W)
  q55 : Eqn
  q55 = eqn (CZ01 ∷ CZ01 ∷ []) [] (wn 1877 W)
  q56 : Eqn
  q56 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q57 : Eqn
  q57 = eqn (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd23)
  q58 : Eqn
  q58 = eqn (CZ12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd23)

-- pass [CZ12 CCZ123] [TOFF201 CS23 TOFF201 CSd23]: 806 steps
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 = derive (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 5 q2 ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 11 q3 ∷
   rw⁻ 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw⁻ 4 q4 ∷
   rw 5 q9 ∷
   re 5 8 (Toff201 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 8 q8 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 6 q11 ∷
   rw⁻ 5 q12 ∷
   rw 4 q11 ∷
   rw⁻ 3 q13 ∷
   rw 4 q2 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 7 q12 ∷
   rw 8 q14 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q15 ∷
   rw 11 q10 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q16 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw⁻ 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw 6 q17 ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q20 ∷
   rw 9 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q21 ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q19 ∷
   rw 6 q23 ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q13 ∷
   rw 5 q24 ∷
   rw 6 q12 ∷
   rw 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q26 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q27 ∷
   rw 10 q28 ∷
   rw 8 q29 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q20 ∷
   rw 6 q30 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q20 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q33 ∷
   rw⁻ 7 q34 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw⁻ 9 q34 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 6 q35 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q20 ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q17 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q19 ∷
   rw 4 q23 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 7 q2 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q3 ∷
   rw 12 q36 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q32 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q33 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q5 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw 8 q7 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q10 ∷
   rw 6 q8 ∷
   rw⁻ 5 q10 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw⁻ 8 q38 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw 7 q39 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q3 ∷
   rw 10 q36 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q36 ∷
   rw 5 q37 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 5 q40 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q32 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q33 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q10 ∷
   rw 5 q25 ∷
   rw 6 q10 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q41 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q42 ∷
   rw 8 q10 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q41 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q32 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q33 ∷
   rw⁻ 6 q38 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw⁻ 8 q38 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw 5 q39 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 7 q12 ∷
   rw 8 q24 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q12 ∷
   rw 9 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q15 ∷
   rw 12 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q16 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q26 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q32 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q33 ∷
   rw 3 q43 ∷
   rw 6 q17 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q44 ∷
   rw 8 q17 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q27 ∷
   rw⁻ 9 q28 ∷
   rw 10 q29 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q12 ∷
   rw 7 q14 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q16 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 7 q12 ∷
   rw 8 q24 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q26 ∷
   rw 4 q45 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q46 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q20 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q27 ∷
   rw⁻ 10 q28 ∷
   rw 11 q29 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q32 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q33 ∷
   rw⁻ 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw⁻ 8 q34 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw 5 q35 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q20 ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q13 ∷
   rw 4 q24 ∷
   rw 5 q12 ∷
   rw 6 q24 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q26 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q12 ∷
   rw 5 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q15 ∷
   rw 8 q10 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q16 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q32 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q33 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q25 ∷
   rw 5 q10 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q41 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q42 ∷
   rw 7 q10 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q41 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q15 ∷
   rw 9 q10 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q32 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q33 ∷
   rw⁻ 5 q38 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q33 ∷
   rw⁻ 7 q38 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw 4 q39 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   rw 4 q26 ∷
   rw 0 q47 ∷
   rw⁻ 3 q48 ∷
   rw 4 q49 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   rw 1 q52 ∷
   rw 5 q1 ∷
   rw 9 q2 ∷
   re 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 15 q3 ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw⁻ 8 q4 ∷
   rw 9 q9 ∷
   re 9 8 (Toff201 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q8 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 10 q11 ∷
   rw⁻ 9 q12 ∷
   rw 8 q11 ∷
   rw⁻ 7 q13 ∷
   rw 8 q2 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 11 q12 ∷
   rw 12 q14 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q15 ∷
   rw 15 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q16 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 13 q3 ∷
   rw⁻ 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw⁻ 6 q4 ∷
   rw 7 q9 ∷
   re 7 8 (Toff201 ∷ []) ∷
   rw 10 q17 ∷
   re 9 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 16 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q20 ∷
   rw 13 q17 ∷
   re 14 3 (CX02 ∷ []) ∷
   rw 12 q21 ∷
   rw 11 q17 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q22 ∷
   rw 9 q19 ∷
   rw 10 q23 ∷
   re 10 8 (Toff102 ∷ []) ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q13 ∷
   rw 9 q24 ∷
   rw 10 q12 ∷
   rw 11 q24 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q25 ∷
   rw 14 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q26 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q27 ∷
   rw 14 q28 ∷
   rw 12 q29 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 13 q20 ∷
   rw 10 q30 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q20 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw⁻ 11 q34 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw⁻ 13 q34 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 10 q35 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   re 9 3 (CCZ013 ∷ []) ∷
   re 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q20 ∷
   rw 11 q17 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q21 ∷
   rw 9 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q22 ∷
   rw 7 q19 ∷
   rw 8 q23 ∷
   re 8 8 (Toff102 ∷ []) ∷
   rw 11 q2 ∷
   re 10 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q36 ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   rw 13 q7 ∷
   rw 12 q6 ∷
   rw 11 q8 ∷
   rw 10 q36 ∷
   rw 11 q37 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q32 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q34 ∷
   rw 13 q32 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q34 ∷
   rw 15 q32 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q33 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q10 ∷
   rw 14 q5 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q10 ∷
   rw 12 q7 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q10 ∷
   rw 10 q8 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 10 q32 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw⁻ 14 q38 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q33 ∷
   rw 11 q39 ∷
   re 11 5 (CCZ012 ∷ []) ∷
   re 10 3 (CCZ013 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q36 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw 8 q36 ∷
   rw 9 q37 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 9 q40 ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q32 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q34 ∷
   rw 13 q32 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q34 ∷
   rw 15 q32 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q33 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q41 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q42 ∷
   rw 12 q10 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 11 q41 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw 9 q39 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q13 ∷
   rw 10 q24 ∷
   rw 11 q12 ∷
   rw 12 q24 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q25 ∷
   rw 15 q10 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q13 ∷
   rw 11 q14 ∷
   rw 12 q12 ∷
   rw 13 q14 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q10 ∷
   rw 15 q15 ∷
   rw 16 q10 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 10 q16 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   re 9 3 (CCZ023 ∷ []) ∷
   rw 10 q26 ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q32 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q34 ∷
   rw 12 q32 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q34 ∷
   rw 14 q32 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q33 ∷
   rw 7 q43 ∷
   rw 10 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 9 q44 ∷
   rw 12 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q27 ∷
   rw⁻ 13 q28 ∷
   rw 14 q29 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q12 ∷
   rw 11 q14 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q16 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q13 ∷
   rw 10 q24 ∷
   rw 11 q12 ∷
   rw 12 q24 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q25 ∷
   rw 15 q10 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q26 ∷
   rw 8 q45 ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q46 ∷
   re 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q20 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q27 ∷
   rw⁻ 14 q28 ∷
   rw 15 q29 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q34 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw⁻ 12 q34 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw 9 q35 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   rw 9 q20 ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q13 ∷
   rw 8 q24 ∷
   rw 9 q12 ∷
   rw 10 q24 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q10 ∷
   rw 12 q25 ∷
   rw 13 q10 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q26 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q12 ∷
   rw 9 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q15 ∷
   rw 12 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q16 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q32 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q34 ∷
   rw 12 q32 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q34 ∷
   rw 14 q32 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q33 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q41 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q42 ∷
   rw 11 q10 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q41 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q10 ∷
   rw 12 q15 ∷
   rw 13 q10 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q32 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw⁻ 9 q38 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw⁻ 11 q38 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw 8 q39 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 7 3 (CCZ013 ∷ []) ∷
   rw 8 q26 ∷
   rw 4 q53 ∷
   rw 3 q47 ∷
   rw 2 q54 ∷
   rw⁻ 7 q48 ∷
   rw 3 q55 ∷
   rw 6 q32 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q32 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q33 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw 8 q34 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw 6 q34 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q32 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q33 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 7 q34 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw 5 q34 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q33 ∷
   rw 5 q35 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 5 q56 ∷
   rw 4 q33 ∷
   rw 4 q57 ∷
   rw 3 q58 ∷ []) Eq.refl
