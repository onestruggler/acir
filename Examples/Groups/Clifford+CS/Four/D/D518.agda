{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D518 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-pass-CCZ013-vs-CSd13 ; lem-pass-CCZ013-vs-CZ13 ; lem-pass-CS02-vs-CS03 ; lem-pass-Sd0-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D021 W using (lem-pass-CS23-vs-S0)
open import Examples.Groups.Clifford+CS.Four.D.D024 W using (lem-comm-CCZ012-CZ03 ; lem-pass-S0-vs-CSd23)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q5 : Eqn
  q5 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q8 : Eqn
  q8 = eqn (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) (wn 467 W)
  q9 : Eqn
  q9 = eqn (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) (wn 468 W)
  q10 : Eqn
  q10 = eqn (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wn 469 W)
  q11 : Eqn
  q11 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q12 : Eqn
  q12 = eqn (S2⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S2⁻ ∷ []) (wn 1384 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q14 : Eqn
  q14 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q15 : Eqn
  q15 = eqn (S2 ∷ Toff012 ∷ []) (Toff012 ∷ S2 ∷ []) (wn 1385 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q17 : Eqn
  q17 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q19 : Eqn
  q19 = eqn (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 1386 W)
  q20 : Eqn
  q20 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q21 : Eqn
  q21 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q22 : Eqn
  q22 = eqn (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CSd13)
  q23 : Eqn
  q23 = eqn (CCZ013 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CZ13)
  q24 : Eqn
  q24 = eqn (S3 ∷ S3⁻ ∷ []) [] (wn 154 W)
  q25 : Eqn
  q25 = eqn (CS13 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ []) [] (wn 1387 W)
  q26 : Eqn
  q26 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q27 : Eqn
  q27 = eqn (S0⁻ ∷ CS03 ∷ []) (CS03 ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CS03
  q28 : Eqn
  q28 = eqn (CS02 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ []) lem-pass-CS02-vs-CS03

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part2: 466 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 : ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 = derive (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ [])
  (re 15 3 (Toff013 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CZ13 ∷ []) ∷
   re 18 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw⁻ 21 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 18 q4 ∷
   re 18 5 (CCZ012 ∷ []) ∷
   re 17 3 (CCZ013 ∷ []) ∷
   rw 18 q3 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 16 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 15 q5 ∷
   rw 18 q1 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q6 ∷
   rw 23 q3 ∷
   rw 22 q6 ∷
   rw 21 q5 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 19 q2 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 15 q5 ∷
   rw 16 q7 ∷
   re 16 8 (Toff012 ∷ []) ∷
   re 14 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 14 q1 ∷
   rw⁻ 15 q5 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q6 ∷
   rw 15 q7 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 14 3 (Toff013 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CZ13 ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 22 q3 ∷
   rw 21 q6 ∷
   rw 20 q5 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 18 q2 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 14 q5 ∷
   rw 15 q7 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q9 ∷
   re 14 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 13 q1 ∷
   rw⁻ 14 q5 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw⁻ 16 q2 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw⁻ 18 q2 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 14 q7 ∷
   re 14 8 (Toff012 ∷ []) ∷
   re 13 3 (Toff013 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q1 ∷
   re 13 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 14 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 21 q3 ∷
   rw 20 q6 ∷
   rw 19 q5 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 13 q5 ∷
   rw 14 q7 ∷
   re 14 8 (Toff012 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q10 ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 12 q1 ∷
   rw⁻ 13 q5 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 13 q7 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 12 3 (Toff013 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 16 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 16 q4 ∷
   re 16 5 (CCZ012 ∷ []) ∷
   re 15 3 (CCZ013 ∷ []) ∷
   rw 16 q3 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 20 q3 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 12 q5 ∷
   rw 13 q7 ∷
   re 13 8 (Toff012 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 11 q1 ∷
   rw⁻ 12 q5 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw⁻ 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw⁻ 16 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 12 q7 ∷
   re 12 8 (Toff012 ∷ []) ∷
   re 11 3 (Toff013 ∷ []) ∷
   rw 12 q13 ∷
   rw 13 q3 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 19 q3 ∷
   rw 18 q6 ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 13 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 11 q5 ∷
   rw 12 q7 ∷
   re 12 8 (Toff012 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q15 ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 10 q1 ∷
   rw⁻ 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 11 q7 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 10 3 (Toff013 ∷ []) ∷
   rw 11 q16 ∷
   rw 12 q3 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 18 q3 ∷
   rw 17 q6 ∷
   rw 16 q5 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 10 q5 ∷
   rw 11 q7 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw 8 q21 ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q6 ∷
   rw 9 q1 ∷
   rw⁻ 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw⁻ 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw⁻ 14 q2 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 10 q7 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 9 3 (Toff013 ∷ []) ∷
   rw⁻ 10 q20 ∷
   rw 11 q21 ∷
   rw 12 q3 ∷
   rw 16 q22 ∷
   rw 17 q23 ∷
   rw 18 q23 ∷
   rw 12 q24 ∷
   rw 13 q25 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 15 5 (CCZ012 ∷ []) ∷
   re 13 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 14 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   re 14 5 (CCZ012 ∷ []) ∷
   rw 14 q26 ∷
   rw 13 q3 ∷
   rw⁻ 12 q27 ∷
   rw⁻ 13 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ03)

-- pass [CCZ012] [CZ03]: 1 steps
lem-pass-CCZ012-vs-CZ03 : ⟪ (CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ03 = derive (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS23 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ []) lem-pass-CS23-vs-S0
  q31 : Eqn
  q31 = eqn (S0 ∷ Toff201 ∷ []) (Toff201 ∷ S0 ∷ []) (wn 1388 W)
  q32 : Eqn
  q32 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd23)

-- pass [S0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 = derive (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ [])
  (rw⁻ 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷ []) Eq.refl
