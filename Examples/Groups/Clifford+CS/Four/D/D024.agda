{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D024 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 56 W
  q9 : Eqn
  q9 = wE 458 W
  q10 : Eqn
  q10 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q12 : Eqn
  q12 = wE 459 W
  q13 : Eqn
  q13 = wE 151 W
  q14 : Eqn
  q14 = wE 460 W
  q15 : Eqn
  q15 = wE 43 W
  q16 : Eqn
  q16 = eqn (CX10 ∷ S3 ∷ []) (S3 ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑)))
  q17 : Eqn
  q17 = wE 461 W
  q18 : Eqn
  q18 = wE 462 W
  q19 : Eqn
  q19 = wE 463 W
  q20 : Eqn
  q20 = wE 153 W
  q21 : Eqn
  q21 = wE 464 W
  q22 : Eqn
  q22 = wE 465 W
  q23 : Eqn
  q23 = wE 466 W
  q24 : Eqn
  q24 = wE 467 W
  q25 : Eqn
  q25 = wE 468 W
  q26 : Eqn
  q26 = wE 469 W

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part0: 500 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 : ⟪ (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 = derive (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  (rw 6 q1 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q4 ∷
   rw 4 q8 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw⁻ 1 q10 ∷
   rw⁻ 2 q11 ∷
   rw 5 q1 ∷
   re 3 3 (CX30 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw 4 q1 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q5 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q6 ∷
   rw 5 q8 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q1 ∷
   rw 1 q10 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q12 ∷
   rw⁻ 0 q10 ∷
   rw 1 q13 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q1 ∷
   rw 3 q11 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q14 ∷
   rw⁻ 2 q11 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q5 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 6 q15 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 1 q16 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q7 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q15 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q1 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CZ13 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q5 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 8 q15 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 7 3 (CCZ013 ∷ []) ∷
   rw 8 q7 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q18 ∷
   rw 6 q1 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q19 ∷
   rw 5 q1 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q20 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q7 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q1 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q13 ∷
   rw 4 q7 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw 17 q7 ∷
   rw 16 q6 ∷
   rw 15 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   rw 13 q5 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q4 ∷
   rw 10 q8 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q7 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 9 q15 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   rw 9 q23 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q6 ∷
   rw 8 q1 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw⁻ 13 q5 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw 9 q8 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CZ13 ∷ []) ∷
   re 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw⁻ 12 q5 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw⁻ 14 q5 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 11 q15 ∷
   re 11 5 (CCZ012 ∷ []) ∷
   re 10 3 (CCZ013 ∷ []) ∷
   rw 11 q7 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q6 ∷
   rw 16 q7 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q5 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q4 ∷
   rw 9 q8 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 8 q24 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q6 ∷
   rw 7 q1 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw⁻ 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw⁻ 12 q5 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q6 ∷
   rw 8 q8 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CZ13 ∷ []) ∷
   rw 9 q7 ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q6 ∷
   rw 15 q7 ∷
   rw 14 q6 ∷
   rw 13 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q4 ∷
   rw 8 q8 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q25 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw 6 q1 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q5 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q6 ∷
   rw 7 q8 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw 14 q7 ∷
   rw 13 q6 ∷
   rw 12 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q4 ∷
   rw 7 q8 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q26 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q6 ∷
   rw 5 q1 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 8 q5 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw⁻ 10 q5 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw 6 q8 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw⁻ 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw⁻ 12 q5 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 9 q15 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 188 W

-- pass [CCZ012] [Z0]: 1 steps
lem-pass-CCZ012-vs-Z0 : ⟪ (CCZ012 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-Z0 = derive (CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 85 W
  q29 : Eqn
  q29 = wE 5 W
  q30 : Eqn
  q30 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q31 : Eqn
  q31 = wE 189 W
  q32 : Eqn
  q32 = wE 7 W
  q33 : Eqn
  q33 = wE 106 W
  q34 : Eqn
  q34 = wE 191 W
  q35 : Eqn
  q35 = wE 27 W
  q36 : Eqn
  q36 = wE 31 W
  q37 : Eqn
  q37 = wE 13 W
  q38 : Eqn
  q38 = eqn (CZ01 ∷ CX32 ∷ []) (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀))
  q39 : Eqn
  q39 = wE 78 W
  q40 : Eqn
  q40 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q41 : Eqn
  q41 = wE 192 W
  q42 : Eqn
  q42 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q43 : Eqn
  q43 = wE 193 W
  q44 : Eqn
  q44 = wE 89 W

-- comm CCZ012 CZ03: 53 steps
lem-comm-CCZ012-CZ03 : ⟪ (CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ03 = derive (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ [])
  (rw 0 q28 ∷
   rw 6 q29 ∷
   re 5 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q30 ∷
   rw 6 q31 ∷
   rw⁻ 5 q30 ∷
   re 6 3 (CZ13 ∷ []) ∷
   rw 4 q32 ∷
   rw 5 q33 ∷
   re 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q34 ∷
   rw 6 q30 ∷
   re 4 3 (CZ03 ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q1 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 4 q37 ∷
   rw⁻ 5 q38 ∷
   rw 6 q39 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   re 3 5 (CZ03 ∷ []) ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 2 q40 ∷
   rw 3 q41 ∷
   rw 4 q1 ∷
   re 2 3 (CZ03 ∷ []) ∷
   rw⁻ 3 q40 ∷
   rw 4 q7 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q37 ∷
   rw⁻ 3 q38 ∷
   rw 4 q39 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 1 5 (CZ03 ∷ []) ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q1 ∷
   re 0 3 (CZ03 ∷ []) ∷
   rw⁻ 1 q42 ∷
   rw 2 q7 ∷
   rw 1 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 194 W
  q46 : Eqn
  q46 = wE 175 W

-- pass [CS03] [X1 X3 TOFF013 X1 X3]: 69 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3 : ⟪ (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3 = derive (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS03 ∷ [])
  (rw 6 q1 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q4 ∷
   rw 4 q8 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q45 ∷
   rw⁻ 0 q3 ∷
   rw 1 q46 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw 2 q1 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 3 q8 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 4 q46 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q7 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 195 W

-- pass [CSd03] [X1 X3 TOFF013 X1 X3]: 69 steps
lem-pass-CSd03-vs-X1-X3-TOFF013-X1-X3 : ⟪ (CS03⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-X1-X3-TOFF013-X1-X3 = derive (CS03⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 6 q1 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 3 q4 ∷
   rw 4 q8 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q47 ∷
   rw⁻ 0 q3 ∷
   rw 1 q46 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw 2 q1 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 3 q8 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 4 q46 ∷
   rw 7 q1 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q7 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 470 W

-- pass [S0] [CSd23]: 1 steps
lem-pass-S0-vs-CSd23 : ⟪ (S0 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd23 = derive (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ [])
  (rw 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q50 : Eqn
  q50 = wE 76 W
  q51 : Eqn
  q51 = wE 471 W
  q52 : Eqn
  q52 = wE 29 W

-- pass [CSd03] [CSd23]: 15 steps
lem-pass-CSd03-vs-CSd23 : ⟪ (CS03⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CSd23 = derive (CS03⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS03⁻ ∷ [])
  (rw 2 q29 ∷
   rw⁻ 1 q49 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q30 ∷
   rw 1 q50 ∷
   rw⁻ 0 q30 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 q51 ∷
   rw 0 q49 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q30 ∷
   rw 2 q52 ∷
   rw 3 q30 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q36 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q54 : Eqn
  q54 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q55 : Eqn
  q55 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q56 : Eqn
  q56 = wE 452 W
  q57 : Eqn
  q57 = wE 453 W

-- b2g 1111R1: 5 steps
lem-b2g-1111R1 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1111R1 = derive (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  (rw 1 q53 ∷
   rw 2 q54 ∷
   rw 12 q55 ∷
   rw 3 q56 ∷
   rw 11 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 472 W

-- pass [TOFF102] [iI]: 1 steps
lem-pass-TOFF102-vs-iI : ⟪ (Toff102 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-iI = derive (Toff102 ∷ ι ∷ []) (ι ∷ Toff102 ∷ [])
  (rw 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (Toff102 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) ((S • S • S)))

-- pass [TOFF102] [Sd3]: 1 steps
lem-pass-TOFF102-vs-Sd3 : ⟪ (Toff102 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-Sd3 = derive (Toff102 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff102 ∷ [])
  (rw 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (Toff102 ∷ S3 ∷ []) (S3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (S))

-- pass [TOFF102] [S3]: 1 steps
lem-pass-TOFF102-vs-S3 : ⟪ (Toff102 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-S3 = derive (Toff102 ∷ S3 ∷ []) (S3 ∷ Toff102 ∷ [])
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (ι ∷ []) (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q62 : Eqn
  q62 = wE 473 W
  q63 : Eqn
  q63 = eqn (ι3 ∷ []) (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))

-- pass [CSd13] [iI]: 3 steps
lem-pass-CSd13-vs-iI : ⟪ (CS13⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-iI = derive (CS13⁻ ∷ ι ∷ []) (ι ∷ CS13⁻ ∷ [])
  (rw 1 q61 ∷
   rw 0 q62 ∷
   rw 0 q63 ∷ []) Eq.refl
