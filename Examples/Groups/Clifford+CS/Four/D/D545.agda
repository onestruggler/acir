{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD545 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D545 (W : Ws) (Sᴰ : SD545) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ013-vs-CSd13 : St 175
  lem-pass-CCZ013-vs-CSd13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ013-vs-CZ13 : St 58
  lem-pass-CCZ013-vs-CZ13 = pickᴰ 1 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CCZ012-vs-CSd03 : St 830
  lem-pass-CCZ012-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CS03-vs-S0 : St 918
  lem-pass-CS03-vs-S0 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 914
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 5 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 916
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 6 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 917
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 7 Sᴰ
  lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 : St 919
  lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q7 : Eqn
  q7 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q8 : Eqn
  q8 = eqn (S2⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S2⁻ ∷ []) (wn 1384 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q10 : Eqn
  q10 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q11 : Eqn
  q11 = eqn (S2 ∷ Toff012 ∷ []) (Toff012 ∷ S2 ∷ []) (wn 1385 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q13 : Eqn
  q13 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q15 : Eqn
  q15 = eqn (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 1386 W)
  q16 : Eqn
  q16 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q18 : Eqn
  q18 = eqn (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CSd13)
  q19 : Eqn
  q19 = eqn (CCZ013 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CZ13)
  q20 : Eqn
  q20 = eqn (S3 ∷ S3⁻ ∷ []) [] (wn 154 W)
  q21 : Eqn
  q21 = eqn (CS13 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ []) [] (wn 1387 W)
  q22 : Eqn
  q22 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q23 : Eqn
  q23 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q24 : Eqn
  q24 = eqn (CS03 ∷ S0 ∷ []) (S0 ∷ CS03 ∷ []) (lem-pass-CS03-vs-S0)
  q25 : Eqn
  q25 = eqn (CS02⁻ ∷ CS03 ∷ []) (CS03 ∷ CS02⁻ ∷ []) lem-pass-CSd02-vs-CS03
  q26 : Eqn
  q26 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q27 : Eqn
  q27 = eqn (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) (wn 458 W)
  q28 : Eqn
  q28 = eqn (CS02 ∷ X0 ∷ []) (X0 ∷ S2 ∷ CS02⁻ ∷ []) (wn 459 W)
  q29 : Eqn
  q29 = eqn (CS02⁻ ∷ CX10 ∷ []) (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wn 460 W)
  q30 : Eqn
  q30 = eqn (CX10 ∷ S3 ∷ []) (S3 ∷ CX10 ∷ []) (low-comm (CX₁₀) ((S ↑)))
  q31 : Eqn
  q31 = eqn (CCZ012 ∷ CX20 ∷ []) (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) (wn 461 W)
  q32 : Eqn
  q32 = eqn (CS12⁻ ∷ CX20 ∷ []) (CX20 ∷ CS12⁻ ∷ []) (wn 462 W)
  q33 : Eqn
  q33 = eqn (CS02⁻ ∷ CX20 ∷ []) (CX20 ∷ S2⁻ ∷ CS02 ∷ []) (wn 463 W)
  q34 : Eqn
  q34 = eqn (S2 ∷ CX20 ∷ []) (CX20 ∷ S2 ∷ []) (wn 465 W)
  q35 : Eqn
  q35 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wn 466 W)

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part1: 500 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 : ⟪ (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 = derive (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ [])
  (re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q1 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q1 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q1 ∷
   rw 6 q6 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q8 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q1 ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 4 q2 ∷
   rw⁻ 5 q1 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q1 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q1 ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q1 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q1 ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 3 q2 ∷
   rw⁻ 4 q1 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q12 ∷
   rw 5 q5 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q1 ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q1 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw⁻ 0 q16 ∷
   rw 1 q17 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q1 ∷
   rw 5 q2 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q1 ∷
   rw⁻ 9 q4 ∷
   rw 2 q2 ∷
   rw⁻ 3 q1 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 4 q17 ∷
   rw 5 q5 ∷
   rw 9 q18 ∷
   rw 10 q19 ∷
   rw 11 q19 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q5 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 8 q22 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 7 q22 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q5 ∷
   rw 5 q24 ∷
   rw⁻ 6 q25 ∷
   rw 13 q2 ∷
   rw 12 q26 ∷
   rw 11 q16 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q1 ∷
   rw 13 q2 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q2 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q2 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q1 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q26 ∷
   rw 8 q16 ∷
   rw 9 q27 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q13 ∷
   rw 12 q2 ∷
   re 10 3 (CX30 ∷ []) ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 11 q1 ∷
   rw 14 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw⁻ 17 q1 ∷
   rw⁻ 18 q4 ∷
   rw 11 q2 ∷
   rw⁻ 12 q1 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 19 q4 ∷
   rw 12 q6 ∷
   re 12 8 (Toff012 ∷ []) ∷
   re 11 3 (Toff013 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 8 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 8 q28 ∷
   rw⁻ 7 q14 ∷
   rw 8 q12 ∷
   rw 11 q2 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q2 ∷
   rw 10 q13 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 10 q29 ∷
   rw⁻ 9 q13 ∷
   rw 12 q2 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 13 q2 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   re 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 13 q22 ∷
   re 13 5 (CCZ012 ∷ []) ∷
   re 12 3 (CCZ013 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 8 q30 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 12 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q3 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw 13 q22 ∷
   re 13 5 (CCZ012 ∷ []) ∷
   rw 13 q31 ∷
   rw 14 q2 ∷
   re 12 3 (CX30 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CZ13 ∷ []) ∷
   re 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 16 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 20 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw⁻ 18 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 15 q22 ∷
   re 15 5 (CCZ012 ∷ []) ∷
   re 14 3 (CCZ013 ∷ []) ∷
   rw 15 q5 ∷
   rw 13 q2 ∷
   re 12 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 12 q32 ∷
   rw 13 q2 ∷
   re 11 3 (CX30 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 13 q5 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q33 ∷
   rw 12 q2 ∷
   re 10 3 (CX30 ∷ []) ∷
   rw 11 q9 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q10 ∷
   rw 10 q34 ∷
   rw 11 q2 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q5 ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 17 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw 19 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q2 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw⁻ 22 q1 ∷
   rw⁻ 23 q4 ∷
   rw 24 q5 ∷
   rw 23 q4 ∷
   rw 22 q1 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 20 q3 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q1 ∷
   rw 17 q6 ∷
   re 17 8 (Toff012 ∷ []) ∷
   re 15 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 16 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q2 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 16 q22 ∷
   re 16 5 (CCZ012 ∷ []) ∷
   rw 16 q35 ∷
   re 16 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 15 q1 ∷
   rw 18 q2 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 20 q2 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw⁻ 21 q1 ∷
   rw⁻ 22 q4 ∷
   rw 15 q2 ∷
   rw⁻ 16 q1 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw⁻ 18 q3 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw⁻ 20 q3 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw⁻ 22 q1 ∷
   rw⁻ 23 q4 ∷
   rw 16 q6 ∷
   re 16 8 (Toff012 ∷ []) ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [S0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (wn 1535 W)
  q38 : Eqn
  q38 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q40 : Eqn
  q40 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q42 : Eqn
  q42 = eqn (K2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K2⁻ ∷ []) (wn 1549 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q45 : Eqn
  q45 = eqn (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd03)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q47 : Eqn
  q47 = eqn (K2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K2 ∷ []) (wn 1550 W)
  q48 : Eqn
  q48 = eqn (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wn 1538 W)

-- pass [TOFF201] [CSd03]: 33 steps
lem-pass-TOFF201-vs-CSd03 : ⟪ (Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CSd03 = derive (Toff201 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff201 ∷ [])
  (rw 0 q37 ∷
   rw 4 q38 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q39 ∷
   rw 4 q40 ∷
   rw⁻ 3 q39 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q41 ∷
   rw 3 q42 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q39 ∷
   rw 3 q43 ∷
   rw 4 q39 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q41 ∷
   rw 4 q44 ∷
   rw 1 q45 ∷
   rw 2 q38 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q39 ∷
   rw 2 q40 ∷
   rw⁻ 1 q39 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q46 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q39 ∷
   rw 1 q43 ∷
   rw 2 q39 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q46 ∷
   rw 2 q44 ∷
   rw 1 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q50 : Eqn
  q50 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q52 : Eqn
  q52 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1551 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q54 : Eqn
  q54 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q55 : Eqn
  q55 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q56 : Eqn
  q56 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1552 W)
  q57 : Eqn
  q57 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q58 : Eqn
  q58 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q59 : Eqn
  q59 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1553 W)
  q60 : Eqn
  q60 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q61 : Eqn
  q61 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q62 : Eqn
  q62 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1554 W)

-- pass [X2 CSd20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 43 steps
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 5 q38 ∷
   rw⁻ 4 q49 ∷
   rw 3 q50 ∷
   rw⁻ 2 q51 ∷
   rw 1 q40 ∷
   rw⁻ 0 q51 ∷
   rw 1 q52 ∷
   rw 0 q53 ∷
   rw 1 q49 ∷
   rw 2 q51 ∷
   rw 3 q54 ∷
   rw 4 q51 ∷
   rw 5 q51 ∷
   rw 6 q55 ∷
   rw 7 q51 ∷
   rw 8 q51 ∷
   rw 9 q55 ∷
   rw 10 q51 ∷
   rw 11 q44 ∷
   rw 2 q56 ∷
   rw 12 q57 ∷
   rw 9 q57 ∷
   rw 6 q58 ∷
   rw 10 q59 ∷
   rw 25 q38 ∷
   rw⁻ 24 q49 ∷
   rw 23 q50 ∷
   rw⁻ 22 q51 ∷
   rw 21 q60 ∷
   rw⁻ 20 q51 ∷
   rw⁻ 19 q51 ∷
   rw 18 q60 ∷
   rw⁻ 17 q51 ∷
   rw⁻ 16 q51 ∷
   rw 15 q61 ∷
   rw⁻ 14 q51 ∷
   rw 15 q62 ∷
   rw 14 q53 ∷
   rw 15 q49 ∷
   rw 16 q51 ∷
   rw 17 q43 ∷
   rw 18 q51 ∷
   rw 19 q44 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q64 : Eqn
  q64 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1555 W)
  q65 : Eqn
  q65 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1556 W)
  q66 : Eqn
  q66 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q67 : Eqn
  q67 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1557 W)
  q68 : Eqn
  q68 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1558 W)
  q69 : Eqn
  q69 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)

-- pass [X2 CKd20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 57 steps
lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 5 q38 ∷
   rw⁻ 4 q49 ∷
   rw 3 q50 ∷
   rw⁻ 2 q51 ∷
   rw 1 q63 ∷
   rw⁻ 0 q51 ∷
   rw 1 q64 ∷
   rw 0 q53 ∷
   rw 1 q49 ∷
   rw 2 q51 ∷
   rw 3 q54 ∷
   rw 4 q51 ∷
   rw 5 q51 ∷
   rw 6 q55 ∷
   rw 7 q51 ∷
   rw 8 q51 ∷
   rw 9 q43 ∷
   rw 10 q51 ∷
   rw 11 q51 ∷
   rw 12 q55 ∷
   rw 13 q51 ∷
   rw 14 q51 ∷
   rw 15 q54 ∷
   rw 16 q51 ∷
   rw 17 q44 ∷
   rw 2 q65 ∷
   rw 18 q58 ∷
   rw 15 q57 ∷
   rw 12 q66 ∷
   rw 9 q57 ∷
   rw 6 q58 ∷
   rw 10 q67 ∷
   rw 31 q38 ∷
   rw⁻ 30 q49 ∷
   rw 29 q50 ∷
   rw⁻ 28 q51 ∷
   rw 27 q61 ∷
   rw⁻ 26 q51 ∷
   rw⁻ 25 q51 ∷
   rw 24 q60 ∷
   rw⁻ 23 q51 ∷
   rw⁻ 22 q51 ∷
   rw 21 q40 ∷
   rw⁻ 20 q51 ∷
   rw⁻ 19 q51 ∷
   rw 18 q60 ∷
   rw⁻ 17 q51 ∷
   rw⁻ 16 q51 ∷
   rw 15 q61 ∷
   rw⁻ 14 q51 ∷
   rw 15 q68 ∷
   rw 14 q53 ∷
   rw 15 q49 ∷
   rw 16 q51 ∷
   rw 17 q69 ∷
   rw 18 q51 ∷
   rw 19 q44 ∷ []) Eq.refl
