{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D542 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-pass-CCZ013-vs-CZ01)
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CS13-vs-CS02 ; lem-pass-CSd02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D016 W using (lem-pass-CCZ012-vs-CZ02 ; lem-pass-CS12-vs-CS13 ; lem-pass-CS12-vs-CSd13 ; lem-pass-CS12-vs-CZ02 ; lem-pass-CSd12-vs-CS13 ; lem-pass-CSd12-vs-CSd13 ; lem-pass-CSd12-vs-CZ02)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-CCZ012-vs-CS13 ; lem-pass-CCZ013-vs-CCZ012)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ012-vs-CCZ123 ; lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q5 : Eqn
  q5 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1495 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) (wn 1413 W)
  q9 : Eqn
  q9 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X2 CK20 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   rw 1 q5 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   rw 1 q8 ∷
   rw 1 q9 ∷
   rw 5 q8 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   rw 6 q5 ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q6 ∷
   rw 8 q3 ∷
   rw 9 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q11 : Eqn
  q11 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1497 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1485 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X2 CKd20 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw 1 q10 ∷
   rw⁻ 0 q3 ∷
   rw 1 q11 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q12 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   rw 1 q13 ∷
   rw 1 q14 ∷
   rw 5 q13 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 7 q3 ∷
   rw 6 q10 ∷
   rw⁻ 5 q3 ∷
   rw 6 q11 ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q12 ∷
   rw 8 q3 ∷
   rw 9 q7 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q16 : Eqn
  q16 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1499 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q18 : Eqn
  q18 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1482 W)
  q19 : Eqn
  q19 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X2 CSd20 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw 1 q15 ∷
   rw⁻ 0 q3 ∷
   rw 1 q16 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q17 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   rw 1 q18 ∷
   rw 1 q19 ∷
   rw 5 q18 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 7 q3 ∷
   rw 6 q15 ∷
   rw⁻ 5 q3 ∷
   rw 6 q16 ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q17 ∷
   rw 8 q3 ∷
   rw 9 q7 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q21 : Eqn
  q21 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q22 : Eqn
  q22 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q23 : Eqn
  q23 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q24 : Eqn
  q24 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q25 : Eqn
  q25 = eqn (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q26 : Eqn
  q26 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q27 : Eqn
  q27 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q28 : Eqn
  q28 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- pass [X1 CS10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q20 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 2 q20 ∷
   rw 3 q24 ∷
   rw 4 q20 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q23 ∷
   rw⁻ 4 q25 ∷
   rw 12 q20 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q22 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q22 ∷
   rw 11 q26 ∷
   rw 10 q22 ∷
   rw 9 q27 ∷
   rw 10 q20 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q22 ∷
   rw 9 q28 ∷
   rw 8 q22 ∷
   rw 7 q27 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1501 W)
  q30 : Eqn
  q30 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q31 : Eqn
  q31 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1502 W)

-- pass [X2 CSd21 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q16 ∷
   rw 1 q29 ∷
   rw 3 q30 ∷
   rw 7 q31 ∷
   rw 9 q16 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1503 W)
  q33 : Eqn
  q33 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q34 : Eqn
  q34 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1504 W)

-- pass [X2 CKd21 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q11 ∷
   rw 1 q32 ∷
   rw 3 q33 ∷
   rw 7 q34 ∷
   rw 9 q11 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1505 W)
  q36 : Eqn
  q36 = eqn (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q37 : Eqn
  q37 = eqn (X2 ∷ CK21 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1506 W)

-- pass [X2 CK21 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q5 ∷
   rw 1 q35 ∷
   rw 3 q36 ∷
   rw 7 q37 ∷
   rw 9 q5 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1493 W)
  q39 : Eqn
  q39 = eqn (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1507 W)
  q40 : Eqn
  q40 = eqn (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q41 : Eqn
  q41 = eqn (X2 ∷ CS12 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1508 W)

-- pass [X2 CS21 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q38 ∷
   rw 1 q39 ∷
   rw 3 q40 ∷
   rw 7 q41 ∷
   rw 9 q38 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (wn 1347 W)
  q43 : Eqn
  q43 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q44 : Eqn
  q44 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q45 : Eqn
  q45 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q46 : Eqn
  q46 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q47 : Eqn
  q47 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q48 : Eqn
  q48 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q49 : Eqn
  q49 = eqn (K1⁻ ∷ K1 ∷ []) [] (wn 1509 W)
  q50 : Eqn
  q50 = eqn (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CCZ012)
  q51 : Eqn
  q51 = eqn [] (K1⁻ ∷ K1 ∷ []) (wn 1510 W)
  q52 : Eqn
  q52 = eqn (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) (wn 1450 W)

-- pass [TOFF103] [TOFF102]: 111 steps
lem-pass-TOFF103-vs-TOFF102 : ⟪ (Toff103 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-TOFF102 = derive (Toff103 ∷ Toff102 ∷ []) (Toff102 ∷ Toff103 ∷ [])
  (rw 1 q42 ∷
   rw 1 q20 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q43 ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q44 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q44 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q43 ∷
   rw⁻ 7 q45 ∷
   rw 8 q22 ∷
   rw 7 q45 ∷
   rw 6 q43 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw 4 q44 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw 2 q44 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw 0 q43 ∷
   rw 1 q46 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q42 ∷
   rw⁻ 0 q43 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q44 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q44 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q20 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw⁻ 3 q44 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   rw 2 q47 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q48 ∷
   rw 3 q22 ∷
   rw 2 q49 ∷
   rw 1 q50 ∷
   rw 2 q51 ∷
   rw 0 q52 ∷
   rw 4 q20 ∷
   rw 3 q48 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q44 ∷
   rw 6 q20 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q44 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q44 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   rw 3 q44 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   rw 3 q47 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q43 ∷
   rw 2 q52 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q43 ∷
   rw 4 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q44 ∷
   rw 6 q20 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q44 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q43 ∷
   rw⁻ 8 q45 ∷
   rw 1 q20 ∷
   rw⁻ 2 q43 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw⁻ 4 q44 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw⁻ 6 q44 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw⁻ 8 q43 ∷
   rw⁻ 9 q45 ∷
   rw 2 q46 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q22 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ []) lem-pass-CCZ012-vs-CCZ123

-- pass [CCZ123] [CCZ012]: 1 steps
lem-pass-CCZ123-vs-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CCZ012 = derive (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (CS12 ∷ Toff102 ∷ []) (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wn 1511 W)
  q55 : Eqn
  q55 = eqn (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13)
  q56 : Eqn
  q56 = eqn (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS13)
  q57 : Eqn
  q57 = eqn (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ []) lem-pass-CS13-vs-CS02
  q58 : Eqn
  q58 = eqn (CCZ012 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (wn 1512 W)
  q59 : Eqn
  q59 = eqn (CS02 ∷ Toff102 ∷ []) (Toff102 ∷ CS02 ∷ []) (wn 1351 W)
  q60 : Eqn
  q60 = eqn (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02)
  q61 : Eqn
  q61 = eqn (CS12 ∷ CZ02 ∷ []) (CZ02 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CZ02)
  q62 : Eqn
  q62 = eqn (CS02 ∷ CS02 ∷ CZ02 ∷ []) [] (wn 1513 W)
  q63 : Eqn
  q63 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q64 : Eqn
  q64 = eqn (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd13)

-- pass [CS12] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 = derive (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ [])
  (rw 0 q54 ∷
   rw 3 q55 ∷
   rw 2 q56 ∷
   rw⁻ 1 q57 ∷
   rw 4 q58 ∷
   rw 3 q54 ∷
   rw 2 q59 ∷
   rw 6 q60 ∷
   rw 5 q61 ∷
   rw 3 q62 ∷
   rw 4 q63 ∷
   rw 3 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CS12⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wn 1514 W)
  q66 : Eqn
  q66 = eqn (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CS13)
  q67 : Eqn
  q67 = eqn (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13)
  q68 : Eqn
  q68 = eqn (CS02⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ []) (wn 1352 W)
  q69 : Eqn
  q69 = eqn (CS12⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CZ02)
  q70 : Eqn
  q70 = eqn (CS02⁻ ∷ CS02⁻ ∷ CZ02 ∷ []) [] (wn 1515 W)
  q71 : Eqn
  q71 = eqn (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CSd13)

-- pass [CSd12] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 = derive (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ [])
  (rw 0 q65 ∷
   rw 3 q55 ∷
   rw 2 q66 ∷
   rw 1 q67 ∷
   rw 4 q58 ∷
   rw 3 q65 ∷
   rw 2 q68 ∷
   rw 6 q60 ∷
   rw 5 q69 ∷
   rw 3 q70 ∷
   rw 4 q63 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (X2 ∷ Toff102 ∷ X2 ∷ []) (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (wn 1516 W)
  q73 : Eqn
  q73 = eqn (CCZ013 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CZ01)
  q74 : Eqn
  q74 = eqn (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) (wn 1517 W)

-- pass [TOFF103] [X2 TOFF102 X2]: 112 steps
lem-pass-TOFF103-vs-X2-TOFF102-X2 : ⟪ (Toff103 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-X2-TOFF102-X2 = derive (Toff103 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff103 ∷ [])
  (rw 1 q72 ∷
   rw 1 q20 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q43 ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q44 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q44 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q43 ∷
   rw⁻ 7 q45 ∷
   rw 8 q22 ∷
   rw 7 q45 ∷
   rw 6 q43 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw 4 q44 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw 2 q44 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q22 ∷
   rw 0 q43 ∷
   rw 1 q46 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q42 ∷
   rw⁻ 0 q43 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q44 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q44 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q20 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q22 ∷
   rw⁻ 3 q44 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   rw 2 q47 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q48 ∷
   rw 3 q22 ∷
   rw 2 q49 ∷
   rw 1 q73 ∷
   rw 2 q50 ∷
   rw 3 q51 ∷
   rw 0 q74 ∷
   rw 6 q20 ∷
   rw 5 q48 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q20 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q44 ∷
   rw 8 q20 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q44 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q44 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q44 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q47 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q43 ∷
   rw 4 q52 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q43 ∷
   rw 6 q20 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q44 ∷
   rw 8 q20 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q44 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q43 ∷
   rw⁻ 10 q45 ∷
   rw 3 q20 ∷
   rw⁻ 4 q43 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   rw⁻ 6 q44 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   rw⁻ 8 q44 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q22 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q45 ∷
   rw 4 q46 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   rw 4 q22 ∷ []) Eq.refl
