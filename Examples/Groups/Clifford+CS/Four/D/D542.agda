{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD542 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D542 (W : Ws) (Sᴰ : SD542) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ013-vs-CZ01 : St 815
  lem-pass-CCZ013-vs-CZ01 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 1 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-CCZ012-vs-CZ02 : St 872
  lem-pass-CCZ012-vs-CZ02 = pickᴰ 3 Sᴰ
  lem-pass-CS12-vs-CS13 : St 873
  lem-pass-CS12-vs-CS13 = pickᴰ 4 Sᴰ
  lem-pass-CS12-vs-CSd13 : St 874
  lem-pass-CS12-vs-CSd13 = pickᴰ 5 Sᴰ
  lem-pass-CS12-vs-CZ02 : St 875
  lem-pass-CS12-vs-CZ02 = pickᴰ 6 Sᴰ
  lem-pass-CSd12-vs-CS13 : St 876
  lem-pass-CSd12-vs-CS13 = pickᴰ 7 Sᴰ
  lem-pass-CSd12-vs-CSd13 : St 877
  lem-pass-CSd12-vs-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-CSd12-vs-CZ02 : St 878
  lem-pass-CSd12-vs-CZ02 = pickᴰ 9 Sᴰ
  lem-pass-CCZ012-vs-CS13 : St 829
  lem-pass-CCZ012-vs-CS13 = pickᴰ 10 Sᴰ
  lem-pass-CCZ013-vs-CCZ012 : St 823
  lem-pass-CCZ013-vs-CCZ012 = pickᴰ 11 Sᴰ
  lem-pass-CCZ012-vs-CCZ123 : St 846
  lem-pass-CCZ012-vs-CCZ123 = pickᴰ 12 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 849
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 850
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 16 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 868
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 18 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 853
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 19 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 871
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 20 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 1495 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1413 W
  q9 : Eqn
  q9 = sE 849 lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13

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
  q10 = wE 137 W
  q11 : Eqn
  q11 = wE 1497 W
  q12 : Eqn
  q12 = wE 139 W
  q13 : Eqn
  q13 = wE 1485 W
  q14 : Eqn
  q14 = sE 850 lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

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
  q15 = wE 76 W
  q16 : Eqn
  q16 = wE 1499 W
  q17 : Eqn
  q17 = wE 29 W
  q18 : Eqn
  q18 = wE 1482 W
  q19 : Eqn
  q19 = sE 853 lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

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
  q20 = wE 1 W
  q21 : Eqn
  q21 = wE 1357 W
  q22 : Eqn
  q22 = wE 3 W
  q23 : Eqn
  q23 = wE 45 W
  q24 : Eqn
  q24 = wE 231 W
  q25 : Eqn
  q25 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q26 : Eqn
  q26 = wE 1358 W
  q27 : Eqn
  q27 = wE 227 W
  q28 : Eqn
  q28 = wE 1342 W

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
  q29 = wE 1501 W
  q30 : Eqn
  q30 = sE 871 lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q31 : Eqn
  q31 = wE 1502 W

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
  q32 = wE 1503 W
  q33 : Eqn
  q33 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q34 : Eqn
  q34 = wE 1504 W

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
  q35 = wE 1505 W
  q36 : Eqn
  q36 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q37 : Eqn
  q37 = wE 1506 W

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
  q38 = wE 1493 W
  q39 : Eqn
  q39 = wE 1507 W
  q40 : Eqn
  q40 = sE 868 lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q41 : Eqn
  q41 = wE 1508 W

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
  q42 = wE 1347 W
  q43 : Eqn
  q43 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q44 : Eqn
  q44 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q45 : Eqn
  q45 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q46 : Eqn
  q46 = wE 196 W
  q47 : Eqn
  q47 = wE 43 W
  q48 : Eqn
  q48 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q49 : Eqn
  q49 = wE 1509 W
  q50 : Eqn
  q50 = sE 823 lem-pass-CCZ013-vs-CCZ012
  q51 : Eqn
  q51 = wE 1510 W
  q52 : Eqn
  q52 = wE 1450 W

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
  q53 = sE 846 lem-pass-CCZ012-vs-CCZ123

-- pass [CCZ123] [CCZ012]: 1 steps
lem-pass-CCZ123-vs-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CCZ012 = derive (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 1511 W
  q55 : Eqn
  q55 = sE 829 lem-pass-CCZ012-vs-CS13
  q56 : Eqn
  q56 = sE 873 lem-pass-CS12-vs-CS13
  q57 : Eqn
  q57 = sE 27 lem-pass-CS13-vs-CS02
  q58 : Eqn
  q58 = wE 1512 W
  q59 : Eqn
  q59 = wE 1351 W
  q60 : Eqn
  q60 = sE 872 lem-pass-CCZ012-vs-CZ02
  q61 : Eqn
  q61 = sE 875 lem-pass-CS12-vs-CZ02
  q62 : Eqn
  q62 = wE 1513 W
  q63 : Eqn
  q63 = wE 32 W
  q64 : Eqn
  q64 = sE 874 lem-pass-CS12-vs-CSd13

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
  q65 = wE 1514 W
  q66 : Eqn
  q66 = sE 876 lem-pass-CSd12-vs-CS13
  q67 : Eqn
  q67 = sE 28 lem-pass-CSd02-vs-CS13
  q68 : Eqn
  q68 = wE 1352 W
  q69 : Eqn
  q69 = sE 878 lem-pass-CSd12-vs-CZ02
  q70 : Eqn
  q70 = wE 1515 W
  q71 : Eqn
  q71 = sE 877 lem-pass-CSd12-vs-CSd13

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
  q72 = wE 1516 W
  q73 : Eqn
  q73 = sE 815 lem-pass-CCZ013-vs-CZ01
  q74 : Eqn
  q74 = wE 1517 W

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
