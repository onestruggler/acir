{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD539 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D539 (W : Ws) (Sᴰ : SD539) where

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
  lem-pass-CCZ013-vs-CZ13 : St 58
  lem-pass-CCZ013-vs-CZ13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ013-vs-CS13 : St 61
  lem-pass-CCZ013-vs-CS13 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 2 Sᴰ
  lem-pass-S0-vs-CS02 : St 847
  lem-pass-S0-vs-CS02 = pickᴰ 3 Sᴰ
  lem-pass-S0-vs-CSd02 : St 848
  lem-pass-S0-vs-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-CCZ013-vs-CS02 : St 826
  lem-pass-CCZ013-vs-CS02 = pickᴰ 5 Sᴰ
  lem-pass-CCZ023-vs-CCZ012 : St 824
  lem-pass-CCZ023-vs-CCZ012 = pickᴰ 6 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 849
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 850
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 852
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 853
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q5 : Eqn
  q5 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q6 : Eqn
  q6 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q7 : Eqn
  q7 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q8 : Eqn
  q8 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- pass [X2 CS20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 2 q1 ∷
   rw 3 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 4 q6 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q7 ∷
   rw 10 q3 ∷
   rw 9 q8 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 9 q9 ∷
   rw 8 q3 ∷
   rw 7 q8 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q11 : Eqn
  q11 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q12 : Eqn
  q12 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ [])
  (rw 0 q10 ∷
   rw 1 q11 ∷
   rw 5 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q15 : Eqn
  q15 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ [])
  (rw 0 q13 ∷
   rw 1 q14 ∷
   rw 5 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q17 : Eqn
  q17 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q18 : Eqn
  q18 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ [])
  (rw 0 q16 ∷
   rw 1 q17 ∷
   rw 5 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1466 W)
  q20 : Eqn
  q20 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q21 : Eqn
  q21 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) (wn 1467 W)

-- pass [CSd20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ [])
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 5 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ []) lem-pass-CCZ023-vs-CCZ012

-- pass [CCZ012] [CCZ023]: 1 steps
lem-pass-CCZ012-vs-CCZ023 : ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CCZ023 = derive (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ [])
  (rw⁻ 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q24 : Eqn
  q24 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q27 : Eqn
  q27 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q28 : Eqn
  q28 = eqn (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (wn 1443 W)
  q29 : Eqn
  q29 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q30 : Eqn
  q30 = eqn (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CS02)
  q31 : Eqn
  q31 = eqn (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS02)
  q32 : Eqn
  q32 = eqn (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ []) (lem-pass-S0-vs-CS02)
  q33 : Eqn
  q33 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wn 466 W)
  q34 : Eqn
  q34 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wn 90 W)
  q35 : Eqn
  q35 = eqn (CCZ013 ∷ CS13 ∷ []) (CS13 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CS13)
  q36 : Eqn
  q36 = eqn (CCZ013 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CZ13)
  q37 : Eqn
  q37 = eqn (CS13 ∷ CS13 ∷ CZ13 ∷ []) [] (wn 1365 W)
  q38 : Eqn
  q38 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q39 : Eqn
  q39 = eqn (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd02)

-- pass [S0] [TOFF013 CS02 TOFF013 CSd02]: 378 steps
lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (S0 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 = derive (S0 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ S0 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q23 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q23 ∷
   rw⁻ 8 q25 ∷
   rw 9 q3 ∷
   rw 8 q25 ∷
   rw 7 q23 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 3 q24 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 1 q23 ∷
   rw 2 q26 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q23 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q23 ∷
   rw⁻ 7 q25 ∷
   rw 0 q1 ∷
   rw⁻ 1 q23 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q23 ∷
   rw⁻ 8 q25 ∷
   rw 1 q26 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q27 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 4 q29 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q30 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q23 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 13 q3 ∷
   rw 12 q25 ∷
   rw 11 q23 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 9 q24 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q23 ∷
   rw 6 q26 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q29 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 5 q33 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q23 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 4 q1 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 5 q26 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CZ13 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q24 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 10 q24 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 7 q29 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   rw 7 q3 ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q23 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 12 q3 ∷
   rw 11 q25 ∷
   rw 10 q23 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 8 q24 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 4 q23 ∷
   rw 5 q26 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q34 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q23 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 3 q1 ∷
   rw⁻ 4 q23 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw⁻ 6 q24 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q24 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 4 q26 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q23 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 11 q3 ∷
   rw 10 q25 ∷
   rw 9 q23 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 3 q23 ∷
   rw 4 q26 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q27 ∷
   rw 3 q28 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q23 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q25 ∷
   rw 2 q1 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 3 q26 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q27 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 6 q29 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 4 q37 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 8 q24 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 6 q29 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q29 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 5 q38 ∷
   rw 4 q3 ∷
   rw 3 q39 ∷ []) Eq.refl
