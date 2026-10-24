{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD539 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D539 (W : Ws) (Sᴰ : SD539) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 1357 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 45 W
  q5 : Eqn
  q5 = wE 231 W
  q6 : Eqn
  q6 = sE 851 lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q7 : Eqn
  q7 = wE 1358 W
  q8 : Eqn
  q8 = wE 227 W
  q9 : Eqn
  q9 = wE 1342 W

-- pass [X2 CS20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丧丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丧丘中九丮九") (ℓ "中九丮九丘丧丘")
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 2 q1 ∷
   rw 3 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 4 q6 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q3 ∷
   rw 11 q7 ∷
   rw 10 q3 ∷
   rw 9 q8 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 9 q9 ∷
   rw 8 q3 ∷
   rw 7 q8 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1462 W
  q11 : Eqn
  q11 = sE 852 lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q12 : Eqn
  q12 = wE 1463 W

-- pass [CS20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丧丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丧") ⟫ʷ
lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丧丘习丽习举丘") (ℓ "丘习丽习举丘丧")
  (rw 0 q10 ∷
   rw 1 q11 ∷
   rw 5 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1407 W
  q14 : Eqn
  q14 = sE 849 lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q15 : Eqn
  q15 = wE 1408 W

-- pass [CK20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "乄丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘乄") ⟫ʷ
lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "乄丘习丽习举丘") (ℓ "丘习丽习举丘乄")
  (rw 0 q13 ∷
   rw 1 q14 ∷
   rw 5 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1464 W
  q17 : Eqn
  q17 = sE 850 lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q18 : Eqn
  q18 = wE 1465 W

-- pass [CKd20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "久丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘久") ⟫ʷ
lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "久丘习丽习举丘") (ℓ "丘习丽习举丘久")
  (rw 0 q16 ∷
   rw 1 q17 ∷
   rw 5 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1466 W
  q20 : Eqn
  q20 = sE 853 lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q21 : Eqn
  q21 = wE 1467 W

-- pass [CSd20] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丨丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丨") ⟫ʷ
lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丨丘习丽习举丘") (ℓ "丘习丽习举丘丨")
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 5 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 824 lem-pass-CCZ023-vs-CCZ012

-- pass [CCZ012] [CCZ023]: 1 steps
lem-pass-CCZ012-vs-CCZ023 : ⟪ (ℓ "乙乛") ⟫ʷ ≈ ⟪ (ℓ "乛乙") ⟫ʷ
lem-pass-CCZ012-vs-CCZ023 = derive (ℓ "乙乛") (ℓ "乛乙")
  (rw⁻ 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q26 : Eqn
  q26 = wE 56 W
  q27 : Eqn
  q27 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 1443 W
  q29 : Eqn
  q29 = wE 43 W
  q30 : Eqn
  q30 = sE 826 lem-pass-CCZ013-vs-CS02
  q31 : Eqn
  q31 = sE 27 lem-pass-CS13-vs-CS02
  q32 : Eqn
  q32 = sE 847 lem-pass-S0-vs-CS02
  q33 : Eqn
  q33 = wE 466 W
  q34 : Eqn
  q34 = wE 90 W
  q35 : Eqn
  q35 = sE 61 lem-pass-CCZ013-vs-CS13
  q36 : Eqn
  q36 = sE 58 lem-pass-CCZ013-vs-CZ13
  q37 : Eqn
  q37 = wE 1365 W
  q38 : Eqn
  q38 = wE 32 W
  q39 : Eqn
  q39 = sE 848 lem-pass-S0-vs-CSd02

-- pass [S0] [TOFF013 CS02 TOFF013 CSd02]: 378 steps
lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丈乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丈") ⟫ʷ
lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丈乞丧乞丨") (ℓ "乞丧乞丨丈")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q23 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q24 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q23 ∷
   rw⁻ 8 q25 ∷
   rw 9 q3 ∷
   rw 8 q25 ∷
   rw 7 q23 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw 3 q24 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 1 q23 ∷
   rw 2 q26 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q23 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q23 ∷
   rw⁻ 7 q25 ∷
   rw 0 q1 ∷
   rw⁻ 1 q23 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q23 ∷
   rw⁻ 8 q25 ∷
   rw 1 q26 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q27 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 4 q29 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q3 ∷
   rw 3 q30 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q23 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q24 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 13 q3 ∷
   rw 12 q25 ∷
   rw 11 q23 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q3 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 5 q23 ∷
   rw 6 q26 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 5 q29 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q33 ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q23 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 4 q1 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q25 ∷
   rw 5 q26 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丿") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q24 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q24 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q3 ∷
   rw⁻ 10 q24 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q3 ∷
   rw 7 q29 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q3 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q23 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 12 q3 ∷
   rw 11 q25 ∷
   rw 10 q23 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q3 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q3 ∷
   rw 6 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 4 q23 ∷
   rw 5 q26 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 4 q34 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q23 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 3 q1 ∷
   rw⁻ 4 q23 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q24 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q24 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q25 ∷
   rw 4 q26 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q3 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q23 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 11 q3 ∷
   rw 10 q25 ∷
   rw 9 q23 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 3 q23 ∷
   rw 4 q26 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q27 ∷
   rw 3 q28 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q23 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q24 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q25 ∷
   rw 2 q1 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q25 ∷
   rw 3 q26 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q27 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q24 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw⁻ 9 q24 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 6 q29 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw 6 q3 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 4 q37 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q3 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q3 ∷
   rw 6 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 6 q29 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 5 q29 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q38 ∷
   rw 4 q3 ∷
   rw 3 q39 ∷ []) Eq.refl
