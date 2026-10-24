{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D051 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 546 W
  q8 : Eqn
  q8 = wE 175 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 CKd31 X3]: 85 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乕丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乕丞") (ℓ "丞乕丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乕") ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乔") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乔") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乐") ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乐") ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (ℓ "两丞") (ℓ "丞两") (low-comm (CK₀₁) ((X ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "两乘") (ℓ "乘两") (low-comm (CK₀₁) ((S ↑ • CK₁₀)))
  q11 : Eqn
  q11 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q16 : Eqn
  q16 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 6 W
  q18 : Eqn
  q18 = wE 547 W
  q19 : Eqn
  q19 = wE 39 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丈乘") (ℓ "乘丈") (low₁-comm (S) (((S ↑ • CK₁₀) ↑)))
  q23 : Eqn
  q23 = wE 548 W
  q24 : Eqn
  q24 = wE 549 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 CKd32 X3]: 107 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乘丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乘丞") (ℓ "丞乘丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 28 q9 ∷
   rw 29 q10 ∷
   rw 30 q9 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q9 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q11 ∷
   rw 24 q12 ∷
   rw 25 q11 ∷
   rw 26 q13 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q14 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw⁻ 24 q16 ∷
   rw 23 q17 ∷
   rw⁻ 22 q16 ∷
   re 23 3 (ℓ "乓") ∷
   rw 23 q18 ∷
   rw 22 q14 ∷
   rw 23 q15 ∷
   rw 24 q14 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q16 ∷
   rw 26 q19 ∷
   rw 27 q16 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q20 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 17 q11 ∷
   rw 18 q12 ∷
   rw 19 q11 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q11 ∷
   rw 15 q21 ∷
   rw 16 q22 ∷
   rw 17 q21 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q9 ∷
   rw 13 q11 ∷
   rw 14 q12 ∷
   rw 15 q11 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q11 ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q9 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 10 q13 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q16 ∷
   rw 7 q17 ∷
   rw⁻ 6 q16 ∷
   re 7 3 (ℓ "乓") ∷
   rw 7 q18 ∷
   rw 6 q14 ∷
   rw 7 q15 ∷
   rw 8 q14 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q16 ∷
   rw 10 q19 ∷
   rw 11 q16 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q20 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = wE 27 W
  q29 : Eqn
  q29 = wE 7 W
  q30 : Eqn
  q30 = wE 74 W
  q31 : Eqn
  q31 = wE 26 W
  q32 : Eqn
  q32 = wE 75 W
  q33 : Eqn
  q33 = wE 29 W
  q34 : Eqn
  q34 = wE 550 W
  q35 : Eqn
  q35 = wE 107 W
  q36 : Eqn
  q36 = eqn (ℓ "丳之") (ℓ "之丳") (low-comm (CX₁₀) (CZ))
  q37 : Eqn
  q37 = wE 108 W
  q38 : Eqn
  q38 = wE 551 W
  q39 : Eqn
  q39 = wE 552 W
  q40 : Eqn
  q40 = wE 76 W
  q41 : Eqn
  q41 = wE 81 W
  q42 : Eqn
  q42 = wE 24 W
  q43 : Eqn
  q43 = wE 25 W

-- comm CCZ023 CZ12: 99 steps
lem-comm-CCZ023-CZ12 : ⟪ (ℓ "乛丸") ⟫ʷ ≈ ⟪ (ℓ "丸乛") ⟫ʷ
lem-comm-CCZ023-CZ12 = derive (ℓ "乛丸") (ℓ "丸乛")
  (rw 1 q13 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q16 ∷
   rw 5 q28 ∷
   rw 6 q16 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q20 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q16 ∷
   rw 5 q29 ∷
   rw⁻ 4 q16 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q30 ∷
   rw⁻ 2 q27 ∷
   rw 1 q30 ∷
   rw⁻ 0 q25 ∷
   rw 1 q31 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q32 ∷
   rw 0 q28 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q16 ∷
   rw 2 q19 ∷
   rw 3 q16 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q33 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q16 ∷
   rw 4 q19 ∷
   rw 5 q16 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q25 ∷
   rw 5 q20 ∷
   rw 4 q34 ∷
   re 3 1 (ℓ "乏丼丳丼乏") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丿") ∷
   rw 6 q35 ∷
   rw 5 q36 ∷
   rw 4 q37 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 3 q3 ∷
   re 4 5 (ℓ "乐") ∷
   rw 2 q38 ∷
   re 1 1 (ℓ "乏丼丳丼乏") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丿") ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 2 1 (ℓ "乏丸乏") ∷
   rw 1 q3 ∷
   re 2 5 (ℓ "乐") ∷
   rw 0 q39 ∷
   rw 6 q13 ∷
   rw⁻ 5 q25 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q16 ∷
   rw 5 q17 ∷
   rw⁻ 4 q16 ∷
   re 5 3 (ℓ "乓") ∷
   rw 3 q40 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q16 ∷
   rw 3 q17 ∷
   rw⁻ 2 q16 ∷
   re 3 3 (ℓ "乓") ∷
   rw 1 q29 ∷
   rw 2 q41 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q27 ∷
   rw 4 q26 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q16 ∷
   rw 6 q28 ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q13 ∷
   rw 2 q25 ∷
   rw 3 q42 ∷
   rw 4 q27 ∷
   rw 5 q42 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q16 ∷
   rw 7 q43 ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q31 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q20 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 553 W

-- pass [CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12] [X3 TOFF213 X3]: 1 steps
lem-pass-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-vs-X3-TOFF213-X3 : ⟪ (ℓ "丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶") ⟫ʷ
lem-pass-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-vs-X3-TOFF213-X3 = derive (ℓ "丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞乥丞") (ℓ "丞乥丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶")
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 509 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21] [X3 TOFF213 X3]: 1 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-vs-X3-TOFF213-X3 : ⟪ (ℓ "丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-vs-X3-TOFF213-X3 = derive (ℓ "丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞乥丞") (ℓ "丞乥丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇")
  (rw 0 q45 ∷ []) Eq.refl
