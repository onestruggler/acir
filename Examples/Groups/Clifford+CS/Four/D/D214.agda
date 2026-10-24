{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D214 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 359 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q10 : Eqn
  q10 = wE 361 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 20 W
  q13 : Eqn
  q13 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q14 : Eqn
  q14 = wE 49 W
  q15 : Eqn
  q15 = wE 360 W
  q16 : Eqn
  q16 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q17 : Eqn
  q17 = wE 362 W
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q20 : Eqn
  q20 = eqn (ℓ "乇业") (ℓ "业乇") (low₃-comm ((CK₁₀ ↑)) (S))
  q21 : Eqn
  q21 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q22 : Eqn
  q22 = eqn (ℓ "么业") (ℓ "业么") (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 630 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q27 : Eqn
  q27 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q28 : Eqn
  q28 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q29 : Eqn
  q29 = wE 810 W
  q30 : Eqn
  q30 = wE 811 W
  q31 : Eqn
  q31 = wE 812 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 CS12 CS12 CKd21 X2] part2: 214 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並乇丶丶么丘中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丘乇丶丶么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並乇丶丶么丘中中乑业中中中中中中乌中中乑中乑乑") (ℓ "丘乇丶丶么丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw⁻ 13 q1 ∷
   rw 12 q2 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q5 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "乔") ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q12 ∷
   rw 16 q13 ∷
   rw 15 q14 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "乕") ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   re 16 1 (ℓ "乏么乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "中") ∷
   rw 18 q18 ∷
   rw⁻ 17 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q1 ∷
   rw 17 q2 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q1 ∷
   rw 18 q5 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q6 ∷
   rw⁻ 10 q19 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw⁻ 14 q22 ∷
   rw⁻ 15 q19 ∷
   rw 11 q18 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q23 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q24 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q1 ∷
   rw 11 q25 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "乔") ∷
   rw 13 q8 ∷
   rw 12 q26 ∷
   rw 11 q10 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q12 ∷
   rw 13 q27 ∷
   rw 12 q14 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼临丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q12 ∷
   rw 14 q27 ∷
   rw 13 q14 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "乕") ∷
   rw 16 q15 ∷
   rw 15 q28 ∷
   rw 14 q17 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "乑") ∷
   rw 16 q18 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q1 ∷
   rw 15 q23 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q24 ∷
   rw 14 q4 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q1 ∷
   rw 16 q25 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 9 q20 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q21 ∷
   rw⁻ 12 q22 ∷
   rw⁻ 13 q19 ∷
   rw 9 q18 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q1 ∷
   rw 8 q23 ∷
   rw⁻ 7 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q24 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q1 ∷
   rw 9 q25 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "乔") ∷
   rw 11 q8 ∷
   rw 10 q26 ∷
   rw 9 q10 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q11 ∷
   re 9 5 (ℓ "乑") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q12 ∷
   rw 11 q27 ∷
   rw 10 q14 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q11 ∷
   re 10 5 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q12 ∷
   rw 12 q27 ∷
   rw 11 q14 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "乕") ∷
   rw 14 q15 ∷
   rw 13 q28 ∷
   rw 12 q17 ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "乑") ∷
   rw 14 q18 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q23 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "乔") ∷
   rw 13 q24 ∷
   rw 12 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q1 ∷
   rw 14 q25 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q6 ∷
   rw 6 q29 ∷
   rw 5 q30 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 813 W

-- groups [CK21 CS12 CS12 CKd21] [X2 TOFF312 X2]: 1 steps
lem-groups-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 : ⟪ (ℓ "乇丶丶么丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘乇丶丶么") ⟫ʷ
lem-groups-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 = derive (ℓ "乇丶丶么丘乨丘") (ℓ "丘乨丘乇丶丶么")
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q34 : Eqn
  q34 = eqn (ℓ "两乍") (ℓ "乍两") (low-comm (CK₀₁) (CK₀₁))
  q35 : Eqn
  q35 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q36 : Eqn
  q36 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q37 : Eqn
  q37 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q38 : Eqn
  q38 = wE 6 W
  q39 : Eqn
  q39 = wE 683 W
  q40 : Eqn
  q40 = wE 39 W
  q41 : Eqn
  q41 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q42 : Eqn
  q42 = eqn (ℓ "丈乍") (ℓ "乍丈") (low₁-comm (S) ((CK₀₁ ↑)))
  q43 : Eqn
  q43 = wE 684 W
  q44 : Eqn
  q44 = wE 685 W

-- pass [CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01] [X2 CK23 X2]: 91 steps
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CK23-X2 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乍丘") ⟫ʷ ≈ ⟪ (ℓ "丘乍丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CK23-X2 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乍丘") (ℓ "丘乍丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 28 q33 ∷
   rw 29 q34 ∷
   rw 30 q33 ∷
   rw 27 q33 ∷
   rw 28 q34 ∷
   rw 29 q33 ∷
   rw 26 q35 ∷
   rw 27 q36 ∷
   rw 28 q35 ∷
   rw 25 q33 ∷
   rw 26 q34 ∷
   rw 27 q33 ∷
   rw 24 q35 ∷
   rw 25 q36 ∷
   rw 26 q35 ∷
   rw 23 q35 ∷
   rw 24 q36 ∷
   rw 25 q35 ∷
   rw 26 q18 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q37 ∷
   rw⁻ 23 q4 ∷
   rw 22 q38 ∷
   rw 23 q39 ∷
   rw 22 q4 ∷
   rw 23 q37 ∷
   rw 24 q4 ∷
   rw 25 q40 ∷
   rw 26 q6 ∷
   rw 21 q35 ∷
   rw 22 q36 ∷
   rw 23 q35 ∷
   rw 20 q35 ∷
   rw 21 q36 ∷
   rw 22 q35 ∷
   rw 19 q35 ∷
   rw 20 q36 ∷
   rw 21 q35 ∷
   rw 18 q35 ∷
   rw 19 q36 ∷
   rw 20 q35 ∷
   rw 17 q35 ∷
   rw 18 q36 ∷
   rw 19 q35 ∷
   rw 16 q35 ∷
   rw 17 q36 ∷
   rw 18 q35 ∷
   rw 15 q41 ∷
   rw 16 q42 ∷
   rw 17 q41 ∷
   rw 14 q33 ∷
   rw 15 q34 ∷
   rw 16 q33 ∷
   rw 13 q35 ∷
   rw 14 q36 ∷
   rw 15 q35 ∷
   rw 12 q35 ∷
   rw 13 q36 ∷
   rw 14 q35 ∷
   rw 11 q35 ∷
   rw 12 q36 ∷
   rw 13 q35 ∷
   rw 10 q41 ∷
   rw 11 q42 ∷
   rw 12 q41 ∷
   rw 9 q33 ∷
   rw 10 q34 ∷
   rw 11 q33 ∷
   rw 8 q41 ∷
   rw 9 q42 ∷
   rw 10 q41 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   rw 9 q33 ∷
   rw 10 q18 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q37 ∷
   rw⁻ 7 q4 ∷
   rw 6 q38 ∷
   rw 7 q39 ∷
   rw 6 q4 ∷
   rw 7 q37 ∷
   rw 8 q4 ∷
   rw 9 q40 ∷
   rw 10 q6 ∷
   rw 5 q43 ∷
   rw 4 q43 ∷
   rw 3 q44 ∷
   rw 2 q43 ∷
   rw 1 q44 ∷
   rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 531 W

-- pass [CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01] [X2 CK21 X2]: 1 steps
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CK21-X2 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乇丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CK21-X2 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乇丘") (ℓ "丘乇丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 0 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 546 W

-- pass [CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01] [X2 CKd21 X2]: 1 steps
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CKd21-X2 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘么丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CKd21-X2 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘么丘") (ℓ "丘么丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 0 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (ℓ "两乎") (ℓ "乎两") (low-comm (CK₀₁) ((S • CK₀₁)))
  q48 : Eqn
  q48 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))
  q49 : Eqn
  q49 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))
  q50 : Eqn
  q50 = wE 691 W
  q51 : Eqn
  q51 = eqn (ℓ "丈乎") (ℓ "乎丈") (low₁-comm (S) (((S • CK₀₁) ↑)))
  q52 : Eqn
  q52 = wE 692 W
  q53 : Eqn
  q53 = wE 693 W

-- pass [CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01] [X2 CKd23 X2]: 91 steps
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CKd23-X2 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乎丘") ⟫ʷ ≈ ⟪ (ℓ "丘乎丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-CKd23-X2 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乎丘") (ℓ "丘乎丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 28 q33 ∷
   rw 29 q47 ∷
   rw 30 q33 ∷
   rw 27 q33 ∷
   rw 28 q47 ∷
   rw 29 q33 ∷
   rw 26 q35 ∷
   rw 27 q48 ∷
   rw 28 q35 ∷
   rw 25 q33 ∷
   rw 26 q47 ∷
   rw 27 q33 ∷
   rw 24 q35 ∷
   rw 25 q48 ∷
   rw 26 q35 ∷
   rw 23 q35 ∷
   rw 24 q48 ∷
   rw 25 q35 ∷
   rw 26 q18 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q49 ∷
   rw⁻ 23 q4 ∷
   rw 22 q38 ∷
   rw 23 q50 ∷
   rw 22 q4 ∷
   rw 23 q49 ∷
   rw 24 q4 ∷
   rw 25 q40 ∷
   rw 26 q6 ∷
   rw 21 q35 ∷
   rw 22 q48 ∷
   rw 23 q35 ∷
   rw 20 q35 ∷
   rw 21 q48 ∷
   rw 22 q35 ∷
   rw 19 q35 ∷
   rw 20 q48 ∷
   rw 21 q35 ∷
   rw 18 q35 ∷
   rw 19 q48 ∷
   rw 20 q35 ∷
   rw 17 q35 ∷
   rw 18 q48 ∷
   rw 19 q35 ∷
   rw 16 q35 ∷
   rw 17 q48 ∷
   rw 18 q35 ∷
   rw 15 q41 ∷
   rw 16 q51 ∷
   rw 17 q41 ∷
   rw 14 q33 ∷
   rw 15 q47 ∷
   rw 16 q33 ∷
   rw 13 q35 ∷
   rw 14 q48 ∷
   rw 15 q35 ∷
   rw 12 q35 ∷
   rw 13 q48 ∷
   rw 14 q35 ∷
   rw 11 q35 ∷
   rw 12 q48 ∷
   rw 13 q35 ∷
   rw 10 q41 ∷
   rw 11 q51 ∷
   rw 12 q41 ∷
   rw 9 q33 ∷
   rw 10 q47 ∷
   rw 11 q33 ∷
   rw 8 q41 ∷
   rw 9 q51 ∷
   rw 10 q41 ∷
   rw 7 q33 ∷
   rw 8 q47 ∷
   rw 9 q33 ∷
   rw 10 q18 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q49 ∷
   rw⁻ 7 q4 ∷
   rw 6 q38 ∷
   rw 7 q50 ∷
   rw 6 q4 ∷
   rw 7 q49 ∷
   rw 8 q4 ∷
   rw 9 q40 ∷
   rw 10 q6 ∷
   rw 5 q52 ∷
   rw 4 q52 ∷
   rw 3 q53 ∷
   rw 2 q52 ∷
   rw 1 q53 ∷
   rw 0 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 814 W

-- pass [CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13] [X2 TOFF312 X2]: 1 steps
lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 : ⟪ (ℓ "丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽") ⟫ʷ
lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 = derive (ℓ "丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘乨丘") (ℓ "丘乨丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽")
  (rw 0 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 815 W

-- groups [CS12 CS12 CK21 CS12] [X2 TOFF312 X2]: 1 steps
lem-groups-CS12-CS12-CK21-CS12-vs-X2-TOFF312-X2 : ⟪ (ℓ "丶丶乇丶丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丶丶乇丶") ⟫ʷ
lem-groups-CS12-CS12-CK21-CS12-vs-X2-TOFF312-X2 = derive (ℓ "丶丶乇丶丘乨丘") (ℓ "丘乨丘丶丶乇丶")
  (rw 0 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 816 W

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 S3 S3 S3 CK31 S3 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13] [X2 TOFF312 X2]: 1 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 : ⟪ (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽") ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 = derive (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘乨丘") (ℓ "丘乨丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽")
  (rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 817 W

-- groups [CSd12 CKd21 CS12 CS12] [X2 TOFF312 X2]: 1 steps
lem-groups-CSd12-CKd21-CS12-CS12-vs-X2-TOFF312-X2 : ⟪ (ℓ "丷么丶丶丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丷么丶丶") ⟫ʷ
lem-groups-CSd12-CKd21-CS12-CS12-vs-X2-TOFF312-X2 = derive (ℓ "丷么丶丶丘乨丘") (ℓ "丘乨丘丷么丶丶")
  (rw 0 q57 ∷ []) Eq.refl
