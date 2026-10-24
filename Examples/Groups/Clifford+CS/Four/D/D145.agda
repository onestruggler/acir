{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D145 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = wE 30 W
  q4 : Eqn
  q4 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 74 W
  q10 : Eqn
  q10 = wE 26 W
  q11 : Eqn
  q11 = wE 75 W
  q12 : Eqn
  q12 = wE 39 W
  q13 : Eqn
  q13 = wE 29 W
  q14 : Eqn
  q14 = wE 713 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 714 W
  q18 : Eqn
  q18 = wE 107 W
  q19 : Eqn
  q19 = eqn (ℓ "両之") (ℓ "之両") (low-comm ((CS • CS • CS)) (CZ))
  q20 : Eqn
  q20 = wE 108 W
  q21 : Eqn
  q21 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q22 : Eqn
  q22 = wE 6 W
  q23 : Eqn
  q23 = wE 76 W
  q24 : Eqn
  q24 = wE 81 W
  q25 : Eqn
  q25 = wE 24 W
  q26 : Eqn
  q26 = wE 25 W

-- comm CCZ023 CZ13: 131 steps
lem-comm-CCZ023-CZ13 : ⟪ (ℓ "乛丿") ⟫ʷ ≈ ⟪ (ℓ "丿乛") ⟫ʷ
lem-comm-CCZ023-CZ13 = derive (ℓ "乛丿") (ℓ "丿乛")
  (rw 1 q1 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q11 ∷
   rw 0 q6 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q5 ∷
   rw 2 q12 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q13 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q5 ∷
   rw 4 q12 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q2 ∷
   rw 5 q7 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 6 q16 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "丿") ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q16 ∷
   re 3 1 (ℓ "乏丸乏") ∷
   rw 2 q15 ∷
   re 3 3 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丼両丼乏") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "丿") ∷
   rw 6 q18 ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 3 q16 ∷
   re 4 5 (ℓ "丮") ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q16 ∷
   re 2 3 (ℓ "丿") ∷
   rw 3 q15 ∷
   re 2 1 (ℓ "乏丸乏") ∷
   rw 4 q16 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丿") ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q16 ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw 0 q15 ∷
   re 1 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "丿") ∷
   rw 4 q18 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   re 2 1 (ℓ "乏丸乏") ∷
   rw 1 q16 ∷
   re 2 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q16 ∷
   re 0 3 (ℓ "丿") ∷
   rw 6 q1 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q22 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "乓") ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q5 ∷
   rw 3 q22 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (ℓ "乓") ∷
   rw 1 q8 ∷
   rw 2 q24 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q28 : Eqn
  q28 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))
  q29 : Eqn
  q29 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q30 : Eqn
  q30 = wE 122 W
  q31 : Eqn
  q31 = wE 127 W
  q32 : Eqn
  q32 = wE 337 W
  q33 : Eqn
  q33 = wE 715 W
  q34 : Eqn
  q34 = wE 124 W

-- groups [TOFF302] [X2 CKd23 X2]: 67 steps
lem-groups-TOFF302-vs-X2-CKd23-X2 : ⟪ (ℓ "乧丘乎丘") ⟫ʷ ≈ ⟪ (ℓ "丘乎丘乧") ⟫ʷ
lem-groups-TOFF302-vs-X2-CKd23-X2 = derive (ℓ "乧丘乎丘") (ℓ "丘乎丘乧")
  (rw 4 q1 ∷
   rw⁻ 3 q27 ∷
   rw⁻ 2 q28 ∷
   rw⁻ 1 q27 ∷
   re 0 1 (ℓ "並乨並") ∷
   re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q29 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q29 ∷
   rw 7 q30 ∷
   rw 8 q7 ∷
   rw 7 q31 ∷
   rw⁻ 6 q29 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q9 ∷
   rw⁻ 3 q4 ∷
   rw 2 q9 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 0 q29 ∷
   rw 1 q32 ∷
   re 1 8 (ℓ "乨") ∷
   rw 1 q33 ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   rw 2 q27 ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q29 ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q29 ∷
   rw 10 q30 ∷
   rw 3 q1 ∷
   rw 4 q29 ∷
   rw 5 q2 ∷
   rw 6 q25 ∷
   rw 7 q4 ∷
   rw 8 q25 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 10 q26 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q32 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 716 W
  q36 : Eqn
  q36 = wE 708 W
  q37 : Eqn
  q37 = wE 360 W
  q38 : Eqn
  q38 = eqn (ℓ "丣乘") (ℓ "乘丣") (low-comm (CX₀₁) ((S ↑ • CK₁₀)))
  q39 : Eqn
  q39 = wE 362 W
  q40 : Eqn
  q40 = wE 717 W
  q41 : Eqn
  q41 = wE 718 W
  q42 : Eqn
  q42 = wE 503 W
  q43 : Eqn
  q43 = wE 719 W

-- groups [CK23 CS02 CS23 CX03 CSd23 CX03 CKd23] [X2 CKd21 X2]: 83 steps
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CKd21-X2 : ⟪ (ℓ "乍丧义丰乊丰乎丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘么丘乍丧义丰乊丰乎") ⟫ʷ
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CKd21-X2 = derive (ℓ "乍丧义丰乊丰乎丘么丘") (ℓ "丘么丘乍丧义丰乊丰乎")
  (rw 6 q35 ∷
   rw 7 q1 ∷
   rw⁻ 6 q27 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q9 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q36 ∷
   rw 5 q27 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 6 q5 ∷
   rw 7 q3 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丰") ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏丼丣丼乏") ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "乕") ∷
   rw 9 q37 ∷
   rw 8 q38 ∷
   rw 7 q39 ∷
   re 7 1 (ℓ "乏么乏") ∷
   rw 6 q16 ∷
   re 7 5 (ℓ "丰") ∷
   rw 9 q1 ∷
   rw⁻ 8 q27 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw⁻ 9 q5 ∷
   rw 8 q9 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (ℓ "乀") ∷
   rw 8 q36 ∷
   rw 7 q27 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 8 q5 ∷
   rw 9 q3 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "丰") ∷
   rw 9 q7 ∷
   rw 4 q40 ∷
   rw 5 q1 ∷
   rw⁻ 4 q27 ∷
   re 3 1 (ℓ "乏个乏") ∷
   rw⁻ 5 q5 ∷
   rw 4 q9 ∷
   rw⁻ 3 q5 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q36 ∷
   rw 3 q27 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q5 ∷
   rw 5 q3 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "丰") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丼丣丼乏") ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乕") ∷
   rw 7 q37 ∷
   rw 6 q38 ∷
   rw 5 q39 ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q16 ∷
   re 5 5 (ℓ "丰") ∷
   rw 7 q1 ∷
   rw⁻ 6 q27 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q9 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q36 ∷
   rw 5 q27 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 6 q5 ∷
   rw 7 q3 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丰") ∷
   rw 7 q7 ∷
   rw 2 q41 ∷
   rw 1 q42 ∷
   rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 720 W

-- pass [CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13] [X2 TOFF123 X2]: 1 steps
lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF123-X2 : ⟪ (ℓ "丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽") ⟫ʷ
lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF123-X2 = derive (ℓ "丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘乢丘") (ℓ "丘乢丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽")
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 721 W

-- groups [CS12 CS12 CK21 CS12] [X2 TOFF123 X2]: 1 steps
lem-groups-CS12-CS12-CK21-CS12-vs-X2-TOFF123-X2 : ⟪ (ℓ "丶丶乇丶丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘丶丶乇丶") ⟫ʷ
lem-groups-CS12-CS12-CK21-CS12-vs-X2-TOFF123-X2 = derive (ℓ "丶丶乇丶丘乢丘") (ℓ "丘乢丘丶丶乇丶")
  (rw 0 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 722 W

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 S3 S3 S3 CK31 S3 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13] [X2 TOFF123 X2]: 1 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF123-X2 : ⟪ (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽") ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF123-X2 = derive (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘乢丘") (ℓ "丘乢丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽")
  (rw 0 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 723 W

-- groups [CSd12 CKd21 CS12 CS12] [X2 TOFF123 X2]: 1 steps
lem-groups-CSd12-CKd21-CS12-CS12-vs-X2-TOFF123-X2 : ⟪ (ℓ "丷么丶丶丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘丷么丶丶") ⟫ʷ
lem-groups-CSd12-CKd21-CS12-CS12-vs-X2-TOFF123-X2 = derive (ℓ "丷么丶丶丘乢丘") (ℓ "丘乢丘丷么丶丶")
  (rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 724 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘") (ℓ "丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q50 : Eqn
  q50 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q51 : Eqn
  q51 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q52 : Eqn
  q52 = eqn (ℓ "临乍") (ℓ "乍临") (low-comm (CK₁₀) (CK₀₁))
  q53 : Eqn
  q53 = wE 683 W
  q54 : Eqn
  q54 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q55 : Eqn
  q55 = eqn (ℓ "与乍") (ℓ "乍与") (low-comm ((S ↑)) (CK₀₁))
  q56 : Eqn
  q56 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q57 : Eqn
  q57 = wE 685 W
  q58 : Eqn
  q58 = wE 140 W
  q59 : Eqn
  q59 = wE 684 W
  q60 : Eqn
  q60 = wE 142 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CK23 X2]: 137 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK23-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乍丘") ⟫ʷ ≈ ⟪ (ℓ "丘乍丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK23-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乍丘") (ℓ "丘乍丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 30 q49 ∷
   rw 31 q50 ∷
   rw 32 q49 ∷
   rw 29 q49 ∷
   rw 30 q50 ∷
   rw 31 q49 ∷
   rw 28 q51 ∷
   rw 29 q52 ∷
   rw 30 q51 ∷
   rw 27 q49 ∷
   rw 28 q50 ∷
   rw 29 q49 ∷
   rw 26 q49 ∷
   rw 27 q50 ∷
   rw 28 q49 ∷
   rw 25 q49 ∷
   rw 26 q50 ∷
   rw 27 q49 ∷
   rw 24 q53 ∷
   rw 23 q49 ∷
   rw 24 q50 ∷
   rw 25 q49 ∷
   rw 22 q49 ∷
   rw 23 q50 ∷
   rw 24 q49 ∷
   rw 21 q49 ∷
   rw 22 q50 ∷
   rw 23 q49 ∷
   rw 20 q49 ∷
   rw 21 q50 ∷
   rw 22 q49 ∷
   rw 19 q49 ∷
   rw 20 q50 ∷
   rw 21 q49 ∷
   rw 18 q49 ∷
   rw 19 q50 ∷
   rw 20 q49 ∷
   rw 17 q49 ∷
   rw 18 q50 ∷
   rw 19 q49 ∷
   rw 16 q49 ∷
   rw 17 q50 ∷
   rw 18 q49 ∷
   rw 15 q49 ∷
   rw 16 q50 ∷
   rw 17 q49 ∷
   rw 14 q54 ∷
   rw 15 q55 ∷
   rw 16 q54 ∷
   rw 13 q51 ∷
   rw 14 q52 ∷
   rw 15 q51 ∷
   rw 12 q49 ∷
   rw 13 q50 ∷
   rw 14 q49 ∷
   rw 11 q49 ∷
   rw 12 q50 ∷
   rw 13 q49 ∷
   rw 10 q49 ∷
   rw 11 q50 ∷
   rw 12 q49 ∷
   rw 9 q49 ∷
   rw 10 q50 ∷
   rw 11 q49 ∷
   rw 8 q49 ∷
   rw 9 q50 ∷
   rw 10 q49 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   rw 9 q49 ∷
   rw 6 q53 ∷
   rw 9 q1 ∷
   rw⁻ 8 q27 ∷
   rw⁻ 7 q56 ∷
   rw⁻ 6 q27 ∷
   rw 5 q8 ∷
   rw 6 q57 ∷
   rw 5 q27 ∷
   rw 6 q56 ∷
   rw 7 q27 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 8 q1 ∷
   rw⁻ 7 q27 ∷
   rw⁻ 6 q56 ∷
   rw⁻ 5 q27 ∷
   rw 4 q8 ∷
   rw 5 q57 ∷
   rw 4 q27 ∷
   rw 5 q56 ∷
   rw 6 q27 ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 7 q1 ∷
   rw⁻ 6 q27 ∷
   rw⁻ 5 q56 ∷
   rw⁻ 4 q27 ∷
   rw 3 q58 ∷
   rw 4 q59 ∷
   rw 3 q27 ∷
   rw 4 q56 ∷
   rw 5 q27 ∷
   rw 6 q60 ∷
   rw 7 q7 ∷
   rw 6 q1 ∷
   rw⁻ 5 q27 ∷
   rw⁻ 4 q56 ∷
   rw⁻ 3 q27 ∷
   rw 2 q8 ∷
   rw 3 q57 ∷
   rw 2 q27 ∷
   rw 3 q56 ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 5 q1 ∷
   rw⁻ 4 q27 ∷
   rw⁻ 3 q56 ∷
   rw⁻ 2 q27 ∷
   rw 1 q8 ∷
   rw 2 q57 ∷
   rw 1 q27 ∷
   rw 2 q56 ∷
   rw 3 q27 ∷
   rw 4 q6 ∷
   rw 5 q7 ∷
   rw 4 q1 ∷
   rw⁻ 3 q27 ∷
   rw⁻ 2 q56 ∷
   rw⁻ 1 q27 ∷
   rw 0 q8 ∷
   rw 1 q57 ∷
   rw 0 q27 ∷
   rw 1 q56 ∷
   rw 2 q27 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 725 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CK20 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乄丘") ⟫ʷ ≈ ⟪ (ℓ "丘乄丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK20-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乄丘") (ℓ "丘乄丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q61 ∷ []) Eq.refl
