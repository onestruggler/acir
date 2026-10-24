{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D193 (W : Ws) where

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
  q1 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 360 W
  q4 : Eqn
  q4 = eqn (ℓ "两乘") (ℓ "乘两") (low-comm (CK₀₁) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = wE 362 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q8 : Eqn
  q8 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = wE 173 W
  q10 : Eqn
  q10 = wE 789 W
  q11 : Eqn
  q11 = wE 175 W
  q12 : Eqn
  q12 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丈乕") (ℓ "乕丈") (low₁-comm (S) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)))
  q14 : Eqn
  q14 = wE 790 W
  q15 : Eqn
  q15 = wE 791 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 CKd31 X3]: 351 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd31-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乕丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd31-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乕丞") (ℓ "丞乕丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 28 q1 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丼两丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乕") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏么乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "丱") ∷
   re 31 1 (ℓ "乏丫乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "乕") ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (ℓ "乏么乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乕") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "乕") ∷
   rw 29 q1 ∷
   rw 26 q7 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "乕") ∷
   rw 31 q3 ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏么乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "乕") ∷
   rw 28 q7 ∷
   rw 25 q1 ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丼两丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乕") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "丱") ∷
   re 28 1 (ℓ "乏丫乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "乕") ∷
   rw 27 q1 ∷
   rw 24 q7 ∷
   re 26 1 (ℓ "乏么乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乕") ∷
   rw 29 q3 ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "乕") ∷
   rw 26 q7 ∷
   rw 23 q7 ∷
   re 25 1 (ℓ "乏么乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "乕") ∷
   rw 28 q3 ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏么乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "乕") ∷
   rw 25 q7 ∷
   rw 26 q2 ∷
   rw 25 q9 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 26 q6 ∷
   rw 23 q9 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q6 ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乕") ∷
   rw 24 q11 ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q6 ∷
   rw 21 q7 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乕") ∷
   rw 26 q3 ∷
   rw 25 q8 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "乕") ∷
   rw 23 q7 ∷
   rw 20 q7 ∷
   re 22 1 (ℓ "乏么乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乕") ∷
   rw 25 q3 ∷
   rw 24 q8 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "乕") ∷
   rw 22 q7 ∷
   rw 19 q7 ∷
   re 21 1 (ℓ "乏么乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乕") ∷
   rw 24 q3 ∷
   rw 23 q8 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏么乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "乕") ∷
   rw 21 q7 ∷
   rw 18 q7 ∷
   re 20 1 (ℓ "乏么乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乕") ∷
   rw 23 q3 ∷
   rw 22 q8 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏么乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "乕") ∷
   rw 20 q7 ∷
   rw 17 q7 ∷
   re 19 1 (ℓ "乏么乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乕") ∷
   rw 22 q3 ∷
   rw 21 q8 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏么乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "乕") ∷
   rw 19 q7 ∷
   rw 16 q7 ∷
   re 18 1 (ℓ "乏么乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乕") ∷
   rw 21 q3 ∷
   rw 20 q8 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏么乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "乕") ∷
   rw 18 q7 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   re 16 1 (ℓ "乏么乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "丱") ∷
   re 16 1 (ℓ "乏丼两丼乏") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乕") ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (ℓ "乏么乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "丱") ∷
   re 17 1 (ℓ "乏丫乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "乕") ∷
   rw 16 q1 ∷
   rw 13 q7 ∷
   re 15 1 (ℓ "乏么乏") ∷
   rw 14 q2 ∷
   re 15 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "乕") ∷
   rw 18 q3 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   re 16 1 (ℓ "乏么乏") ∷
   rw 15 q6 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 14 3 (ℓ "乕") ∷
   rw 15 q7 ∷
   rw 12 q7 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "乕") ∷
   rw 17 q3 ∷
   rw 16 q8 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏么乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "乕") ∷
   rw 14 q7 ∷
   rw 11 q7 ∷
   re 13 1 (ℓ "乏么乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "乕") ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   rw 14 q5 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "乕") ∷
   rw 13 q7 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q12 ∷
   rw 9 q1 ∷
   re 11 1 (ℓ "乏么乏") ∷
   rw 10 q2 ∷
   re 11 3 (ℓ "丱") ∷
   re 11 1 (ℓ "乏丼两丼乏") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乕") ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q6 ∷
   re 12 5 (ℓ "丱") ∷
   re 12 1 (ℓ "乏丫乏") ∷
   rw 14 q6 ∷
   re 10 3 (ℓ "乕") ∷
   rw 11 q1 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   rw 7 q1 ∷
   re 9 1 (ℓ "乏么乏") ∷
   rw 8 q2 ∷
   re 9 3 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丼两丼乏") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "乕") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q6 ∷
   re 10 5 (ℓ "丱") ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q6 ∷
   re 8 3 (ℓ "乕") ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏么乏") ∷
   rw 10 q6 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q6 ∷
   rw 7 q10 ∷
   rw 6 q11 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "乕") ∷
   rw 8 q11 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q6 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q17 : Eqn
  q17 = wE 43 W
  q18 : Eqn
  q18 = wE 100 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q21 : Eqn
  q21 = wE 190 W
  q22 : Eqn
  q22 = wE 107 W
  q23 : Eqn
  q23 = eqn (ℓ "丳之") (ℓ "之丳") (low-comm (CX₁₀) (CZ))
  q24 : Eqn
  q24 = wE 108 W
  q25 : Eqn
  q25 = wE 109 W
  q26 : Eqn
  q26 = wE 110 W
  q27 : Eqn
  q27 = wE 104 W

-- comm CCZ013 CZ12: 85 steps
lem-comm-CCZ013-CZ12 : ⟪ (ℓ "乚丸") ⟫ʷ ≈ ⟪ (ℓ "丸乚") ⟫ʷ
lem-comm-CCZ013-CZ12 = derive (ℓ "乚丸") (ℓ "丸乚")
  (rw 1 q2 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q16 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q16 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q6 ∷
   rw 1 q16 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw 1 q17 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q18 ∷
   rw⁻ 0 q19 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "乐") ∷
   rw⁻ 2 q20 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乐") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q6 ∷
   rw 4 q21 ∷
   re 3 1 (ℓ "乏丼丳丼乏") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丿") ∷
   rw 6 q22 ∷
   rw 5 q23 ∷
   rw 4 q24 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 3 q6 ∷
   re 4 5 (ℓ "乐") ∷
   rw 2 q25 ∷
   re 1 1 (ℓ "乏丼丳丼乏") ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丿") ∷
   rw 4 q22 ∷
   rw 3 q23 ∷
   rw 2 q24 ∷
   re 2 1 (ℓ "乏丸乏") ∷
   rw 1 q6 ∷
   re 2 5 (ℓ "乐") ∷
   rw 0 q26 ∷
   rw 6 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw 6 q6 ∷
   rw 3 q20 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q6 ∷
   rw 1 q19 ∷
   rw 2 q27 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 2 q17 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 792 W

-- pass [CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12] [X3 TOFF123 X3]: 1 steps
lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 : ⟪ (ℓ "义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶") ⟫ʷ
lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 = derive (ℓ "义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞乢丞") (ℓ "丞乢丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 793 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12] [X3 TOFF123 X3]: 1 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 : ⟪ (ℓ "义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 = derive (ℓ "义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乢丞") (ℓ "丞乢丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为")
  (rw 0 q29 ∷ []) Eq.refl
