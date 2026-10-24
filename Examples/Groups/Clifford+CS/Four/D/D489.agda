{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D489 (W : Ws) where

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
  q3 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 74 W
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1297 W
  q10 : Eqn
  q10 = wE 39 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 329 W
  q13 : Eqn
  q13 = wE 315 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 113 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q18 : Eqn
  q18 = wE 114 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q21 : Eqn
  q21 = wE 112 W
  q22 : Eqn
  q22 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q23 : Eqn
  q23 = wE 40 W
  q24 : Eqn
  q24 = wE 1290 W
  q25 : Eqn
  q25 = wE 6 W
  q26 : Eqn
  q26 = wE 481 W
  q27 : Eqn
  q27 = wE 1298 W
  q28 : Eqn
  q28 = wE 30 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CX31]: 521 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义乓") ⟫ʷ ≈ ⟪ (ℓ "乓丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义乓") (ℓ "乓丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (ℓ "乀") ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q2 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 7 q2 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw⁻ 6 q4 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q7 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q2 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q2 ∷
   rw 5 q2 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 6 q4 ∷
   rw 7 q10 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "乐") ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   rw 9 q11 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q13 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乐") ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 30 q11 ∷
   rw 31 q14 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q15 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q15 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q16 ∷
   rw 33 q17 ∷
   rw 32 q18 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q19 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q19 ∷
   re 30 3 (ℓ "乓") ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q15 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q15 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   rw 31 q18 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q19 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q19 ∷
   re 29 3 (ℓ "乓") ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q15 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q15 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q16 ∷
   rw 31 q20 ∷
   rw 30 q18 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q19 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q19 ∷
   re 28 3 (ℓ "乓") ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q15 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q15 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q19 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q19 ∷
   re 27 3 (ℓ "乓") ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q15 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q15 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   rw 28 q18 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q19 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q19 ∷
   re 26 3 (ℓ "乓") ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q15 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q15 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q19 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q19 ∷
   re 25 3 (ℓ "乓") ∷
   rw 26 q15 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 27 q19 ∷
   re 24 1 (ℓ "乏乃乏") ∷
   rw 26 q19 ∷
   rw 25 q21 ∷
   rw 26 q15 ∷
   re 24 3 (ℓ "乓") ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q19 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q15 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q15 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q18 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q19 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q19 ∷
   re 23 3 (ℓ "乓") ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q15 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q15 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q16 ∷
   rw 25 q17 ∷
   rw 24 q18 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q19 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q19 ∷
   re 22 3 (ℓ "乓") ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q15 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q15 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q18 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q19 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q19 ∷
   re 21 3 (ℓ "乓") ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q15 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q19 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q19 ∷
   re 20 3 (ℓ "乓") ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q15 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q15 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   rw 21 q18 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q19 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q19 ∷
   re 19 3 (ℓ "乓") ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q15 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q15 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   rw 20 q18 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q19 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q19 ∷
   re 18 3 (ℓ "乓") ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q15 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q15 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   rw 19 q18 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q19 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q19 ∷
   re 17 3 (ℓ "乓") ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q15 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q15 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   rw 18 q18 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q19 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q19 ∷
   re 16 3 (ℓ "乓") ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q15 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q15 ∷
   re 20 3 (ℓ "乓") ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   rw 17 q18 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q19 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q19 ∷
   re 15 3 (ℓ "乓") ∷
   rw 14 q22 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 13 q15 ∷
   re 14 3 (ℓ "丱") ∷
   re 14 1 (ℓ "乏丼两丼乏") ∷
   rw 20 q15 ∷
   re 18 3 (ℓ "乓") ∷
   rw 17 q16 ∷
   rw 16 q20 ∷
   rw 15 q18 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 14 q19 ∷
   re 15 5 (ℓ "丱") ∷
   re 15 1 (ℓ "乏丫乏") ∷
   rw 17 q19 ∷
   re 13 3 (ℓ "乓") ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 12 q15 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q15 ∷
   re 17 3 (ℓ "乓") ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   rw 14 q18 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 13 q19 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q19 ∷
   re 12 3 (ℓ "乓") ∷
   re 12 1 (ℓ "乏乆乏") ∷
   rw 11 q15 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q15 ∷
   re 16 3 (ℓ "乓") ∷
   rw 15 q16 ∷
   rw 14 q17 ∷
   rw 13 q18 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 12 q19 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q19 ∷
   re 11 3 (ℓ "乓") ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 10 q15 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q15 ∷
   re 15 3 (ℓ "乓") ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q18 ∷
   re 12 1 (ℓ "乏乆乏") ∷
   rw 11 q19 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q19 ∷
   re 10 3 (ℓ "乓") ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q15 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q15 ∷
   re 14 3 (ℓ "乓") ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   rw 11 q18 ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 10 q19 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q19 ∷
   re 9 3 (ℓ "乓") ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q15 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q15 ∷
   re 13 3 (ℓ "乓") ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q19 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q19 ∷
   re 8 3 (ℓ "乓") ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q15 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q15 ∷
   re 12 3 (ℓ "乓") ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   rw 9 q18 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q19 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q19 ∷
   re 7 3 (ℓ "乓") ∷
   rw 8 q15 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q19 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q19 ∷
   rw 7 q21 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "乓") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q19 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q23 ∷
   rw 0 q23 ∷
   rw 32 q1 ∷
   rw 31 q7 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   re 25 1 (ℓ "乏乃乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q25 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "乓") ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q26 ∷
   rw 14 q8 ∷
   rw 13 q7 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   re 7 1 (ℓ "乏乃乏") ∷
   rw⁻ 9 q4 ∷
   rw 8 q25 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q2 ∷
   rw 2 q27 ∷
   rw 1 q11 ∷
   rw 2 q11 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q4 ∷
   rw 8 q28 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q2 ∷
   rw 9 q2 ∷
   rw 10 q2 ∷
   rw 11 q2 ∷
   rw 12 q2 ∷
   rw 13 q2 ∷
   rw 14 q3 ∷
   rw 15 q6 ∷
   rw 16 q2 ∷
   rw 17 q2 ∷
   rw 18 q2 ∷
   rw 19 q2 ∷
   rw 20 q2 ∷
   rw 21 q2 ∷
   rw 22 q2 ∷
   rw 23 q2 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q4 ∷
   rw 26 q28 ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q2 ∷
   rw 27 q2 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 31 q2 ∷
   rw 32 q14 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q30 : Eqn
  q30 = eqn (ℓ "両乗") (ℓ "乗両") (low-comm ((CS • CS • CS)) (CK₁₀))
  q31 : Eqn
  q31 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q32 : Eqn
  q32 = wE 1291 W
  q33 : Eqn
  q33 = eqn (ℓ "両业") (ℓ "业両") (low-comm ((CS • CS • CS)) ((S ↑)))
  q34 : Eqn
  q34 = wE 246 W
  q35 : Eqn
  q35 = wE 1292 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CSd01]: 47 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义両") ⟫ʷ ≈ ⟪ (ℓ "両丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义両") (ℓ "両丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw⁻ 30 q29 ∷
   rw⁻ 29 q29 ∷
   rw⁻ 28 q30 ∷
   rw⁻ 27 q29 ∷
   rw⁻ 26 q29 ∷
   rw⁻ 25 q29 ∷
   rw 26 q15 ∷
   rw 25 q31 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw 26 q19 ∷
   rw 25 q32 ∷
   rw⁻ 24 q31 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q19 ∷
   rw⁻ 23 q29 ∷
   rw⁻ 22 q29 ∷
   rw⁻ 21 q29 ∷
   rw⁻ 20 q29 ∷
   rw⁻ 19 q29 ∷
   rw⁻ 18 q29 ∷
   rw⁻ 17 q29 ∷
   rw⁻ 16 q29 ∷
   rw⁻ 15 q29 ∷
   rw⁻ 14 q33 ∷
   rw⁻ 13 q30 ∷
   rw⁻ 12 q29 ∷
   rw⁻ 11 q29 ∷
   rw⁻ 10 q29 ∷
   rw⁻ 9 q29 ∷
   rw⁻ 8 q29 ∷
   rw⁻ 7 q29 ∷
   rw 8 q15 ∷
   rw 7 q31 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q19 ∷
   rw 7 q32 ∷
   rw⁻ 6 q31 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q19 ∷
   rw 5 q34 ∷
   rw 4 q34 ∷
   rw 3 q35 ∷
   rw 2 q34 ∷
   rw 1 q34 ∷
   rw 0 q34 ∷ []) Eq.refl
