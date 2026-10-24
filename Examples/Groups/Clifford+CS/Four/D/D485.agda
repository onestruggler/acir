{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D485 (W : Ws) where

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
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 74 W
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1287 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 329 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = wE 31 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CS03]: 87 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS03 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗中") ⟫ʷ ≈ ⟪ (ℓ "中丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS03 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗中") (ℓ "中丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 30 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (ℓ "丽") ∷
   rw⁻ 28 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 23 q5 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q6 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q3 ∷
   rw 2 q8 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 10 q4 ∷
   rw 11 q7 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q4 ∷
   rw 16 q7 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q2 ∷
   rw 24 q12 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 29 q4 ∷
   rw 30 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q15 : Eqn
  q15 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 1288 W
  q20 : Eqn
  q20 = eqn (ℓ "丠业") (ℓ "业丠") (low-comm (CS) ((S ↑)))
  q21 : Eqn
  q21 = wE 1289 W
  q22 : Eqn
  q22 = wE 245 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CS01]: 45 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS01 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丠") ⟫ʷ ≈ ⟪ (ℓ "丠丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS01 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丠") (ℓ "丠丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw⁻ 28 q14 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q15 ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q18 ∷
   rw 23 q19 ∷
   rw⁻ 22 q17 ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q18 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q20 ∷
   rw⁻ 7 q14 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw⁻ 6 q17 ∷
   rw 9 q16 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q18 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1284 W
  q24 : Eqn
  q24 = wE 39 W
  q25 : Eqn
  q25 = wE 315 W
  q26 : Eqn
  q26 = wE 113 W
  q27 : Eqn
  q27 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q28 : Eqn
  q28 = wE 114 W
  q29 : Eqn
  q29 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q30 : Eqn
  q30 = wE 112 W
  q31 : Eqn
  q31 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q32 : Eqn
  q32 = wE 1290 W
  q33 : Eqn
  q33 = wE 40 W
  q34 : Eqn
  q34 = wE 6 W
  q35 : Eqn
  q35 = wE 481 W
  q36 : Eqn
  q36 = wE 1286 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CX31]: 455 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CX31 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乓") ⟫ʷ ≈ ⟪ (ℓ "乓丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CX31 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗乓") (ℓ "乓丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 29 q1 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 23 q5 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q6 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q3 ∷
   rw 2 q8 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q23 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   rw 5 q4 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 6 q2 ∷
   rw 7 q24 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乐") ∷
   rw 7 q11 ∷
   rw 8 q25 ∷
   rw 9 q11 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q11 ∷
   rw 15 q25 ∷
   rw 16 q10 ∷
   rw 17 q10 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q2 ∷
   rw 23 q24 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乐") ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q11 ∷
   rw 26 q10 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q13 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q16 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q16 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q26 ∷
   rw 31 q27 ∷
   rw 30 q28 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q18 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q18 ∷
   re 28 3 (ℓ "乓") ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q16 ∷
   re 28 3 (ℓ "丱") ∷
   re 28 1 (ℓ "乏丼两丼乏") ∷
   rw 34 q16 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q26 ∷
   rw 30 q27 ∷
   rw 29 q28 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q18 ∷
   re 29 5 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q18 ∷
   re 27 3 (ℓ "乓") ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q16 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q16 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q26 ∷
   rw 29 q29 ∷
   rw 28 q28 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q18 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q18 ∷
   re 26 3 (ℓ "乓") ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q16 ∷
   re 26 3 (ℓ "丱") ∷
   re 26 1 (ℓ "乏丼两丼乏") ∷
   rw 32 q16 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   rw 27 q28 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q18 ∷
   re 27 5 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丫乏") ∷
   rw 29 q18 ∷
   re 25 3 (ℓ "乓") ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q16 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q16 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q26 ∷
   rw 27 q29 ∷
   rw 26 q28 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q18 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q18 ∷
   re 24 3 (ℓ "乓") ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q16 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q16 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q26 ∷
   rw 26 q29 ∷
   rw 25 q28 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q18 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q18 ∷
   re 23 3 (ℓ "乓") ∷
   rw 24 q16 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q18 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q18 ∷
   rw 23 q30 ∷
   rw 24 q16 ∷
   re 22 3 (ℓ "乓") ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q18 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q16 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q16 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q26 ∷
   rw 24 q29 ∷
   rw 23 q28 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q18 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q18 ∷
   re 21 3 (ℓ "乓") ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q16 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q16 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q26 ∷
   rw 23 q29 ∷
   rw 22 q28 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q18 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q18 ∷
   re 20 3 (ℓ "乓") ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q16 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q16 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q26 ∷
   rw 22 q29 ∷
   rw 21 q28 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q18 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q18 ∷
   re 19 3 (ℓ "乓") ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q16 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q26 ∷
   rw 21 q29 ∷
   rw 20 q28 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q18 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q18 ∷
   re 18 3 (ℓ "乓") ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q16 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q16 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q26 ∷
   rw 20 q29 ∷
   rw 19 q28 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q18 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q18 ∷
   re 17 3 (ℓ "乓") ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q16 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q16 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q26 ∷
   rw 19 q29 ∷
   rw 18 q28 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q18 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q18 ∷
   re 16 3 (ℓ "乓") ∷
   rw 15 q31 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 14 q16 ∷
   re 15 3 (ℓ "丱") ∷
   re 15 1 (ℓ "乏丼两丼乏") ∷
   rw 21 q16 ∷
   re 19 3 (ℓ "乓") ∷
   rw 18 q26 ∷
   rw 17 q27 ∷
   rw 16 q28 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q18 ∷
   re 16 5 (ℓ "丱") ∷
   re 16 1 (ℓ "乏丫乏") ∷
   rw 18 q18 ∷
   re 14 3 (ℓ "乓") ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 13 q16 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q16 ∷
   re 18 3 (ℓ "乓") ∷
   rw 17 q26 ∷
   rw 16 q29 ∷
   rw 15 q28 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 14 q18 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q18 ∷
   re 13 3 (ℓ "乓") ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 12 q16 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q16 ∷
   re 17 3 (ℓ "乓") ∷
   rw 16 q26 ∷
   rw 15 q29 ∷
   rw 14 q28 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 13 q18 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q18 ∷
   re 12 3 (ℓ "乓") ∷
   re 12 1 (ℓ "乏乆乏") ∷
   rw 11 q16 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q16 ∷
   re 16 3 (ℓ "乓") ∷
   rw 15 q26 ∷
   rw 14 q29 ∷
   rw 13 q28 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 12 q18 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q18 ∷
   re 11 3 (ℓ "乓") ∷
   rw 10 q31 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q16 ∷
   re 10 3 (ℓ "丱") ∷
   re 10 1 (ℓ "乏丼两丼乏") ∷
   rw 16 q16 ∷
   re 14 3 (ℓ "乓") ∷
   rw 13 q26 ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 10 q18 ∷
   re 11 5 (ℓ "丱") ∷
   re 11 1 (ℓ "乏丫乏") ∷
   rw 13 q18 ∷
   re 9 3 (ℓ "乓") ∷
   rw 8 q31 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q16 ∷
   re 8 3 (ℓ "丱") ∷
   re 8 1 (ℓ "乏丼两丼乏") ∷
   rw 14 q16 ∷
   re 12 3 (ℓ "乓") ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   rw 9 q28 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q18 ∷
   re 9 5 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丫乏") ∷
   rw 11 q18 ∷
   re 7 3 (ℓ "乓") ∷
   rw 8 q16 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q18 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q18 ∷
   rw 7 q30 ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "乓") ∷
   rw 9 q16 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q18 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q33 ∷
   rw 0 q33 ∷
   rw 30 q1 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q3 ∷
   rw 26 q8 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   re 23 1 (ℓ "乏乃乏") ∷
   rw⁻ 25 q2 ∷
   rw 24 q34 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (ℓ "乓") ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q35 ∷
   rw 15 q8 ∷
   rw 14 q3 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q35 ∷
   rw 10 q8 ∷
   rw 9 q35 ∷
   rw 8 q8 ∷
   re 7 1 (ℓ "乏乃乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q34 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 6 q4 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q5 ∷
   rw 2 q36 ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 10 q4 ∷
   rw 11 q7 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q4 ∷
   rw 16 q7 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q2 ∷
   rw 24 q12 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 29 q4 ∷
   rw 30 q13 ∷ []) Eq.refl
