{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D484 (W : Ws) where

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
  q2 = wE 1106 W
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 772 W
  q5 : Eqn
  q5 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q7 : Eqn
  q7 = wE 74 W
  q8 : Eqn
  q8 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 1283 W
  q11 : Eqn
  q11 = wE 317 W
  q12 : Eqn
  q12 = wE 329 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = wE 31 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CK03 X0]: 91 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丱丌") ⟫ʷ ≈ ⟪ (ℓ "丌丱丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丱丌") (ℓ "丌丱丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乁") ∷
   rw 29 q2 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q9 ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   re 2 1 (ℓ "乏为乏") ∷
   rw 1 q3 ∷
   rw 2 q12 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丱") ∷
   rw 2 q11 ∷
   rw 3 q13 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q12 ∷
   rw 8 q12 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q3 ∷
   rw 10 q14 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "丰") ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q6 ∷
   rw 17 q5 ∷
   rw 18 q8 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q3 ∷
   rw 26 q14 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q6 ∷
   rw 27 q6 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q5 ∷
   rw 31 q5 ∷
   rw 32 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1284 W
  q17 : Eqn
  q17 = wE 39 W
  q18 : Eqn
  q18 = wE 315 W
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = wE 107 W
  q21 : Eqn
  q21 = eqn (ℓ "两之") (ℓ "之两") (low-comm (CK₀₁) (CZ))
  q22 : Eqn
  q22 = wE 108 W
  q23 : Eqn
  q23 = wE 3 W
  q24 : Eqn
  q24 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q25 : Eqn
  q25 = wE 714 W
  q26 : Eqn
  q26 = eqn (ℓ "丈丿") (ℓ "丿丈") (low₁-comm (S) ((Swap ↑ • CZ • Swap ↑)))
  q27 : Eqn
  q27 = wE 1285 W
  q28 : Eqn
  q28 = wE 713 W
  q29 : Eqn
  q29 = wE 6 W
  q30 : Eqn
  q30 = wE 481 W
  q31 : Eqn
  q31 = wE 1286 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CZ13]: 455 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CZ13 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丿") ⟫ʷ ≈ ⟪ (ℓ "丿丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CZ13 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丿") (ℓ "丿丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 29 q1 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q9 ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q16 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 6 q3 ∷
   rw 7 q17 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乐") ∷
   rw 7 q12 ∷
   rw 8 q18 ∷
   rw 9 q12 ∷
   rw 10 q18 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q12 ∷
   rw 15 q18 ∷
   rw 16 q13 ∷
   rw 17 q13 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q3 ∷
   rw 23 q17 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "乐") ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q12 ∷
   rw 26 q13 ∷
   rw 27 q12 ∷
   rw 28 q12 ∷
   rw 29 q15 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q19 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q19 ∷
   re 33 3 (ℓ "丿") ∷
   rw 32 q20 ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   re 30 1 (ℓ "乏丸乏") ∷
   rw 29 q23 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q23 ∷
   re 28 3 (ℓ "丿") ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q19 ∷
   re 28 3 (ℓ "丱") ∷
   re 28 1 (ℓ "乏丼两丼乏") ∷
   rw 34 q19 ∷
   re 32 3 (ℓ "丿") ∷
   rw 31 q20 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q23 ∷
   re 29 5 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q23 ∷
   re 27 3 (ℓ "丿") ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q19 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "丿") ∷
   rw 30 q20 ∷
   rw 29 q24 ∷
   rw 28 q22 ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q23 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q23 ∷
   re 26 3 (ℓ "丿") ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q19 ∷
   re 26 3 (ℓ "丱") ∷
   re 26 1 (ℓ "乏丼两丼乏") ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "丿") ∷
   rw 29 q20 ∷
   rw 28 q21 ∷
   rw 27 q22 ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q23 ∷
   re 27 5 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丫乏") ∷
   rw 29 q23 ∷
   re 25 3 (ℓ "丿") ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q19 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "丿") ∷
   rw 28 q20 ∷
   rw 27 q24 ∷
   rw 26 q22 ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q23 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q23 ∷
   re 24 3 (ℓ "丿") ∷
   re 24 1 (ℓ "乏丸乏") ∷
   rw 23 q19 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "丿") ∷
   rw 27 q20 ∷
   rw 26 q24 ∷
   rw 25 q22 ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q23 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q23 ∷
   re 23 3 (ℓ "丿") ∷
   rw 24 q19 ∷
   re 23 1 (ℓ "乏丸乏") ∷
   rw 25 q23 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q23 ∷
   rw 23 q25 ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "丿") ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q23 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q19 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "丿") ∷
   rw 25 q20 ∷
   rw 24 q24 ∷
   rw 23 q22 ∷
   re 23 1 (ℓ "乏丸乏") ∷
   rw 22 q23 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q23 ∷
   re 21 3 (ℓ "丿") ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q19 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q19 ∷
   re 25 3 (ℓ "丿") ∷
   rw 24 q20 ∷
   rw 23 q24 ∷
   rw 22 q22 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q23 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q23 ∷
   re 20 3 (ℓ "丿") ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q19 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "丿") ∷
   rw 23 q20 ∷
   rw 22 q24 ∷
   rw 21 q22 ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q23 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q23 ∷
   re 19 3 (ℓ "丿") ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q19 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q20 ∷
   rw 21 q24 ∷
   rw 20 q22 ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q23 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q23 ∷
   re 18 3 (ℓ "丿") ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q19 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "丿") ∷
   rw 21 q20 ∷
   rw 20 q24 ∷
   rw 19 q22 ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q23 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q23 ∷
   re 17 3 (ℓ "丿") ∷
   re 17 1 (ℓ "乏丸乏") ∷
   rw 16 q19 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "丿") ∷
   rw 20 q20 ∷
   rw 19 q24 ∷
   rw 18 q22 ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q23 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q23 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q26 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q19 ∷
   re 15 3 (ℓ "丱") ∷
   re 15 1 (ℓ "乏丼两丼乏") ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "丿") ∷
   rw 18 q20 ∷
   rw 17 q21 ∷
   rw 16 q22 ∷
   re 16 1 (ℓ "乏丸乏") ∷
   rw 15 q23 ∷
   re 16 5 (ℓ "丱") ∷
   re 16 1 (ℓ "乏丫乏") ∷
   rw 18 q23 ∷
   re 14 3 (ℓ "丿") ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q19 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q19 ∷
   re 18 3 (ℓ "丿") ∷
   rw 17 q20 ∷
   rw 16 q24 ∷
   rw 15 q22 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q23 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q23 ∷
   re 13 3 (ℓ "丿") ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q19 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "丿") ∷
   rw 16 q20 ∷
   rw 15 q24 ∷
   rw 14 q22 ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q23 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q23 ∷
   re 12 3 (ℓ "丿") ∷
   re 12 1 (ℓ "乏丸乏") ∷
   rw 11 q19 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q20 ∷
   rw 14 q24 ∷
   rw 13 q22 ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q23 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q23 ∷
   re 11 3 (ℓ "丿") ∷
   rw 10 q26 ∷
   re 10 1 (ℓ "乏丸乏") ∷
   rw 9 q19 ∷
   re 10 3 (ℓ "丱") ∷
   re 10 1 (ℓ "乏丼两丼乏") ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "丿") ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 11 q22 ∷
   re 11 1 (ℓ "乏丸乏") ∷
   rw 10 q23 ∷
   re 11 5 (ℓ "丱") ∷
   re 11 1 (ℓ "乏丫乏") ∷
   rw 13 q23 ∷
   re 9 3 (ℓ "丿") ∷
   rw 8 q26 ∷
   re 8 1 (ℓ "乏丸乏") ∷
   rw 7 q19 ∷
   re 8 3 (ℓ "丱") ∷
   re 8 1 (ℓ "乏丼两丼乏") ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "丿") ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 9 q22 ∷
   re 9 1 (ℓ "乏丸乏") ∷
   rw 8 q23 ∷
   re 9 5 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丫乏") ∷
   rw 11 q23 ∷
   re 7 3 (ℓ "丿") ∷
   rw 8 q19 ∷
   re 7 1 (ℓ "乏丸乏") ∷
   rw 9 q23 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q23 ∷
   rw 7 q25 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "丿") ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q23 ∷
   rw 5 q27 ∷
   rw 4 q27 ∷
   rw 3 q28 ∷
   rw 2 q27 ∷
   rw 1 q28 ∷
   rw 0 q28 ∷
   rw 30 q1 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q9 ∷
   rw 26 q4 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   re 23 1 (ℓ "乏乃乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q29 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "乓") ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q30 ∷
   rw 15 q4 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q30 ∷
   rw 10 q4 ∷
   rw 9 q30 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乃乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q29 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 6 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 1 q6 ∷
   rw 2 q31 ∷
   rw 1 q13 ∷
   rw 2 q13 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q12 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q3 ∷
   rw 8 q14 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q5 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q5 ∷
   rw 16 q8 ∷
   rw 17 q6 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q3 ∷
   rw 24 q14 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q5 ∷
   rw 27 q6 ∷
   rw 28 q5 ∷
   rw 29 q5 ∷
   rw 30 q15 ∷ []) Eq.refl
