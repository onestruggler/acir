{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D488 (W : Ws) where

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
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = wE 74 W
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1299 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 329 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = wE 31 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CS03]: 91 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义中") ⟫ʷ ≈ ⟪ (ℓ "中丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS03 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义中") (ℓ "中丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 32 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 30 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 25 q4 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q2 ∷
   rw 25 q6 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (ℓ "乀") ∷
   rw⁻ 23 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q8 ∷
   rw 2 q3 ∷
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
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q4 ∷
   rw 9 q4 ∷
   rw 10 q4 ∷
   rw 11 q4 ∷
   rw 12 q4 ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q7 ∷
   rw 16 q4 ∷
   rw 17 q4 ∷
   rw 18 q4 ∷
   rw 19 q4 ∷
   rw 20 q4 ∷
   rw 21 q4 ∷
   rw 22 q4 ∷
   rw 23 q4 ∷
   rw 24 q4 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q2 ∷
   rw 26 q12 ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q4 ∷
   rw 27 q4 ∷
   rw 28 q4 ∷
   rw 29 q5 ∷
   rw 30 q4 ∷
   rw 31 q4 ∷
   rw 32 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q15 : Eqn
  q15 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
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
  q21 = wE 245 W
  q22 : Eqn
  q22 = wE 1289 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CS01]: 47 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丠") ⟫ʷ ≈ ⟪ (ℓ "丠丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CS01 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丠") (ℓ "丠丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw⁻ 30 q14 ∷
   rw⁻ 29 q14 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 25 q14 ∷
   rw 26 q16 ∷
   rw 25 q17 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw 26 q18 ∷
   rw 25 q19 ∷
   rw⁻ 24 q17 ∷
   rw 27 q16 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q18 ∷
   rw⁻ 23 q14 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 21 q14 ∷
   rw⁻ 20 q14 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q14 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 14 q20 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q14 ∷
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
   rw 1 q21 ∷
   rw 0 q21 ∷ []) Eq.refl
