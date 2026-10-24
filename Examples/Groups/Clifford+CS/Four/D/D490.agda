{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D490 (W : Ws) where

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
  q4 = wE 1228 W
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q7 : Eqn
  q7 = wE 74 W
  q8 : Eqn
  q8 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 772 W
  q11 : Eqn
  q11 = wE 1300 W
  q12 : Eqn
  q12 = wE 317 W
  q13 : Eqn
  q13 = wE 330 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 30 W
  q17 : Eqn
  q17 = wE 31 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 CKd03 X0]: 95 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CKd03-X0 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌串丌") ⟫ʷ ≈ ⟪ (ℓ "丌串丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CKd03-X0 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌串丌") (ℓ "丌串丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (ℓ "乏丬乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乂") ∷
   rw 31 q2 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q5 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q7 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "乀") ∷
   rw⁻ 23 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 14 q8 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 2 q9 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   re 2 1 (ℓ "乏主乏") ∷
   rw 1 q3 ∷
   rw 2 q13 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "串") ∷
   rw 2 q12 ∷
   rw 3 q14 ∷
   rw 4 q14 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 7 q14 ∷
   rw 8 q14 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q3 ∷
   rw 10 q16 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "丰") ∷
   rw 10 q5 ∷
   rw 11 q5 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q5 ∷
   rw 16 q6 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   rw 23 q5 ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q5 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q3 ∷
   rw 28 q16 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "丰") ∷
   rw 28 q5 ∷
   rw 29 q5 ∷
   rw 30 q5 ∷
   rw 31 q6 ∷
   rw 32 q5 ∷
   rw 33 q5 ∷
   rw 34 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1301 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23 X0]: 159 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌") (ℓ "丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 62 q1 ∷
   rw 61 q2 ∷
   rw⁻ 60 q5 ∷
   rw⁻ 59 q5 ∷
   rw⁻ 58 q6 ∷
   rw⁻ 57 q5 ∷
   rw⁻ 56 q5 ∷
   rw⁻ 55 q5 ∷
   re 54 1 (ℓ "乏个乏") ∷
   rw⁻ 56 q3 ∷
   rw 55 q7 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (ℓ "乀") ∷
   rw⁻ 53 q5 ∷
   rw⁻ 52 q5 ∷
   rw⁻ 51 q5 ∷
   rw⁻ 50 q5 ∷
   rw⁻ 49 q5 ∷
   rw⁻ 48 q5 ∷
   rw⁻ 47 q5 ∷
   rw⁻ 46 q5 ∷
   rw⁻ 45 q5 ∷
   rw⁻ 44 q8 ∷
   rw⁻ 43 q6 ∷
   rw⁻ 42 q5 ∷
   rw⁻ 41 q5 ∷
   rw⁻ 40 q5 ∷
   rw⁻ 39 q5 ∷
   rw⁻ 38 q5 ∷
   rw⁻ 37 q5 ∷
   re 36 1 (ℓ "乏个乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q7 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "乀") ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 23 q5 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q6 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q10 ∷
   rw 4 q10 ∷
   rw 3 q9 ∷
   rw 2 q10 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q18 ∷
   rw 0 q12 ∷
   rw 1 q14 ∷
   rw 2 q14 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 5 q14 ∷
   rw 6 q14 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q3 ∷
   rw 8 q16 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q5 ∷
   rw 9 q5 ∷
   rw 10 q5 ∷
   rw 11 q5 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q8 ∷
   rw 16 q5 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   rw 23 q5 ∷
   rw 24 q5 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q3 ∷
   rw 26 q16 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q5 ∷
   rw 27 q5 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q5 ∷
   rw 31 q5 ∷
   rw 32 q12 ∷
   rw 33 q14 ∷
   rw 34 q14 ∷
   rw 35 q15 ∷
   rw 36 q14 ∷
   rw 37 q15 ∷
   rw 38 q15 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q3 ∷
   rw 40 q16 ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "丰") ∷
   rw 40 q6 ∷
   rw 41 q8 ∷
   rw 42 q6 ∷
   rw 43 q8 ∷
   rw 44 q5 ∷
   rw 45 q5 ∷
   rw 46 q5 ∷
   rw 47 q6 ∷
   rw 48 q8 ∷
   rw 49 q5 ∷
   rw 50 q5 ∷
   rw 51 q5 ∷
   rw 52 q5 ∷
   rw 53 q5 ∷
   rw 54 q5 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 55 q3 ∷
   rw 56 q16 ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "丰") ∷
   rw 56 q5 ∷
   rw 57 q5 ∷
   rw 58 q6 ∷
   rw 59 q5 ∷
   rw 60 q6 ∷
   rw 61 q6 ∷
   rw 62 q17 ∷ []) Eq.refl
