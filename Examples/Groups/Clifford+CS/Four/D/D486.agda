{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D486 (W : Ws) where

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
  q1 = eqn (ℓ "両乗") (ℓ "乗両") (low-comm ((CS • CS • CS)) (CK₁₀))
  q2 : Eqn
  q2 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 1291 W
  q7 : Eqn
  q7 = eqn (ℓ "両业") (ℓ "业両") (low-comm ((CS • CS • CS)) ((S ↑)))
  q8 : Eqn
  q8 = wE 1292 W
  q9 : Eqn
  q9 = wE 246 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CSd01]: 45 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CSd01 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗両") ⟫ʷ ≈ ⟪ (ℓ "両丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CSd01 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗両") (ℓ "両丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw⁻ 28 q1 ∷
   rw⁻ 27 q1 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw⁻ 22 q4 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q5 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q1 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q1 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw⁻ 6 q4 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q5 ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q9 ∷
   rw 2 q8 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = wE 1106 W
  q12 : Eqn
  q12 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 1228 W
  q14 : Eqn
  q14 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q15 : Eqn
  q15 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = wE 74 W
  q17 : Eqn
  q17 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 772 W
  q19 : Eqn
  q19 = wE 7 W
  q20 : Eqn
  q20 = wE 1293 W
  q21 : Eqn
  q21 = wE 317 W
  q22 : Eqn
  q22 = wE 330 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 329 W
  q25 : Eqn
  q25 = wE 30 W
  q26 : Eqn
  q26 = wE 31 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CKd03 X0]: 91 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CKd03-X0 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌串丌") ⟫ʷ ≈ ⟪ (ℓ "丌串丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CKd03-X0 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌串丌") (ℓ "丌串丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 32 q10 ∷
   rw 31 q11 ∷
   re 30 1 (ℓ "乏丬乏") ∷
   rw⁻ 32 q12 ∷
   rw 31 q13 ∷
   rw⁻ 30 q12 ∷
   re 31 3 (ℓ "乂") ∷
   rw 29 q11 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q15 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q12 ∷
   rw 23 q16 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (ℓ "乀") ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q17 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q17 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q12 ∷
   rw 7 q16 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q18 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   re 2 1 (ℓ "乏主乏") ∷
   rw 1 q12 ∷
   rw 2 q22 ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "串") ∷
   rw 2 q21 ∷
   rw 3 q23 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 8 q24 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q12 ∷
   rw 10 q25 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丰") ∷
   rw 10 q14 ∷
   rw 11 q17 ∷
   rw 12 q14 ∷
   rw 13 q17 ∷
   rw 14 q15 ∷
   rw 15 q15 ∷
   rw 16 q15 ∷
   rw 17 q14 ∷
   rw 18 q17 ∷
   rw 19 q15 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q15 ∷
   rw 24 q15 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q12 ∷
   rw 26 q25 ∷
   rw 27 q12 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q15 ∷
   rw 27 q15 ∷
   rw 28 q14 ∷
   rw 29 q15 ∷
   rw 30 q14 ∷
   rw 31 q14 ∷
   rw 32 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 335 W
  q29 : Eqn
  q29 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q30 : Eqn
  q30 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q31 : Eqn
  q31 = wE 1294 W
  q32 : Eqn
  q32 = wE 368 W
  q33 : Eqn
  q33 = wE 1295 W
  q34 : Eqn
  q34 = wE 336 W

-- pass [TOFF301] [X0 TOFF301 X0]: 115 steps
lem-pass-TOFF301-vs-X0-TOFF301-X0 : ⟪ (ℓ "书丌书丌") ⟫ʷ ≈ ⟪ (ℓ "丌书丌书") ⟫ʷ
lem-pass-TOFF301-vs-X0-TOFF301-X0 = derive (ℓ "书丌书丌") (ℓ "丌书丌书")
  (rw 4 q3 ∷
   rw 3 q27 ∷
   re 2 1 (ℓ "乏乣乏") ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 2 q28 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q29 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q29 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q28 ∷
   rw⁻ 9 q30 ∷
   rw 10 q5 ∷
   rw 9 q30 ∷
   rw 8 q31 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 6 q29 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw 4 q29 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 2 q31 ∷
   rw 3 q32 ∷
   re 3 8 (ℓ "乣") ∷
   rw 1 q27 ∷
   re 0 1 (ℓ "乏乣乏") ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q28 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q29 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q29 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q28 ∷
   rw⁻ 7 q30 ∷
   rw 8 q5 ∷
   rw 7 q30 ∷
   rw 6 q31 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 4 q29 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 2 q29 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   re 1 8 (ℓ "乣") ∷
   rw 1 q33 ∷
   rw⁻ 0 q27 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q28 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q29 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q29 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q28 ∷
   rw⁻ 8 q30 ∷
   rw 1 q3 ∷
   rw 2 q34 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q29 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q29 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 8 q34 ∷
   rw⁻ 9 q30 ∷
   rw 2 q32 ∷
   re 2 8 (ℓ "乣") ∷
   re 1 3 (ℓ "书") ∷
   rw⁻ 2 q27 ∷
   re 4 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 3 q28 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q29 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q29 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q28 ∷
   rw⁻ 10 q30 ∷
   rw 3 q3 ∷
   rw 4 q34 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q29 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q29 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 10 q34 ∷
   rw⁻ 11 q30 ∷
   rw 4 q32 ∷
   re 4 8 (ℓ "乣") ∷
   re 3 3 (ℓ "书") ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1296 W

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 CK03 X0]: 95 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丱丌") ⟫ʷ ≈ ⟪ (ℓ "丌丱丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CK03-X0 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丱丌") (ℓ "丌丱丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 34 q10 ∷
   rw 33 q11 ∷
   re 32 1 (ℓ "乏丫乏") ∷
   rw⁻ 34 q12 ∷
   rw 33 q18 ∷
   rw⁻ 32 q12 ∷
   re 33 3 (ℓ "乁") ∷
   rw 31 q11 ∷
   rw⁻ 30 q15 ∷
   rw⁻ 29 q15 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q15 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q15 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q12 ∷
   rw 25 q16 ∷
   rw⁻ 24 q12 ∷
   re 25 3 (ℓ "乀") ∷
   rw⁻ 23 q15 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 13 q14 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q15 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q12 ∷
   rw 7 q16 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (ℓ "乀") ∷
   rw 5 q19 ∷
   rw 4 q19 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 1 q35 ∷
   rw 0 q21 ∷
   re 2 1 (ℓ "乏为乏") ∷
   rw 1 q12 ∷
   rw 2 q24 ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "丱") ∷
   rw 2 q21 ∷
   rw 3 q23 ∷
   rw 4 q23 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw 7 q23 ∷
   rw 8 q23 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q12 ∷
   rw 10 q25 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丰") ∷
   rw 10 q15 ∷
   rw 11 q15 ∷
   rw 12 q15 ∷
   rw 13 q15 ∷
   rw 14 q15 ∷
   rw 15 q15 ∷
   rw 16 q14 ∷
   rw 17 q17 ∷
   rw 18 q15 ∷
   rw 19 q15 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q15 ∷
   rw 24 q15 ∷
   rw 25 q15 ∷
   rw 26 q15 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q12 ∷
   rw 28 q25 ∷
   rw 29 q12 ∷
   re 27 3 (ℓ "丰") ∷
   rw 28 q15 ∷
   rw 29 q15 ∷
   rw 30 q15 ∷
   rw 31 q14 ∷
   rw 32 q15 ∷
   rw 33 q15 ∷
   rw 34 q26 ∷ []) Eq.refl
