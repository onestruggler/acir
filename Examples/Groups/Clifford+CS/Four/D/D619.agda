{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD619 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D619 (W : Ws) (Sᴰ : SD619) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 : St 1405
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-TOFF201-X0 : St 1406
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-TOFF201-X0 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : St 1407
  lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : St 1408
  lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 335 W
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 1294 W
  q7 : Eqn
  q7 = wE 368 W
  q8 : Eqn
  q8 = wE 1855 W
  q9 : Eqn
  q9 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q10 : Eqn
  q10 = wE 336 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = wE 1106 W
  q13 : Eqn
  q13 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 74 W
  q17 : Eqn
  q17 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 772 W
  q20 : Eqn
  q20 = wE 1859 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 329 W
  q23 : Eqn
  q23 = wE 30 W
  q24 : Eqn
  q24 = wE 317 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = sE 1405 lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0
  q27 : Eqn
  q27 = wE 1860 W
  q28 : Eqn
  q28 = wE 1858 W

-- pass [TOFF301] [X0 CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23 X0]: 293 steps
lem-pass-TOFF301-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : ⟪ (ℓ "书丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌书") ⟫ʷ
lem-pass-TOFF301-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = derive (ℓ "书丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌") (ℓ "丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌书")
  (rw 1 q1 ∷
   re 0 1 (ℓ "乏乣乏") ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 8 q5 ∷
   rw 7 q4 ∷
   rw 6 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 2 q3 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   re 1 8 (ℓ "乣") ∷
   rw 1 q8 ∷
   rw⁻ 0 q9 ∷
   rw⁻ 1 q9 ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q1 ∷
   rw 3 q10 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 9 q10 ∷
   rw⁻ 10 q4 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "乣") ∷
   re 2 3 (ℓ "书") ∷
   rw⁻ 3 q9 ∷
   rw⁻ 4 q9 ∷
   rw 5 q5 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 35 q13 ∷
   rw⁻ 34 q14 ∷
   rw⁻ 33 q13 ∷
   rw⁻ 32 q13 ∷
   rw⁻ 31 q13 ∷
   re 30 1 (ℓ "乏个乏") ∷
   rw⁻ 32 q15 ∷
   rw 31 q16 ∷
   rw⁻ 30 q15 ∷
   re 31 3 (ℓ "乀") ∷
   rw⁻ 29 q13 ∷
   rw⁻ 28 q13 ∷
   rw⁻ 27 q13 ∷
   rw⁻ 26 q13 ∷
   rw⁻ 25 q13 ∷
   rw⁻ 24 q13 ∷
   rw⁻ 23 q13 ∷
   rw⁻ 22 q13 ∷
   rw⁻ 21 q13 ∷
   rw⁻ 20 q17 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 15 q13 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 13 q13 ∷
   re 12 1 (ℓ "乏个乏") ∷
   rw⁻ 14 q15 ∷
   rw 13 q16 ∷
   rw⁻ 12 q15 ∷
   re 13 3 (ℓ "乀") ∷
   rw 11 q18 ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   rw 8 q18 ∷
   rw 7 q18 ∷
   rw 6 q18 ∷
   rw 5 q12 ∷
   rw 4 q12 ∷
   rw 5 q20 ∷
   rw 4 q21 ∷
   rw 5 q21 ∷
   rw 6 q21 ∷
   rw 7 q22 ∷
   rw 8 q21 ∷
   rw 9 q21 ∷
   re 11 1 (ℓ "乏丹乏") ∷
   rw 10 q15 ∷
   rw 11 q23 ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "丰") ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q13 ∷
   rw 15 q13 ∷
   rw 16 q13 ∷
   rw 17 q14 ∷
   rw 18 q17 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   rw 22 q13 ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q13 ∷
   rw 26 q13 ∷
   rw 27 q13 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q15 ∷
   rw 29 q23 ∷
   rw 30 q15 ∷
   re 28 3 (ℓ "丰") ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q13 ∷
   rw 34 q13 ∷
   rw 35 q24 ∷
   rw 36 q25 ∷
   rw⁻ 1 q26 ∷
   rw 32 q11 ∷
   rw⁻ 31 q13 ∷
   rw⁻ 30 q13 ∷
   rw⁻ 29 q14 ∷
   rw⁻ 28 q13 ∷
   rw⁻ 27 q13 ∷
   rw⁻ 26 q13 ∷
   re 25 1 (ℓ "乏个乏") ∷
   rw⁻ 27 q15 ∷
   rw 26 q16 ∷
   rw⁻ 25 q15 ∷
   re 26 3 (ℓ "乀") ∷
   rw⁻ 24 q13 ∷
   rw⁻ 23 q13 ∷
   rw⁻ 22 q13 ∷
   rw⁻ 21 q13 ∷
   rw⁻ 20 q13 ∷
   rw⁻ 19 q13 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 15 q17 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q13 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 8 q13 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw⁻ 9 q15 ∷
   rw 8 q16 ∷
   rw⁻ 7 q15 ∷
   re 8 3 (ℓ "乀") ∷
   rw 6 q18 ∷
   rw 5 q18 ∷
   rw 4 q19 ∷
   rw 3 q18 ∷
   rw 2 q18 ∷
   rw 1 q18 ∷
   rw 0 q12 ∷
   rw 1 q27 ∷
   rw 0 q24 ∷
   rw 1 q21 ∷
   rw 2 q21 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q21 ∷
   rw 6 q21 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q15 ∷
   rw 8 q23 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q13 ∷
   rw 9 q13 ∷
   rw 10 q13 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q17 ∷
   rw 16 q13 ∷
   rw 17 q13 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   rw 22 q13 ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q15 ∷
   rw 26 q23 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q13 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q24 ∷
   rw 33 q24 ∷
   rw 34 q25 ∷
   rw 38 q1 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   re 35 1 (ℓ "乏乣乏") ∷
   re 36 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "丽") ∷
   rw⁻ 37 q3 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "举") ∷
   rw⁻ 39 q3 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q2 ∷
   rw⁻ 42 q4 ∷
   rw 43 q5 ∷
   rw 42 q4 ∷
   rw 41 q6 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   rw 39 q3 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 40 q5 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw 35 q6 ∷
   rw 36 q7 ∷
   re 36 8 (ℓ "乣") ∷
   rw 34 q9 ∷
   rw 33 q9 ∷
   rw 34 q28 ∷
   re 34 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q3 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q3 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q2 ∷
   rw⁻ 40 q4 ∷
   rw 33 q1 ∷
   rw 34 q10 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw⁻ 36 q3 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q5 ∷
   rw⁻ 38 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   rw 40 q10 ∷
   rw⁻ 41 q4 ∷
   rw 34 q7 ∷
   re 34 8 (ℓ "乣") ∷
   re 33 3 (ℓ "书") ∷
   rw 34 q5 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 1407 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0

-- Bar(SSKSKK;0,2->3) passes factors of X0 CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13 X0: 1 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-factors-of-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : ⟪ (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") ⟫ʷ ≈ ⟪ (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍") ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-factors-of-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = derive (ℓ "中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌中中丱中丱丱个乍且乍且义义义乍且义义义义义义个义义乍义乍乍")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q31 : Eqn
  q31 = wE 1856 W
  q32 : Eqn
  q32 = sE 1406 lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-TOFF201-X0
  q33 : Eqn
  q33 = wE 1857 W

-- pass [TOFF201] [X0 CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13 X0]: 229 steps
lem-pass-TOFF201-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : ⟪ (ℓ "乣丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") ⟫ʷ ≈ ⟪ (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌乣") ⟫ʷ
lem-pass-TOFF201-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = derive (ℓ "乣丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌乣")
  (rw 0 q8 ∷
   rw 36 q1 ∷
   rw 35 q9 ∷
   re 34 1 (ℓ "乏为乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏为乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏为乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q5 ∷
   rw 28 q3 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   rw 21 q30 ∷
   re 20 1 (ℓ "乏为乏") ∷
   rw 22 q5 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q5 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q5 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   rw 16 q30 ∷
   re 15 1 (ℓ "乏为乏") ∷
   rw 17 q5 ∷
   rw 14 q30 ∷
   re 13 1 (ℓ "乏为乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丫乏") ∷
   rw 13 q5 ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   re 8 1 (ℓ "乏丫乏") ∷
   rw 10 q5 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 5 q31 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丱") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丱") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丱") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乁") ∷
   rw⁻ 12 q30 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乁") ∷
   rw⁻ 14 q30 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乁") ∷
   rw⁻ 19 q30 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw⁻ 26 q3 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乁") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乁") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乁") ∷
   rw⁻ 33 q9 ∷
   rw 34 q5 ∷
   rw⁻ 1 q32 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏为乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏为乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q5 ∷
   rw 23 q3 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q5 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q5 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q5 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q5 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   rw 16 q30 ∷
   re 15 1 (ℓ "乏为乏") ∷
   rw 17 q5 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q5 ∷
   rw 11 q30 ∷
   re 10 1 (ℓ "乏为乏") ∷
   rw 12 q5 ∷
   rw 9 q30 ∷
   re 8 1 (ℓ "乏为乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丫乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏丫乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   rw 0 q9 ∷
   rw 1 q33 ∷
   rw⁻ 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丱") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丱") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丱") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乁") ∷
   rw⁻ 9 q30 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乁") ∷
   rw⁻ 11 q30 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乁") ∷
   rw⁻ 16 q30 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw⁻ 23 q3 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乁") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乁") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乁") ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q9 ∷
   rw 32 q5 ∷
   rw 31 q28 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1408 lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0

-- Bar(SSSKSS;0,2->3) passes factors of X0 CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13 X0: 1 steps
lem-Bar⟨SSSKSS02-⟶3⟩-passes-factors-of-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : ⟪ (ℓ "中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") ⟫ʷ ≈ ⟪ (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义") ⟫ʷ
lem-Bar⟨SSSKSS02-⟶3⟩-passes-factors-of-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = derive (ℓ "中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌") (ℓ "丌中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丌中中中丱中中个义义义义义义乍且义义义义义义义义义个义义义乍义义")
  (rw 0 q34 ∷ []) Eq.refl
