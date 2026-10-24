{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D498 (W : Ws) where

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
  q1 = wE 1052 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q3 : Eqn
  q3 = wE 1053 W
  q4 : Eqn
  q4 = wE 65 W
  q5 : Eqn
  q5 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q6 : Eqn
  q6 = wE 48 W
  q7 : Eqn
  q7 = wE 1262 W
  q8 : Eqn
  q8 = wE 1263 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 772 W
  q13 : Eqn
  q13 = wE 1311 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 101 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CS02]: 185 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS02 : ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丧") ⟫ʷ ≈ ⟪ (ℓ "丧中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁") ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS02 = derive (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丧") (ℓ "丧中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁")
  (re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q1 ∷
   rw⁻ 29 q2 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "丧") ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "丧") ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q4 ∷
   rw⁻ 25 q5 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "丧") ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "丧") ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q4 ∷
   rw⁻ 22 q5 ∷
   rw 23 q6 ∷
   re 21 3 (ℓ "丧") ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q4 ∷
   rw⁻ 21 q5 ∷
   rw 22 q6 ∷
   re 20 3 (ℓ "丧") ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q4 ∷
   rw⁻ 20 q5 ∷
   rw 21 q6 ∷
   re 19 3 (ℓ "丧") ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q4 ∷
   rw⁻ 19 q5 ∷
   rw 20 q6 ∷
   re 18 3 (ℓ "丧") ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q4 ∷
   rw⁻ 18 q5 ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "丧") ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q4 ∷
   rw⁻ 17 q5 ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "丧") ∷
   rw 15 q8 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "丧") ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q4 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "丧") ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q4 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "丧") ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q4 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "丧") ∷
   rw 10 q8 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "丧") ∷
   rw 8 q8 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丧") ∷
   rw 6 q7 ∷
   rw 7 q9 ∷
   rw 6 q10 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (ℓ "乁") ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 6 q11 ∷
   rw 7 q15 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "丱") ∷
   rw 7 q16 ∷
   rw 6 q9 ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (ℓ "乁") ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 5 q11 ∷
   rw 6 q15 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "丱") ∷
   rw 6 q16 ∷
   rw 5 q9 ∷
   rw 4 q10 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q11 ∷
   rw 4 q10 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw 5 q14 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q16 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (ℓ "乁") ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏为乏") ∷
   rw 3 q11 ∷
   rw 4 q15 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "丱") ∷
   rw 4 q16 ∷
   rw 3 q9 ∷
   rw 2 q10 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q11 ∷
   rw 2 q10 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q11 ∷
   rw 3 q14 ∷
   rw 4 q11 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q16 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q11 ∷
   rw 1 q10 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q17 ∷
   rw 0 q14 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q11 ∷
   rw 2 q14 ∷
   rw 3 q11 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q21 : Eqn
  q21 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q22 : Eqn
  q22 = wE 1257 W
  q23 : Eqn
  q23 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q24 : Eqn
  q24 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q25 : Eqn
  q25 = wE 157 W
  q26 : Eqn
  q26 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q27 : Eqn
  q27 = wE 158 W
  q28 : Eqn
  q28 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q29 : Eqn
  q29 = wE 1265 W
  q30 : Eqn
  q30 = eqn (ℓ "丈丹") (ℓ "丹丈") (low₁-comm (S) (CX₀₁))
  q31 : Eqn
  q31 = wE 1312 W
  q32 : Eqn
  q32 = wE 66 W
  q33 : Eqn
  q33 = wE 1260 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CX12]: 391 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CX12 : ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丹") ⟫ʷ ≈ ⟪ (ℓ "丹中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁") ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CX12 = derive (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丹") (ℓ "丹中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁")
  (rw 29 q18 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 30 q19 ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 29 q19 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q19 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 27 q19 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q19 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q19 ∷
   rw 22 q20 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q19 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q19 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q19 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q19 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q19 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q19 ∷
   rw 15 q21 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 16 q19 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q19 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q19 ∷
   rw 10 q21 ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 11 q19 ∷
   rw 8 q21 ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 9 q19 ∷
   rw 6 q20 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw 7 q19 ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw 6 q19 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q19 ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw 4 q19 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q19 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q19 ∷
   rw 1 q22 ∷
   rw 2 q18 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "乁") ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "乁") ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "乁") ∷
   rw⁻ 6 q23 ∷
   rw 9 q18 ∷
   re 7 3 (ℓ "丱") ∷
   rw⁻ 8 q24 ∷
   rw 11 q18 ∷
   re 9 3 (ℓ "丱") ∷
   rw⁻ 10 q24 ∷
   rw 13 q18 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q18 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q18 ∷
   re 14 3 (ℓ "丱") ∷
   rw⁻ 15 q24 ∷
   rw 18 q18 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q18 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q18 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q18 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q18 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q23 ∷
   rw 25 q18 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q18 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q18 ∷
   re 25 3 (ℓ "丱") ∷
   rw 28 q18 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q18 ∷
   re 27 3 (ℓ "丱") ∷
   rw 30 q18 ∷
   re 28 3 (ℓ "丱") ∷
   rw 29 q19 ∷
   re 28 1 (ℓ "乏丼两丼乏") ∷
   rw 34 q18 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q25 ∷
   rw 30 q26 ∷
   rw 29 q27 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q19 ∷
   re 29 5 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丼两丼乏") ∷
   rw 33 q18 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q25 ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q19 ∷
   re 28 5 (ℓ "丱") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q18 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q25 ∷
   rw 28 q28 ∷
   rw 27 q27 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q19 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼两丼乏") ∷
   rw 31 q18 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q25 ∷
   rw 27 q26 ∷
   rw 26 q27 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q19 ∷
   re 26 5 (ℓ "丱") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q18 ∷
   re 28 3 (ℓ "乀") ∷
   rw 27 q25 ∷
   rw 26 q28 ∷
   rw 25 q27 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q19 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q18 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q25 ∷
   rw 25 q28 ∷
   rw 24 q27 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q19 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q29 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q18 ∷
   re 25 3 (ℓ "乀") ∷
   rw 24 q25 ∷
   rw 23 q28 ∷
   rw 22 q27 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 21 q19 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q18 ∷
   re 24 3 (ℓ "乀") ∷
   rw 23 q25 ∷
   rw 22 q28 ∷
   rw 21 q27 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 20 q19 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q18 ∷
   re 23 3 (ℓ "乀") ∷
   rw 22 q25 ∷
   rw 21 q28 ∷
   rw 20 q27 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 19 q19 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q18 ∷
   re 22 3 (ℓ "乀") ∷
   rw 21 q25 ∷
   rw 20 q28 ∷
   rw 19 q27 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 18 q19 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q18 ∷
   re 21 3 (ℓ "乀") ∷
   rw 20 q25 ∷
   rw 19 q28 ∷
   rw 18 q27 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 17 q19 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q18 ∷
   re 20 3 (ℓ "乀") ∷
   rw 19 q25 ∷
   rw 18 q28 ∷
   rw 17 q27 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q19 ∷
   re 17 5 (ℓ "中") ∷
   rw 15 q30 ∷
   re 14 1 (ℓ "乏丼两丼乏") ∷
   rw 20 q18 ∷
   re 18 3 (ℓ "乀") ∷
   rw 17 q25 ∷
   rw 16 q26 ∷
   rw 15 q27 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 14 q19 ∷
   re 15 5 (ℓ "丱") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "乀") ∷
   rw 16 q25 ∷
   rw 15 q28 ∷
   rw 14 q27 ∷
   re 14 1 (ℓ "乏丹乏") ∷
   rw 13 q19 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q18 ∷
   re 16 3 (ℓ "乀") ∷
   rw 15 q25 ∷
   rw 14 q28 ∷
   rw 13 q27 ∷
   re 13 1 (ℓ "乏丹乏") ∷
   rw 12 q19 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q18 ∷
   re 15 3 (ℓ "乀") ∷
   rw 14 q25 ∷
   rw 13 q28 ∷
   rw 12 q27 ∷
   re 12 1 (ℓ "乏丹乏") ∷
   rw 11 q19 ∷
   re 12 5 (ℓ "中") ∷
   rw 10 q30 ∷
   re 9 1 (ℓ "乏丼两丼乏") ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "乀") ∷
   rw 12 q25 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q19 ∷
   re 10 5 (ℓ "丱") ∷
   rw 8 q30 ∷
   re 7 1 (ℓ "乏丼两丼乏") ∷
   rw 13 q18 ∷
   re 11 3 (ℓ "乀") ∷
   rw 10 q25 ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q19 ∷
   re 8 5 (ℓ "丱") ∷
   rw 6 q29 ∷
   rw 5 q31 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 30 q18 ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q19 ∷
   re 28 1 (ℓ "乏丫乏") ∷
   rw 30 q19 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q19 ∷
   re 26 1 (ℓ "乏丫乏") ∷
   rw 28 q19 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q19 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q19 ∷
   rw 23 q23 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q19 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q19 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q19 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q19 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q19 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q19 ∷
   rw 16 q24 ∷
   re 15 1 (ℓ "乏丫乏") ∷
   rw 17 q19 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q19 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q19 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q19 ∷
   rw 11 q24 ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q19 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丫乏") ∷
   rw 10 q19 ∷
   rw 7 q23 ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 8 q19 ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 7 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   re 3 1 (ℓ "乏为乏") ∷
   rw 5 q19 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q19 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q19 ∷
   rw 2 q33 ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "丱") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "丱") ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "丱") ∷
   rw⁻ 7 q20 ∷
   rw 10 q18 ∷
   re 8 3 (ℓ "乁") ∷
   rw⁻ 9 q21 ∷
   rw 12 q18 ∷
   re 10 3 (ℓ "乁") ∷
   rw⁻ 11 q21 ∷
   rw 14 q18 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q18 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q18 ∷
   re 15 3 (ℓ "乁") ∷
   rw⁻ 16 q21 ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q18 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q18 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q18 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q18 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q18 ∷
   re 22 3 (ℓ "丽") ∷
   rw⁻ 23 q20 ∷
   rw 26 q18 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q18 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q18 ∷
   re 26 3 (ℓ "乁") ∷
   rw 29 q18 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q18 ∷
   re 28 3 (ℓ "乁") ∷
   rw 31 q18 ∷
   re 29 3 (ℓ "乁") ∷
   rw 30 q19 ∷ []) Eq.refl
