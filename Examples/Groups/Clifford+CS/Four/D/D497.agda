{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D497 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q5 : Eqn
  q5 = wE 1257 W
  q6 : Eqn
  q6 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q8 : Eqn
  q8 = wE 107 W
  q9 : Eqn
  q9 = eqn (ℓ "两之") (ℓ "之两") (low-comm (CK₀₁) (CZ))
  q10 : Eqn
  q10 = wE 108 W
  q11 : Eqn
  q11 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q12 : Eqn
  q12 = wE 1258 W
  q13 : Eqn
  q13 = eqn (ℓ "丈丸") (ℓ "丸丈") (low₁-comm (S) (CZ))
  q14 : Eqn
  q14 = wE 1310 W
  q15 : Eqn
  q15 = wE 190 W
  q16 : Eqn
  q16 = wE 1260 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CZ12]: 391 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CZ12 : ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丸") ⟫ʷ ≈ ⟪ (ℓ "丸中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁") ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CZ12 = derive (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丸") (ℓ "丸中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁")
  (rw 29 q1 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   rw 22 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 16 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 11 q2 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 9 q2 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw 4 q2 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q5 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乁") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乁") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乁") ∷
   rw⁻ 6 q6 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丱") ∷
   rw⁻ 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丱") ∷
   rw⁻ 10 q7 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丱") ∷
   rw⁻ 15 q7 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q6 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丱") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丱") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丱") ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏丼两丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丿") ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q2 ∷
   re 29 5 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丼两丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丿") ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q2 ∷
   re 28 5 (ℓ "丱") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丿") ∷
   rw 29 q8 ∷
   rw 28 q11 ∷
   rw 27 q10 ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q2 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼两丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丿") ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q2 ∷
   re 26 5 (ℓ "丱") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丿") ∷
   rw 27 q8 ∷
   rw 26 q11 ∷
   rw 25 q10 ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q2 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丿") ∷
   rw 26 q8 ∷
   rw 25 q11 ∷
   rw 24 q10 ∷
   re 24 1 (ℓ "乏丸乏") ∷
   rw 23 q2 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q12 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丿") ∷
   rw 24 q8 ∷
   rw 23 q11 ∷
   rw 22 q10 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q2 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丿") ∷
   rw 23 q8 ∷
   rw 22 q11 ∷
   rw 21 q10 ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q2 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q8 ∷
   rw 21 q11 ∷
   rw 20 q10 ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q2 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丿") ∷
   rw 21 q8 ∷
   rw 20 q11 ∷
   rw 19 q10 ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q2 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丿") ∷
   rw 20 q8 ∷
   rw 19 q11 ∷
   rw 18 q10 ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q2 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丿") ∷
   rw 19 q8 ∷
   rw 18 q11 ∷
   rw 17 q10 ∷
   re 17 1 (ℓ "乏丸乏") ∷
   rw 16 q2 ∷
   re 17 5 (ℓ "中") ∷
   rw 15 q13 ∷
   re 14 1 (ℓ "乏丼两丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丿") ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q2 ∷
   re 15 5 (ℓ "丱") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丿") ∷
   rw 16 q8 ∷
   rw 15 q11 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q2 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q8 ∷
   rw 14 q11 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q2 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丿") ∷
   rw 14 q8 ∷
   rw 13 q11 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丸乏") ∷
   rw 11 q2 ∷
   re 12 5 (ℓ "中") ∷
   rw 10 q13 ∷
   re 9 1 (ℓ "乏丼两丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丿") ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   re 10 1 (ℓ "乏丸乏") ∷
   rw 9 q2 ∷
   re 10 5 (ℓ "丱") ∷
   rw 8 q13 ∷
   re 7 1 (ℓ "乏丼两丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丿") ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   re 8 1 (ℓ "乏丸乏") ∷
   rw 7 q2 ∷
   re 8 5 (ℓ "丱") ∷
   rw 6 q12 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q15 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q2 ∷
   re 28 1 (ℓ "乏丫乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丫乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q2 ∷
   rw 23 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q2 ∷
   rw 16 q7 ∷
   re 15 1 (ℓ "乏丫乏") ∷
   rw 17 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q2 ∷
   rw 11 q7 ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q2 ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏丫乏") ∷
   rw 10 q2 ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 8 q2 ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏为乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   rw 2 q16 ∷
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
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乁") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乁") ∷
   rw⁻ 16 q4 ∷
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
   rw 30 q2 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 1261 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CS01]: 111 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS01 : ⟪ (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丠") ⟫ʷ ≈ ⟪ (ℓ "丠中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁") ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS01 = derive (ℓ "中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁丠") (ℓ "丠中中丱中丱丱丣乁与乁与丽丽丽乁与丽丽丽丽丽丽丣丽丽乁丽乁乁")
  (rw 30 q1 ∷
   rw 29 q17 ∷
   re 28 1 (ℓ "乏为乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏为乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   rw 22 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏为乏") ∷
   rw 16 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏为乏") ∷
   rw 11 q2 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏为乏") ∷
   rw 9 q2 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丫乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丫乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丫乏") ∷
   rw 4 q2 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q18 ∷
   rw⁻ 0 q17 ∷
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
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乁") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乁") ∷
   rw⁻ 16 q4 ∷
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
   rw 30 q2 ∷ []) Eq.refl
