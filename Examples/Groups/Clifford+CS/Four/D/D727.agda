{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD727 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D727 (W : Ws) (Sᴰ : SD727) where

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
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 : St 2199
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 56 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 2016 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q11 : Eqn
  q11 = eqn (ℓ "丨丞") (ℓ "丞丨") (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q12 : Eqn
  q12 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = wE 2019 W
  q14 : Eqn
  q14 = wE 1049 W
  q15 : Eqn
  q15 = wE 1051 W
  q16 : Eqn
  q16 = sE 2199 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02
  q17 : Eqn
  q17 = wE 2020 W
  q18 : Eqn
  q18 = wE 2021 W

-- pass [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3] [TOFF013 CS02 TOFF013 CSd02]: 513 steps
lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丒丞习丽习举丒丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丒丞习丽习举丒丞") ⟫ʷ
lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丒丞习丽习举丒丞乞丧乞丨") (ℓ "乞丧乞丨丒丞习丽习举丒丞")
  (rw 9 q1 ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (ℓ "九") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (ℓ "九") ∷
   re 8 3 (ℓ "乞") ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q10 ∷
   rw 13 q1 ∷
   re 12 1 (ℓ "乏九乏") ∷
   re 13 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 20 q5 ∷
   rw 19 q4 ∷
   rw 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q5 ∷
   rw 12 q2 ∷
   rw 13 q6 ∷
   re 13 8 (ℓ "九") ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   re 13 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q4 ∷
   rw 13 q6 ∷
   re 13 8 (ℓ "九") ∷
   re 12 3 (ℓ "乞") ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q5 ∷
   rw⁻ 14 q11 ∷
   rw 10 q1 ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (ℓ "九") ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw⁻ 6 q12 ∷
   rw 7 q9 ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (ℓ "九") ∷
   re 8 3 (ℓ "乞") ∷
   rw⁻ 9 q12 ∷
   rw 10 q9 ∷
   rw⁻ 11 q12 ∷
   rw 12 q5 ∷
   rw 11 q14 ∷
   rw 16 q1 ∷
   rw 15 q7 ∷
   re 14 1 (ℓ "乏九乏") ∷
   re 15 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 22 q5 ∷
   rw 21 q4 ∷
   rw 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q5 ∷
   rw 14 q2 ∷
   rw 15 q6 ∷
   re 15 8 (ℓ "九") ∷
   rw 13 q7 ∷
   rw 12 q12 ∷
   rw 13 q13 ∷
   rw⁻ 12 q12 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q5 ∷
   rw⁻ 19 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 22 q4 ∷
   rw 15 q6 ∷
   re 15 8 (ℓ "九") ∷
   re 14 3 (ℓ "乞") ∷
   rw⁻ 15 q12 ∷
   rw 16 q9 ∷
   rw⁻ 17 q12 ∷
   rw 18 q5 ∷
   rw 17 q15 ∷
   rw 2 q16 ∷
   rw 7 q1 ∷
   rw 6 q7 ∷
   rw 5 q12 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q2 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "九") ∷
   rw 3 q7 ∷
   rw 2 q12 ∷
   rw 1 q7 ∷
   rw 2 q17 ∷
   rw⁻ 1 q12 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q12 ∷
   rw 4 q9 ∷
   rw 5 q5 ∷
   rw⁻ 4 q10 ∷
   rw 11 q1 ∷
   rw 10 q7 ∷
   rw 9 q12 ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (ℓ "九") ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   rw⁻ 5 q12 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q2 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q4 ∷
   rw 6 q1 ∷
   rw⁻ 7 q2 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q4 ∷
   rw 7 q6 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw⁻ 7 q12 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   rw⁻ 8 q11 ∷
   rw 4 q1 ∷
   rw 3 q12 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 10 q5 ∷
   rw 9 q4 ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 2 q2 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q12 ∷
   rw 0 q12 ∷
   rw 1 q18 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q12 ∷
   rw 2 q5 ∷
   rw 1 q14 ∷
   rw 6 q1 ∷
   rw 5 q12 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q2 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "九") ∷
   rw 3 q12 ∷
   rw 2 q12 ∷
   rw 3 q18 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q12 ∷
   rw 4 q5 ∷
   rw 3 q15 ∷ []) Eq.refl
