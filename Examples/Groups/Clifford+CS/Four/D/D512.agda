{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD512 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D512 (W : Ws) (Sᴰ : SD512) where

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
  lem-pass-CCZ013-vs-CZ13 : St 58
  lem-pass-CCZ013-vs-CZ13 = pickᴰ 0 Sᴰ
  lem-pass-CS02-vs-CS03 : St 59
  lem-pass-CS02-vs-CS03 = pickᴰ 1 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CCZ013-vs-CS13 : St 61
  lem-pass-CCZ013-vs-CS13 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 1362 W
  q9 : Eqn
  q9 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q10 : Eqn
  q10 = wE 1363 W
  q11 : Eqn
  q11 = wE 43 W
  q12 : Eqn
  q12 = wE 466 W
  q13 : Eqn
  q13 = wE 90 W
  q14 : Eqn
  q14 = wE 469 W
  q15 : Eqn
  q15 = wE 1364 W
  q16 : Eqn
  q16 = wE 175 W
  q17 : Eqn
  q17 = sE 61 lem-pass-CCZ013-vs-CS13
  q18 : Eqn
  q18 = sE 58 lem-pass-CCZ013-vs-CZ13
  q19 : Eqn
  q19 = wE 1365 W
  q20 : Eqn
  q20 = wE 32 W
  q21 : Eqn
  q21 = sE 59 lem-pass-CS02-vs-CS03
  q22 : Eqn
  q22 = sE 60 lem-pass-CSd02-vs-CS03

-- pass [CS03] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 894 steps
lem-pass-CS03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (ℓ "中丞乞丞丧丞乞丞丨") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丧丞乞丞丨中") ⟫ʷ
lem-pass-CS03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (ℓ "中丞乞丞丧丞乞丞丨") (ℓ "丞乞丞丧丞乞丞丨中")
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q9 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 4 q11 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q6 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 12 q6 ∷
   rw 11 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 4 q3 ∷
   rw 5 q7 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 4 q11 ∷
   re 4 5 (ℓ "乙") ∷
   rw 4 q12 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q1 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丿") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 6 q11 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw 6 q6 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 3 q13 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q6 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q6 ∷
   rw 2 q14 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 5 q11 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q6 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q9 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q16 ∷
   rw 3 q6 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 4 q19 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 6 q11 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 5 q11 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q20 ∷
   rw 4 q6 ∷
   rw⁻ 3 q21 ∷
   rw 8 q1 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q2 ∷
   rw 6 q8 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 7 q6 ∷
   rw 6 q1 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 5 q10 ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw 8 q11 ∷
   re 8 5 (ℓ "乙") ∷
   re 7 3 (ℓ "乚") ∷
   rw 8 q6 ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q4 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw 16 q6 ∷
   rw 15 q5 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   rw 12 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q6 ∷
   rw 8 q3 ∷
   rw 9 q7 ∷
   re 9 8 (ℓ "九") ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 8 q11 ∷
   re 8 5 (ℓ "乙") ∷
   rw 8 q12 ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q1 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw 8 q7 ∷
   re 8 8 (ℓ "九") ∷
   re 7 3 (ℓ "乞") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丿") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q4 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q6 ∷
   rw⁻ 13 q4 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   rw 10 q11 ∷
   re 10 5 (ℓ "乙") ∷
   re 9 3 (ℓ "乚") ∷
   rw 10 q6 ∷
   rw 8 q1 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 7 q3 ∷
   rw 8 q7 ∷
   re 8 8 (ℓ "九") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 7 q13 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q6 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 6 q14 ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   re 9 1 (ℓ "丶丣丷丣丧") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 9 q11 ∷
   re 9 5 (ℓ "乙") ∷
   re 8 3 (ℓ "乚") ∷
   rw 9 q6 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw 6 q16 ∷
   rw 7 q6 ∷
   rw 9 q17 ∷
   rw 10 q18 ∷
   rw 8 q19 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q4 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   rw 12 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q6 ∷
   rw 10 q11 ∷
   re 10 5 (ℓ "乙") ∷
   re 8 1 (ℓ "乏乙乏") ∷
   re 9 1 (ℓ "丶丣丷丣丧") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 9 q11 ∷
   re 9 5 (ℓ "乙") ∷
   rw 9 q20 ∷
   rw 8 q6 ∷
   rw⁻ 7 q22 ∷ []) Eq.refl
