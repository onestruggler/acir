{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD518 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D518 (W : Ws) (Sᴰ : SD518) where

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
  lem-pass-CCZ013-vs-CSd13 : St 175
  lem-pass-CCZ013-vs-CSd13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ013-vs-CZ13 : St 58
  lem-pass-CCZ013-vs-CZ13 = pickᴰ 1 Sᴰ
  lem-pass-CS02-vs-CS03 : St 59
  lem-pass-CS02-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-Sd0-vs-CS03 : St 176
  lem-pass-Sd0-vs-CS03 = pickᴰ 3 Sᴰ
  lem-pass-CS23-vs-S0 : St 177
  lem-pass-CS23-vs-S0 = pickᴰ 4 Sᴰ
  lem-comm-CCZ012-CZ03 : St 178
  lem-comm-CCZ012-CZ03 = pickᴰ 5 Sᴰ
  lem-pass-S0-vs-CSd23 : St 179
  lem-pass-S0-vs-CSd23 = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 43 W
  q5 : Eqn
  q5 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 467 W
  q9 : Eqn
  q9 = wE 468 W
  q10 : Eqn
  q10 = wE 469 W
  q11 : Eqn
  q11 = wE 689 W
  q12 : Eqn
  q12 = wE 1384 W
  q13 : Eqn
  q13 = wE 153 W
  q14 : Eqn
  q14 = wE 464 W
  q15 : Eqn
  q15 = wE 1385 W
  q16 : Eqn
  q16 = wE 151 W
  q17 : Eqn
  q17 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q19 : Eqn
  q19 = wE 1386 W
  q20 : Eqn
  q20 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q21 : Eqn
  q21 = wE 175 W
  q22 : Eqn
  q22 = sE 175 lem-pass-CCZ013-vs-CSd13
  q23 : Eqn
  q23 = sE 58 lem-pass-CCZ013-vs-CZ13
  q24 : Eqn
  q24 = wE 154 W
  q25 : Eqn
  q25 = wE 1387 W
  q26 : Eqn
  q26 = wE 32 W
  q27 : Eqn
  q27 = sE 176 lem-pass-Sd0-vs-CS03
  q28 : Eqn
  q28 = sE 59 lem-pass-CS02-vs-CS03

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part2: 466 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 : ⟪ (ℓ "丒丞乞丒丞丈丨丌丳乐业丛中举丿乏九乏乏丸乙乏三丧") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞丈丨丒丞乞丒丞三丧中") ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 = derive (ℓ "丒丞乞丒丞丈丨丌丳乐业丛中举丿乏九乏乏丸乙乏三丧") (ℓ "丒丞乞丒丞丈丨丒丞乞丒丞三丧中")
  (re 15 3 (ℓ "乞") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丿") ∷
   re 18 1 (ℓ "丶丣丷丣丧") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw⁻ 20 q2 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q3 ∷
   rw⁻ 21 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   rw 18 q4 ∷
   re 18 5 (ℓ "乙") ∷
   re 17 3 (ℓ "乚") ∷
   rw 18 q3 ∷
   rw 16 q1 ∷
   re 15 1 (ℓ "乏九乏") ∷
   re 16 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 15 q5 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "举") ∷
   rw⁻ 19 q2 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q6 ∷
   rw 23 q3 ∷
   rw 22 q6 ∷
   rw 21 q5 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   rw 19 q2 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 15 q5 ∷
   rw 16 q7 ∷
   re 16 8 (ℓ "九") ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   re 15 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 14 q1 ∷
   rw⁻ 15 q5 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q6 ∷
   rw 15 q7 ∷
   re 15 8 (ℓ "九") ∷
   re 14 3 (ℓ "乞") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丿") ∷
   rw 16 q3 ∷
   rw 15 q1 ∷
   re 14 1 (ℓ "乏九乏") ∷
   re 15 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 22 q3 ∷
   rw 21 q6 ∷
   rw 20 q5 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   rw 18 q2 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 14 q5 ∷
   rw 15 q7 ∷
   re 15 8 (ℓ "九") ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q3 ∷
   rw 14 q9 ∷
   re 14 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 13 q1 ∷
   rw⁻ 14 q5 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw⁻ 16 q2 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q3 ∷
   rw⁻ 18 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q6 ∷
   rw 14 q7 ∷
   re 14 8 (ℓ "九") ∷
   re 13 3 (ℓ "乞") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 15 q3 ∷
   rw 14 q1 ∷
   re 13 1 (ℓ "乏九乏") ∷
   re 14 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 13 q5 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 21 q3 ∷
   rw 20 q6 ∷
   rw 19 q5 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 13 q5 ∷
   rw 14 q7 ∷
   re 14 8 (ℓ "九") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 12 q1 ∷
   rw⁻ 13 q5 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q6 ∷
   rw 13 q7 ∷
   re 13 8 (ℓ "九") ∷
   re 12 3 (ℓ "乞") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   re 16 1 (ℓ "丶丣丷丣丧") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   rw⁻ 19 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   rw 16 q4 ∷
   re 16 5 (ℓ "乙") ∷
   re 15 3 (ℓ "乚") ∷
   rw 16 q3 ∷
   rw 13 q1 ∷
   re 12 1 (ℓ "乏九乏") ∷
   re 13 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 20 q3 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 12 q5 ∷
   rw 13 q7 ∷
   re 13 8 (ℓ "九") ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   re 12 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 11 q1 ∷
   rw⁻ 12 q5 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw⁻ 14 q2 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q3 ∷
   rw⁻ 16 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q3 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q6 ∷
   rw 12 q7 ∷
   re 12 8 (ℓ "九") ∷
   re 11 3 (ℓ "乞") ∷
   rw 12 q13 ∷
   rw 13 q3 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏九乏") ∷
   re 12 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 19 q3 ∷
   rw 18 q6 ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 16 q3 ∷
   rw 13 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 11 q5 ∷
   rw 12 q7 ∷
   re 12 8 (ℓ "九") ∷
   rw 10 q14 ∷
   rw 11 q15 ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 10 q1 ∷
   rw⁻ 11 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q3 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q3 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw 11 q7 ∷
   re 11 8 (ℓ "九") ∷
   re 10 3 (ℓ "乞") ∷
   rw 11 q16 ∷
   rw 12 q3 ∷
   rw 11 q1 ∷
   re 10 1 (ℓ "乏九乏") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q5 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 18 q3 ∷
   rw 17 q6 ∷
   rw 16 q5 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q3 ∷
   rw 12 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 10 q5 ∷
   rw 11 q7 ∷
   re 11 8 (ℓ "九") ∷
   re 9 1 (ℓ "乏乃乏") ∷
   rw 11 q3 ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw 8 q21 ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 9 q5 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw⁻ 11 q2 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw⁻ 13 q2 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q6 ∷
   rw 9 q1 ∷
   rw⁻ 10 q5 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw⁻ 12 q2 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q3 ∷
   rw⁻ 14 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw 10 q7 ∷
   re 10 8 (ℓ "九") ∷
   re 9 3 (ℓ "乞") ∷
   rw⁻ 10 q20 ∷
   rw 11 q21 ∷
   rw 12 q3 ∷
   rw 16 q22 ∷
   rw 17 q23 ∷
   rw 18 q23 ∷
   rw 12 q24 ∷
   rw 13 q25 ∷
   rw 15 q1 ∷
   re 14 1 (ℓ "乏乙乏") ∷
   re 15 1 (ℓ "丶丣丷丣丧") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw⁻ 15 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 18 q3 ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 15 5 (ℓ "乙") ∷
   re 13 1 (ℓ "乏乙乏") ∷
   re 14 1 (ℓ "丶丣丷丣丧") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   rw 16 q2 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q3 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   re 14 5 (ℓ "乙") ∷
   rw 14 q26 ∷
   rw 13 q3 ∷
   rw⁻ 12 q27 ∷
   rw⁻ 13 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 178 lem-comm-CCZ012-CZ03

-- pass [CCZ012] [CZ03]: 1 steps
lem-pass-CCZ012-vs-CZ03 : ⟪ (ℓ "乙丯") ⟫ʷ ≈ ⟪ (ℓ "丯乙") ⟫ʷ
lem-pass-CCZ012-vs-CZ03 = derive (ℓ "乙丯") (ℓ "丯乙")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 177 lem-pass-CS23-vs-S0
  q31 : Eqn
  q31 = wE 1388 W
  q32 : Eqn
  q32 = sE 179 lem-pass-S0-vs-CSd23

-- pass [S0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丈义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丈") ⟫ʷ
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丈义乣乊乣") (ℓ "义乣乊乣丈")
  (rw⁻ 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷ []) Eq.refl
