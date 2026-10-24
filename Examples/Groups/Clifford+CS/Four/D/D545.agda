{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD545 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D545 (W : Ws) (Sᴰ : SD545) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ013-vs-CSd13 : St 175
  lem-pass-CCZ013-vs-CSd13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ013-vs-CZ13 : St 58
  lem-pass-CCZ013-vs-CZ13 = pickᴰ 1 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CCZ012-vs-CSd03 : St 830
  lem-pass-CCZ012-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CS03-vs-S0 : St 918
  lem-pass-CS03-vs-S0 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 914
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 5 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 916
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 6 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 917
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 7 Sᴰ
  lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 : St 919
  lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 56 W
  q7 : Eqn
  q7 = wE 689 W
  q8 : Eqn
  q8 = wE 1384 W
  q9 : Eqn
  q9 = wE 153 W
  q10 : Eqn
  q10 = wE 464 W
  q11 : Eqn
  q11 = wE 1385 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q15 : Eqn
  q15 = wE 1386 W
  q16 : Eqn
  q16 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q17 : Eqn
  q17 = wE 175 W
  q18 : Eqn
  q18 = sE 175 lem-pass-CCZ013-vs-CSd13
  q19 : Eqn
  q19 = sE 58 lem-pass-CCZ013-vs-CZ13
  q20 : Eqn
  q20 = wE 154 W
  q21 : Eqn
  q21 = wE 1387 W
  q22 : Eqn
  q22 = wE 43 W
  q23 : Eqn
  q23 = wE 32 W
  q24 : Eqn
  q24 = sE 918 lem-pass-CS03-vs-S0
  q25 : Eqn
  q25 = sE 60 lem-pass-CSd02-vs-CS03
  q26 : Eqn
  q26 = wE 173 W
  q27 : Eqn
  q27 = wE 458 W
  q28 : Eqn
  q28 = wE 459 W
  q29 : Eqn
  q29 = wE 460 W
  q30 : Eqn
  q30 = eqn (ℓ "丳业") (ℓ "业丳") (low-comm (CX₁₀) ((S ↑)))
  q31 : Eqn
  q31 = wE 461 W
  q32 : Eqn
  q32 = wE 462 W
  q33 : Eqn
  q33 = wE 463 W
  q34 : Eqn
  q34 = wE 465 W
  q35 : Eqn
  q35 = wE 466 W

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part1: 500 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 : ⟪ (ℓ "丌丳乐业丛乏九乏乏乏中丽乚举丿丿乚丈丨丒丞乞丒丞三丧") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞丈丨丌丳乐业丛中举丿乏九乏乏丸乙乏三丧") ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 = derive (ℓ "丌丳乐业丛乏九乏乏乏中丽乚举丿丿乚丈丨丒丞乞丒丞三丧") (ℓ "丒丞乞丒丞丈丨丌丳乐业丛中举丿乏九乏乏丸乙乏三丧")
  (re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q1 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q1 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q1 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 5 q1 ∷
   rw 6 q6 ∷
   re 6 8 (ℓ "九") ∷
   rw 4 q7 ∷
   rw 5 q8 ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q1 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 4 q2 ∷
   rw⁻ 5 q1 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q1 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q1 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q1 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "九") ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q1 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 3 q2 ∷
   rw⁻ 4 q1 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q1 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 4 q12 ∷
   rw 5 q5 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q1 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q1 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw⁻ 0 q16 ∷
   rw 1 q17 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q1 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q1 ∷
   rw⁻ 9 q4 ∷
   rw 2 q2 ∷
   rw⁻ 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q16 ∷
   rw 4 q17 ∷
   rw 5 q5 ∷
   rw 9 q18 ∷
   rw 10 q19 ∷
   rw 11 q19 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q3 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q3 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   rw 8 q22 ∷
   re 8 5 (ℓ "乙") ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q5 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 7 q22 ∷
   re 7 5 (ℓ "乙") ∷
   rw 7 q23 ∷
   rw 6 q5 ∷
   rw 5 q24 ∷
   rw⁻ 6 q25 ∷
   rw 13 q2 ∷
   rw 12 q26 ∷
   rw 11 q16 ∷
   re 10 1 (ℓ "乏九乏") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q1 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q3 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q3 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q1 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q1 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw 10 q1 ∷
   rw 11 q6 ∷
   re 11 8 (ℓ "九") ∷
   rw 9 q26 ∷
   rw 8 q16 ∷
   rw 9 q27 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q13 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乐") ∷
   re 12 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 11 q1 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw⁻ 17 q1 ∷
   rw⁻ 18 q4 ∷
   rw 11 q2 ∷
   rw⁻ 12 q1 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 19 q4 ∷
   rw 12 q6 ∷
   re 12 8 (ℓ "九") ∷
   re 11 3 (ℓ "乞") ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 8 q14 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 8 q28 ∷
   rw⁻ 7 q14 ∷
   rw 8 q12 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q5 ∷
   rw 11 q2 ∷
   rw 10 q13 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q5 ∷
   rw 10 q29 ∷
   rw⁻ 9 q13 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "丮") ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "举") ∷
   re 13 1 (ℓ "丶丣丷丣丧") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw 13 q22 ∷
   re 13 5 (ℓ "乙") ∷
   re 12 3 (ℓ "乚") ∷
   rw 13 q5 ∷
   rw⁻ 8 q30 ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏乙乏") ∷
   re 13 1 (ℓ "丶丣丷丣丧") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q3 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 16 q5 ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q5 ∷
   rw 13 q22 ∷
   re 13 5 (ℓ "乙") ∷
   rw 13 q31 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乐") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "丿") ∷
   re 15 1 (ℓ "丶丣丷丣丧") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "丽") ∷
   rw⁻ 15 q3 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "举") ∷
   rw⁻ 17 q3 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q5 ∷
   rw⁻ 16 q3 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q5 ∷
   rw⁻ 18 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   rw 15 q22 ∷
   re 15 5 (ℓ "乙") ∷
   re 14 3 (ℓ "乚") ∷
   rw 15 q5 ∷
   rw 13 q2 ∷
   re 12 1 (ℓ "乏乃乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   rw 12 q32 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "乐") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "举") ∷
   rw 13 q5 ∷
   rw 12 q2 ∷
   re 11 1 (ℓ "乏乃乏") ∷
   rw 13 q5 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q5 ∷
   rw 11 q33 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乐") ∷
   rw 11 q9 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q5 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏乃乏") ∷
   rw 12 q5 ∷
   rw 9 q10 ∷
   rw 10 q34 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q12 ∷
   rw 11 q5 ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏九乏") ∷
   re 17 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 16 q1 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q3 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "举") ∷
   rw⁻ 20 q3 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q1 ∷
   rw⁻ 23 q4 ∷
   rw 24 q5 ∷
   rw 23 q4 ∷
   rw 22 q1 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   rw 20 q3 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   rw 16 q1 ∷
   rw 17 q6 ∷
   re 17 8 (ℓ "九") ∷
   re 15 1 (ℓ "乏乙乏") ∷
   re 16 1 (ℓ "丶丣丷丣丧") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q3 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q3 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q5 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q5 ∷
   rw 16 q22 ∷
   re 16 5 (ℓ "乙") ∷
   rw 16 q35 ∷
   re 16 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 15 q1 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 17 q3 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "举") ∷
   rw⁻ 19 q3 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw⁻ 21 q1 ∷
   rw⁻ 22 q4 ∷
   rw 15 q2 ∷
   rw⁻ 16 q1 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q5 ∷
   rw⁻ 18 q3 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   rw⁻ 20 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   rw⁻ 22 q1 ∷
   rw⁻ 23 q4 ∷
   rw 16 q6 ∷
   re 16 8 (ℓ "九") ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 919 lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [S0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 : ⟪ (ℓ "义乣乊乣丈") ⟫ʷ ≈ ⟪ (ℓ "丈义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 = derive (ℓ "义乣乊乣丈") (ℓ "丈义乣乊乣")
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1535 W
  q38 : Eqn
  q38 = wE 5 W
  q39 : Eqn
  q39 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q40 : Eqn
  q40 = wE 76 W
  q41 : Eqn
  q41 = eqn (ℓ "並丗") (ℓ "丗並") (low-comm (Swap) ((K • iI)))
  q42 : Eqn
  q42 = wE 1549 W
  q43 : Eqn
  q43 = wE 29 W
  q44 : Eqn
  q44 = wE 31 W
  q45 : Eqn
  q45 = sE 830 lem-pass-CCZ012-vs-CSd03
  q46 : Eqn
  q46 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q47 : Eqn
  q47 = wE 1550 W
  q48 : Eqn
  q48 = wE 1538 W

-- pass [TOFF201] [CSd03]: 33 steps
lem-pass-TOFF201-vs-CSd03 : ⟪ (ℓ "乣丮") ⟫ʷ ≈ ⟪ (ℓ "丮乣") ⟫ʷ
lem-pass-TOFF201-vs-CSd03 = derive (ℓ "乣丮") (ℓ "丮乣")
  (rw 0 q37 ∷
   rw 4 q38 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw⁻ 5 q39 ∷
   rw 4 q40 ∷
   rw⁻ 3 q39 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 2 q41 ∷
   rw 3 q42 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q39 ∷
   rw 3 q43 ∷
   rw 4 q39 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q41 ∷
   rw 4 q44 ∷
   rw 1 q45 ∷
   rw 2 q38 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q39 ∷
   rw 2 q40 ∷
   rw⁻ 1 q39 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 0 q46 ∷
   rw 1 q47 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q39 ∷
   rw 1 q43 ∷
   rw 2 q39 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q46 ∷
   rw 2 q44 ∷
   rw 1 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q50 : Eqn
  q50 = wE 1106 W
  q51 : Eqn
  q51 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q52 : Eqn
  q52 = wE 1551 W
  q53 : Eqn
  q53 = wE 317 W
  q54 : Eqn
  q54 = wE 27 W
  q55 : Eqn
  q55 = wE 142 W
  q56 : Eqn
  q56 = wE 1552 W
  q57 : Eqn
  q57 = sE 914 lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q58 : Eqn
  q58 = sE 916 lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q59 : Eqn
  q59 = wE 1553 W
  q60 : Eqn
  q60 = wE 140 W
  q61 : Eqn
  q61 = wE 7 W
  q62 : Eqn
  q62 = wE 1554 W

-- pass [X2 CSd20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 43 steps
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "丘丨丘丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "丘丨丘丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘丨丘")
  (rw 5 q38 ∷
   rw⁻ 4 q49 ∷
   rw 3 q50 ∷
   rw⁻ 2 q51 ∷
   rw 1 q40 ∷
   rw⁻ 0 q51 ∷
   rw 1 q52 ∷
   rw 0 q53 ∷
   rw 1 q49 ∷
   rw 2 q51 ∷
   rw 3 q54 ∷
   rw 4 q51 ∷
   rw 5 q51 ∷
   rw 6 q55 ∷
   rw 7 q51 ∷
   rw 8 q51 ∷
   rw 9 q55 ∷
   rw 10 q51 ∷
   rw 11 q44 ∷
   rw 2 q56 ∷
   rw 12 q57 ∷
   rw 9 q57 ∷
   rw 6 q58 ∷
   rw 10 q59 ∷
   rw 25 q38 ∷
   rw⁻ 24 q49 ∷
   rw 23 q50 ∷
   rw⁻ 22 q51 ∷
   rw 21 q60 ∷
   rw⁻ 20 q51 ∷
   rw⁻ 19 q51 ∷
   rw 18 q60 ∷
   rw⁻ 17 q51 ∷
   rw⁻ 16 q51 ∷
   rw 15 q61 ∷
   rw⁻ 14 q51 ∷
   rw 15 q62 ∷
   rw 14 q53 ∷
   rw 15 q49 ∷
   rw 16 q51 ∷
   rw 17 q43 ∷
   rw 18 q51 ∷
   rw 19 q44 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 137 W
  q64 : Eqn
  q64 = wE 1555 W
  q65 : Eqn
  q65 = wE 1556 W
  q66 : Eqn
  q66 = sE 917 lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q67 : Eqn
  q67 = wE 1557 W
  q68 : Eqn
  q68 = wE 1558 W
  q69 : Eqn
  q69 = wE 139 W

-- pass [X2 CKd20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 57 steps
lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "丘久丘丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "丘久丘丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘久丘")
  (rw 5 q38 ∷
   rw⁻ 4 q49 ∷
   rw 3 q50 ∷
   rw⁻ 2 q51 ∷
   rw 1 q63 ∷
   rw⁻ 0 q51 ∷
   rw 1 q64 ∷
   rw 0 q53 ∷
   rw 1 q49 ∷
   rw 2 q51 ∷
   rw 3 q54 ∷
   rw 4 q51 ∷
   rw 5 q51 ∷
   rw 6 q55 ∷
   rw 7 q51 ∷
   rw 8 q51 ∷
   rw 9 q43 ∷
   rw 10 q51 ∷
   rw 11 q51 ∷
   rw 12 q55 ∷
   rw 13 q51 ∷
   rw 14 q51 ∷
   rw 15 q54 ∷
   rw 16 q51 ∷
   rw 17 q44 ∷
   rw 2 q65 ∷
   rw 18 q58 ∷
   rw 15 q57 ∷
   rw 12 q66 ∷
   rw 9 q57 ∷
   rw 6 q58 ∷
   rw 10 q67 ∷
   rw 31 q38 ∷
   rw⁻ 30 q49 ∷
   rw 29 q50 ∷
   rw⁻ 28 q51 ∷
   rw 27 q61 ∷
   rw⁻ 26 q51 ∷
   rw⁻ 25 q51 ∷
   rw 24 q60 ∷
   rw⁻ 23 q51 ∷
   rw⁻ 22 q51 ∷
   rw 21 q40 ∷
   rw⁻ 20 q51 ∷
   rw⁻ 19 q51 ∷
   rw 18 q60 ∷
   rw⁻ 17 q51 ∷
   rw⁻ 16 q51 ∷
   rw 15 q61 ∷
   rw⁻ 14 q51 ∷
   rw 15 q68 ∷
   rw 14 q53 ∷
   rw 15 q49 ∷
   rw 16 q51 ∷
   rw 17 q69 ∷
   rw 18 q51 ∷
   rw 19 q44 ∷ []) Eq.refl
