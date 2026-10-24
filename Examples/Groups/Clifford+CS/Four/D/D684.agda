{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD684 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D684 (W : Ws) (Sᴰ : SD684) where

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
  lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1805
  lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 0 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 1 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 : St 1806
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1807
  lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 : St 1808
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1809
  lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 5 Sᴰ

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
  q12 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q13 : Eqn
  q13 = wE 1609 W
  q14 : Eqn
  q14 = eqn (ℓ "九丞") (ℓ "丞九") (low₃-comm (Toff) (X))
  q15 : Eqn
  q15 = wE 1962 W
  q16 : Eqn
  q16 = wE 1963 W
  q17 : Eqn
  q17 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = wE 2019 W
  q19 : Eqn
  q19 = eqn (ℓ "丈丒") (ℓ "丒丈") (low₁-comm (S) (X))
  q20 : Eqn
  q20 = wE 1051 W
  q21 : Eqn
  q21 = eqn (ℓ "三丒") (ℓ "丒三") (low₁-comm ((S • S • S)) (X))
  q22 : Eqn
  q22 = wE 1049 W
  q23 : Eqn
  q23 = sE 1806 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02
  q24 : Eqn
  q24 = wE 2020 W
  q25 : Eqn
  q25 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q28 : Eqn
  q28 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q30 : Eqn
  q30 = wE 2021 W
  q31 : Eqn
  q31 = wE 1964 W
  q32 : Eqn
  q32 = wE 2018 W

-- pass [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3] [TOFF013 CS02 TOFF013 CSd02]: 557 steps
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丒丘丞中九丮九丒丘丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丒丘丞中九丮九丒丘丞") ⟫ʷ
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丒丘丞中九丮九丒丘丞乞丧乞丨") (ℓ "乞丧乞丨丒丘丞中九丮九丒丘丞")
  (rw 11 q1 ∷
   re 10 1 (ℓ "乏九乏") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw 10 q2 ∷
   rw 11 q6 ∷
   re 11 8 (ℓ "九") ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 10 q1 ∷
   rw⁻ 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q5 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q4 ∷
   rw 11 q6 ∷
   re 11 8 (ℓ "九") ∷
   re 10 3 (ℓ "乞") ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q5 ∷
   rw⁻ 12 q10 ∷
   rw 15 q1 ∷
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
   rw 14 q8 ∷
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
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q5 ∷
   rw⁻ 16 q11 ∷
   rw 8 q12 ∷
   re 10 1 (ℓ "乏九乏") ∷
   rw 9 q13 ∷
   rw⁻ 10 q14 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "乞") ∷
   rw 10 q12 ∷
   rw 11 q15 ∷
   rw 13 q12 ∷
   re 15 1 (ℓ "乏九乏") ∷
   rw 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "乞") ∷
   rw 15 q12 ∷
   rw 16 q16 ∷
   rw 11 q1 ∷
   rw 10 q7 ∷
   re 9 1 (ℓ "乏九乏") ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw⁻ 13 q3 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 17 q5 ∷
   rw 16 q4 ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q5 ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 14 q5 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 10 q6 ∷
   re 10 8 (ℓ "九") ∷
   rw 8 q7 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw⁻ 7 q17 ∷
   rw 8 q9 ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw⁻ 13 q3 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   rw⁻ 12 q3 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 10 q6 ∷
   re 10 8 (ℓ "九") ∷
   re 9 3 (ℓ "乞") ∷
   rw⁻ 10 q17 ∷
   rw 11 q9 ∷
   rw⁻ 12 q17 ∷
   rw 13 q5 ∷
   rw⁻ 12 q19 ∷
   rw 13 q20 ∷
   rw 18 q1 ∷
   rw 17 q7 ∷
   re 16 1 (ℓ "乏九乏") ∷
   re 17 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw⁻ 20 q3 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q4 ∷
   rw 24 q5 ∷
   rw 23 q4 ∷
   rw 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   rw 20 q3 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   rw 16 q2 ∷
   rw 17 q6 ∷
   re 17 8 (ℓ "九") ∷
   rw 15 q7 ∷
   rw 14 q17 ∷
   rw 15 q18 ∷
   rw⁻ 14 q17 ∷
   rw 15 q9 ∷
   re 17 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw⁻ 20 q3 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q4 ∷
   rw 16 q1 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q5 ∷
   rw⁻ 19 q3 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q5 ∷
   rw⁻ 21 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 22 q5 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 24 q4 ∷
   rw 17 q6 ∷
   re 17 8 (ℓ "九") ∷
   re 16 3 (ℓ "乞") ∷
   rw⁻ 17 q17 ∷
   rw 18 q9 ∷
   rw⁻ 19 q17 ∷
   rw 20 q5 ∷
   rw⁻ 19 q21 ∷
   rw 20 q22 ∷
   rw 3 q23 ∷
   rw 8 q1 ∷
   rw 7 q7 ∷
   rw 6 q17 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   re 6 8 (ℓ "九") ∷
   rw 4 q7 ∷
   rw 3 q17 ∷
   rw 2 q7 ∷
   rw 3 q24 ∷
   rw⁻ 2 q17 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q1 ∷
   rw⁻ 4 q2 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw⁻ 4 q17 ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw⁻ 5 q25 ∷
   rw⁻ 6 q11 ∷
   rw 13 q1 ∷
   rw 12 q7 ∷
   rw 11 q17 ∷
   re 10 1 (ℓ "乏九乏") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   rw 10 q2 ∷
   rw 11 q6 ∷
   re 11 8 (ℓ "九") ∷
   rw 9 q7 ∷
   rw 8 q17 ∷
   rw 7 q7 ∷
   rw 8 q24 ∷
   rw⁻ 7 q17 ∷
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
   rw⁻ 9 q17 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 1 q27 ∷
   re 3 1 (ℓ "乏九乏") ∷
   rw 2 q13 ∷
   rw⁻ 3 q14 ∷
   rw 4 q7 ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q27 ∷
   rw⁻ 4 q28 ∷
   rw 5 q16 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (ℓ "乏九乏") ∷
   rw 8 q13 ∷
   rw⁻ 9 q14 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "乞") ∷
   rw⁻ 9 q27 ∷
   rw⁻ 10 q29 ∷
   rw 11 q15 ∷
   rw 4 q1 ∷
   rw 3 q17 ∷
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
   rw 1 q17 ∷
   rw 0 q17 ∷
   rw 1 q30 ∷
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
   rw⁻ 1 q17 ∷
   rw 2 q5 ∷
   rw⁻ 1 q19 ∷
   rw⁻ 2 q21 ∷
   rw 3 q22 ∷
   rw 8 q1 ∷
   rw 7 q17 ∷
   re 6 1 (ℓ "乏九乏") ∷
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
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   rw 6 q2 ∷
   rw 7 q6 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q17 ∷
   rw 4 q17 ∷
   rw 5 q30 ∷
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
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw⁻ 5 q17 ∷
   rw 6 q5 ∷
   rw⁻ 5 q21 ∷
   rw⁻ 6 q19 ∷
   rw 7 q20 ∷
   rw 1 q31 ∷
   rw 3 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q34 : Eqn
  q34 = sE 1808 lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03
  q35 : Eqn
  q35 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))

-- pass [X3 CS23 TOFF201 CSd23 TOFF201 X3] [CS03]: 31 steps
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 : ⟪ (ℓ "丞义乣乊乣丞中") ⟫ʷ ≈ ⟪ (ℓ "中丞义乣乊乣丞") ⟫ʷ
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 = derive (ℓ "丞义乣乊乣丞中") (ℓ "中丞义乣乊乣丞")
  (rw 7 q1 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw⁻ 5 q33 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q9 ∷
   rw 8 q5 ∷
   rw 1 q34 ∷
   rw⁻ 0 q25 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q5 ∷
   rw 1 q7 ∷
   rw 2 q16 ∷
   rw⁻ 1 q35 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q9 ∷
   rw 4 q5 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 1 q35 ∷
   rw 0 q33 ∷
   rw 1 q31 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 1805 lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2
  q37 : Eqn
  q37 = sE 1809 lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2
  q38 : Eqn
  q38 = sE 1807 lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2

-- pass [CS13 TOFF102 CSd13 TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (ℓ "丽习举习一三丛中丘九丘一一一丈业丮丘九丘") ⟫ʷ ≈ ⟪ (ℓ "一三丛中丘九丘一一一丈业丮丘九丘丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (ℓ "丽习举习一三丛中丘九丘一一一丈业丮丘九丘") (ℓ "一三丛中丘九丘一一一丈业丮丘九丘丽习举习")
  (rw 3 q36 ∷
   rw 2 q37 ∷
   rw 1 q36 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 1778 lem-S2

-- resp TOFF013 CS02 TOFF013 CSd02: 1 steps
lem-resp-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-resp-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "乞丧乞丨") (ℓ "九中九丮")
  (rw⁻ 0 q39 ∷ []) Eq.refl
