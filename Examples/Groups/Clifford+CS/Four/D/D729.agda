{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD729 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D729 (W : Ws) (Sᴰ : SD729) where

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
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 : St 2201
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 = pickᴰ 0 Sᴰ

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
  q16 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 2221 W
  q18 : Eqn
  q18 = wE 2055 W
  q19 : Eqn
  q19 = wE 1966 W
  q20 : Eqn
  q20 = sE 2201 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02
  q21 : Eqn
  q21 = wE 2020 W
  q22 : Eqn
  q22 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q23 : Eqn
  q23 = eqn (ℓ "丕丞") (ℓ "丞丕") (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q24 : Eqn
  q24 = wE 2021 W
  q25 : Eqn
  q25 = eqn (ℓ "丒且") (ℓ "且丒") (low-comm ((X ↑)) (S))
  q26 : Eqn
  q26 = eqn (ℓ "丒丕") (ℓ "丕丒") (low-comm ((X ↑)) ((S • S • S)))
  q27 : Eqn
  q27 = wE 2057 W
  q28 : Eqn
  q28 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "丌丕") (ℓ "丕丌") (low₁-comm (X) (((S • S • S) ↑)))
  q30 : Eqn
  q30 = wE 2219 W
  q31 : Eqn
  q31 = wE 2220 W

-- pass [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3] [TOFF013 CS02 TOFF013 CSd02]: 777 steps
lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丌丒丞习丽习举丌丒丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丌丒丞习丽习举丌丒丞") ⟫ʷ
lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丌丒丞习丽习举丌丒丞乞丧乞丨") (ℓ "乞丧乞丨丌丒丞习丽习举丌丒丞")
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
   rw 12 q1 ∷
   rw 11 q7 ∷
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
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw⁻ 8 q12 ∷
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
   rw⁻ 11 q12 ∷
   rw 12 q9 ∷
   rw⁻ 13 q12 ∷
   rw 14 q5 ∷
   rw 13 q14 ∷
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
   rw 14 q12 ∷
   rw 15 q13 ∷
   rw⁻ 14 q12 ∷
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
   rw⁻ 17 q12 ∷
   rw 18 q9 ∷
   rw⁻ 19 q12 ∷
   rw 20 q5 ∷
   rw 19 q15 ∷
   rw 13 q1 ∷
   rw 12 q7 ∷
   rw 11 q12 ∷
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
   rw 8 q12 ∷
   rw 7 q16 ∷
   rw 8 q17 ∷
   rw⁻ 7 q12 ∷
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
   rw⁻ 10 q12 ∷
   rw 11 q9 ∷
   rw⁻ 12 q16 ∷
   rw 13 q5 ∷
   rw 12 q18 ∷
   rw 20 q1 ∷
   rw 19 q7 ∷
   rw 18 q12 ∷
   re 17 1 (ℓ "乏九乏") ∷
   re 18 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 17 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw⁻ 19 q3 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "举") ∷
   rw⁻ 21 q3 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw⁻ 23 q2 ∷
   rw⁻ 24 q4 ∷
   rw 25 q5 ∷
   rw 24 q4 ∷
   rw 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q5 ∷
   rw 21 q3 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 22 q5 ∷
   rw 19 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q5 ∷
   rw 17 q2 ∷
   rw 18 q6 ∷
   re 18 8 (ℓ "九") ∷
   rw 16 q7 ∷
   rw 15 q12 ∷
   rw 14 q16 ∷
   rw 15 q17 ∷
   rw⁻ 14 q12 ∷
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
   rw⁻ 17 q12 ∷
   rw 18 q9 ∷
   rw⁻ 19 q16 ∷
   rw 20 q5 ∷
   rw 19 q19 ∷
   rw 3 q20 ∷
   rw 8 q1 ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
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
   rw 3 q12 ∷
   rw 2 q7 ∷
   rw 3 q21 ∷
   rw⁻ 2 q12 ∷
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
   rw⁻ 4 q12 ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw⁻ 5 q22 ∷
   rw⁻ 6 q11 ∷
   rw 13 q1 ∷
   rw 12 q7 ∷
   rw 11 q12 ∷
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
   rw 8 q12 ∷
   rw 7 q7 ∷
   rw 8 q21 ∷
   rw⁻ 7 q12 ∷
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
   rw 11 q5 ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q10 ∷
   rw 5 q1 ∷
   rw 4 q12 ∷
   re 3 1 (ℓ "乏九乏") ∷
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
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q12 ∷
   rw 1 q12 ∷
   rw 2 q24 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q6 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw⁻ 2 q12 ∷
   rw 3 q5 ∷
   rw 2 q25 ∷
   rw 3 q15 ∷
   rw 8 q1 ∷
   rw 7 q12 ∷
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
   rw 5 q12 ∷
   rw 4 q12 ∷
   rw 5 q24 ∷
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
   rw⁻ 5 q12 ∷
   rw 6 q5 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 8 q4 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 1 q2 ∷
   rw 2 q6 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q16 ∷
   rw 1 q27 ∷
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
   rw⁻ 1 q16 ∷
   rw 2 q5 ∷
   rw 1 q28 ∷
   rw 2 q19 ∷
   rw 6 q1 ∷
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
   rw 4 q16 ∷
   rw 5 q27 ∷
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
   rw⁻ 5 q16 ∷
   rw 6 q5 ∷
   rw 5 q29 ∷
   rw 6 q18 ∷
   rw 1 q30 ∷
   rw 3 q31 ∷ []) Eq.refl
