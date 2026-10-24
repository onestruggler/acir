{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD682 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D682 (W : Ws) (Sᴰ : SD682) where

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
  lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1788
  lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 0 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 1 Sᴰ
  lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : St 1789
  lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 2 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : St 1790
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = pickᴰ 3 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : St 1791
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = pickᴰ 4 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : St 1792
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = pickᴰ 5 Sᴰ

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
  q12 = sE 1790 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02
  q13 : Eqn
  q13 = wE 2017 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞中九丮九丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞中九丮九丞乞丧乞丨") (ℓ "乞丧乞丨丞中九丮九丞")
  (rw 7 q1 ∷
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
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
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
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   rw⁻ 8 q10 ∷
   rw 11 q1 ∷
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
   rw⁻ 12 q11 ∷
   rw 1 q12 ∷
   rw 4 q1 ∷
   rw 3 q7 ∷
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
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q13 ∷
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
   rw 1 q9 ∷
   rw 2 q5 ∷
   rw⁻ 1 q10 ∷
   rw 6 q1 ∷
   rw 5 q7 ∷
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
   rw 2 q7 ∷
   rw 3 q13 ∷
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
   rw 3 q9 ∷
   rw 4 q5 ∷
   rw⁻ 3 q11 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 1778 lem-S2
  q15 : Eqn
  q15 = sE 1788 lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02
  q16 : Eqn
  q16 = sE 1778 lem-S2

-- pass [X3 CSd30 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞丮丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞丮丞九中九丮") (ℓ "九中九丮丞丮丞")
  (rw 3 q14 ∷
   rw 0 q15 ∷
   rw⁻ 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 12 W
  q18 : Eqn
  q18 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q20 : Eqn
  q20 = wE 22 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = wE 23 W
  q23 : Eqn
  q23 = wE 84 W
  q24 : Eqn
  q24 = wE 65 W
  q25 : Eqn
  q25 = wE 5 W
  q26 : Eqn
  q26 = wE 123 W
  q27 : Eqn
  q27 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q28 : Eqn
  q28 = wE 24 W
  q29 : Eqn
  q29 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q30 : Eqn
  q30 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q31 : Eqn
  q31 = wE 25 W
  q32 : Eqn
  q32 = wE 124 W
  q33 : Eqn
  q33 = wE 125 W
  q34 : Eqn
  q34 = wE 14 W
  q35 : Eqn
  q35 = wE 215 W
  q36 : Eqn
  q36 = wE 121 W
  q37 : Eqn
  q37 = wE 30 W
  q38 : Eqn
  q38 = wE 27 W
  q39 : Eqn
  q39 = wE 122 W
  q40 : Eqn
  q40 = wE 31 W
  q41 : Eqn
  q41 = wE 127 W
  q42 : Eqn
  q42 = wE 118 W
  q43 : Eqn
  q43 = wE 7 W
  q44 : Eqn
  q44 = wE 74 W
  q45 : Eqn
  q45 = wE 216 W
  q46 : Eqn
  q46 = wE 217 W
  q47 : Eqn
  q47 = wE 218 W
  q48 : Eqn
  q48 = eqn (ℓ "丌两丌乢丠乢") (ℓ "乢丠乢丌两丌") (ax ck-tct)
  q49 : Eqn
  q49 = wE 219 W
  q50 : Eqn
  q50 = wE 220 W
  q51 : Eqn
  q51 = wE 221 W
  q52 : Eqn
  q52 = wE 49 W
  q53 : Eqn
  q53 = wE 51 W
  q54 : Eqn
  q54 = wE 222 W
  q55 : Eqn
  q55 = wE 223 W

-- pass [X2 CK20 X2] [TOFF012 CS03 TOFF012 CSd03]: 320 steps
lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘乄丘九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘乄丘九中九丮") (ℓ "九中九丮丘乄丘")
  (rw 3 q14 ∷
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
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 10 q22 ∷
   re 11 5 (ℓ "中") ∷
   rw 9 q17 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q23 ∷
   rw 7 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q24 ∷
   rw 5 q19 ∷
   rw 6 q25 ∷
   rw 7 q26 ∷
   rw 8 q27 ∷
   rw 9 q28 ∷
   rw 10 q29 ∷
   rw 11 q28 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q30 ∷
   rw 13 q31 ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丽") ∷
   rw 13 q26 ∷
   rw 14 q32 ∷
   rw 7 q33 ∷
   re 7 8 (ℓ "乢") ∷
   re 6 3 (ℓ "也") ∷
   re 4 1 (ℓ "丼丠丼") ∷
   rw 6 q34 ∷
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
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 8 q22 ∷
   re 9 5 (ℓ "中") ∷
   rw 7 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q23 ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q24 ∷
   rw 3 q19 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 9 q28 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q30 ∷
   rw 11 q31 ∷
   rw 12 q30 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q26 ∷
   rw 12 q32 ∷
   rw 5 q33 ∷
   re 5 8 (ℓ "乢") ∷
   re 4 3 (ℓ "也") ∷
   rw 2 q35 ∷
   re 1 1 (ℓ "丼临丼") ∷
   rw 3 q34 ∷
   rw 0 q35 ∷
   rw 7 q25 ∷
   re 6 1 (ℓ "並乢並") ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q36 ∷
   rw 7 q27 ∷
   rw 8 q37 ∷
   rw 9 q29 ∷
   rw 10 q37 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q30 ∷
   rw 12 q38 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q36 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 13 q41 ∷
   rw 12 q42 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q30 ∷
   rw 12 q43 ∷
   rw⁻ 11 q30 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q44 ∷
   rw⁻ 9 q29 ∷
   rw 8 q44 ∷
   rw⁻ 7 q27 ∷
   rw 6 q42 ∷
   rw 7 q33 ∷
   re 7 8 (ℓ "乢") ∷
   rw 5 q45 ∷
   re 4 1 (ℓ "並乢並") ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q36 ∷
   rw 5 q27 ∷
   rw 6 q37 ∷
   rw 7 q29 ∷
   rw 8 q37 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q30 ∷
   rw 10 q38 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q36 ∷
   rw 11 q39 ∷
   rw 12 q40 ∷
   rw 11 q41 ∷
   rw 10 q42 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q30 ∷
   rw 10 q43 ∷
   rw⁻ 9 q30 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q44 ∷
   rw⁻ 7 q29 ∷
   rw 6 q44 ∷
   rw⁻ 5 q27 ∷
   rw 4 q42 ∷
   rw 5 q33 ∷
   re 5 8 (ℓ "乢") ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q46 ∷
   rw 2 q48 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q36 ∷
   rw 2 q27 ∷
   rw 3 q37 ∷
   rw 4 q29 ∷
   rw 5 q37 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q30 ∷
   rw 7 q38 ∷
   rw 8 q30 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw 5 q29 ∷
   rw 6 q28 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q26 ∷
   rw 9 q32 ∷
   rw 2 q33 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q49 ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q36 ∷
   rw 4 q27 ∷
   rw 5 q37 ∷
   rw 6 q29 ∷
   rw 7 q37 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 7 q29 ∷
   rw 8 q28 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q26 ∷
   rw 11 q32 ∷
   rw 4 q33 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   rw 4 q50 ∷
   rw 5 q51 ∷
   rw 6 q50 ∷
   rw 7 q40 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q36 ∷
   rw 2 q27 ∷
   rw 3 q37 ∷
   rw 4 q29 ∷
   rw 5 q37 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q30 ∷
   rw 7 q38 ∷
   rw 8 q30 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw⁻ 0 q19 ∷
   rw 1 q52 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 2 q34 ∷
   rw 3 q53 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q34 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q20 ∷
   rw⁻ 7 q21 ∷
   rw 8 q22 ∷
   re 5 5 (ℓ "中") ∷
   rw⁻ 6 q19 ∷
   rw⁻ 7 q18 ∷
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
   rw 3 q17 ∷
   re 1 3 (ℓ "丧") ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q36 ∷
   rw 4 q27 ∷
   rw 5 q37 ∷
   rw 6 q29 ∷
   rw 7 q37 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 11 q40 ∷
   rw⁻ 2 q19 ∷
   rw 3 q52 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q34 ∷
   rw 5 q53 ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 6 q34 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q20 ∷
   rw⁻ 9 q21 ∷
   rw 10 q22 ∷
   re 7 5 (ℓ "中") ∷
   rw⁻ 8 q19 ∷
   rw⁻ 9 q18 ∷
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
   rw 3 q54 ∷
   rw 6 q17 ∷
   re 4 3 (ℓ "乄") ∷
   rw 5 q54 ∷
   rw 6 q34 ∷
   rw 3 q55 ∷
   rw⁻ 0 q16 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q57 : Eqn
  q57 = wE 257 W
  q58 : Eqn
  q58 = wE 76 W
  q59 : Eqn
  q59 = wE 258 W
  q60 : Eqn
  q60 = wE 29 W
  q61 : Eqn
  q61 = sE 1791 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [CS03 TOFF012 CSd03 TOFF012]: 65 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘习丽习举丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘习丽习举丘") ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘习丽习举丘中九丮九") (ℓ "中九丮九丘习丽习举丘")
  (rw 7 q25 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q30 ∷
   rw 7 q43 ∷
   rw⁻ 6 q30 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 5 q56 ∷
   rw 6 q57 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q30 ∷
   rw 6 q38 ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q56 ∷
   rw 7 q40 ∷
   rw 6 q8 ∷
   rw 11 q25 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw⁻ 12 q30 ∷
   rw 11 q58 ∷
   rw⁻ 10 q30 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 9 q56 ∷
   rw 10 q59 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q30 ∷
   rw 10 q60 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q56 ∷
   rw 11 q40 ∷
   rw 10 q8 ∷
   rw 1 q61 ∷
   rw 2 q25 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q30 ∷
   rw 2 q43 ∷
   rw⁻ 1 q30 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 0 q56 ∷
   rw 1 q57 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q30 ∷
   rw 1 q38 ∷
   rw 2 q30 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q56 ∷
   rw 2 q40 ∷
   rw 1 q13 ∷
   rw 4 q25 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw⁻ 5 q30 ∷
   rw 4 q58 ∷
   rw⁻ 3 q30 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 2 q56 ∷
   rw 3 q59 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q30 ∷
   rw 3 q60 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q56 ∷
   rw 4 q40 ∷
   rw 3 q13 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1792 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [TOFF012 CS03 TOFF012 CSd03]: 65 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘习丽习举丘九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘习丽习举丘") ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘习丽习举丘九中九丮") (ℓ "九中九丮丘习丽习举丘")
  (rw 5 q8 ∷
   rw 10 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q30 ∷
   rw 10 q43 ∷
   rw⁻ 9 q30 ∷
   re 10 3 (ℓ "丽") ∷
   rw⁻ 8 q56 ∷
   rw 9 q57 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q56 ∷
   rw 10 q40 ∷
   rw 9 q8 ∷
   rw 14 q25 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw⁻ 15 q30 ∷
   rw 14 q58 ∷
   rw⁻ 13 q30 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 12 q56 ∷
   rw 13 q59 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q30 ∷
   rw 13 q60 ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q56 ∷
   rw 14 q40 ∷
   rw 1 q62 ∷
   rw 0 q13 ∷
   rw 3 q25 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q30 ∷
   rw 3 q43 ∷
   rw⁻ 2 q30 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 1 q56 ∷
   rw 2 q57 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q30 ∷
   rw 2 q38 ∷
   rw 3 q30 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q56 ∷
   rw 3 q40 ∷
   rw 2 q13 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw⁻ 6 q30 ∷
   rw 5 q58 ∷
   rw⁻ 4 q30 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 3 q56 ∷
   rw 4 q59 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q30 ∷
   rw 4 q60 ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q56 ∷
   rw 5 q40 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = sE 1789 lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CCZ123 : ⟪ (ℓ "丽习举习乜") ⟫ʷ ≈ ⟪ (ℓ "乜丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CCZ123 = derive (ℓ "丽习举习乜") (ℓ "乜丽习举习")
  (rw⁻ 0 q63 ∷ []) Eq.refl
