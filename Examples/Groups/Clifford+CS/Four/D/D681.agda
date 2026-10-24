{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD681 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D681 (W : Ws) (Sᴰ : SD681) where

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
  lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1779
  lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 0 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CS03 : St 1780
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CS03 = pickᴰ 1 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CSd03 : St 1781
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-TOFF012-X1-X2 : St 1782
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-TOFF012-X1-X2 = pickᴰ 3 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X2-TOFF012-X2 : St 1783
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X2-TOFF012-X2 = pickᴰ 4 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 5 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : St 1784
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = pickᴰ 6 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF103-X3 : St 1785
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF103-X3 = pickᴰ 7 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1786
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 8 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : St 1787
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = pickᴰ 9 Sᴰ

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
  q12 = sE 1784 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02
  q13 : Eqn
  q13 = wE 2017 W

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞九中九丮丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞九中九丮丞") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞九中九丮丞乞丧乞丨") (ℓ "乞丧乞丨丞九中九丮丞")
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
  q15 = sE 1783 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X2-TOFF012-X2
  q16 : Eqn
  q16 = sE 1778 lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X2 TOFF012 X2]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 : ⟪ (ℓ "九中九丮丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 = derive (ℓ "九中九丮丘九丘") (ℓ "丘九丘九中九丮")
  (rw 0 q14 ∷
   rw 0 q15 ∷
   rw⁻ 3 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 1781 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CSd03]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 : ⟪ (ℓ "九中九丮丮") ⟫ʷ ≈ ⟪ (ℓ "丮九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 = derive (ℓ "九中九丮丮") (ℓ "丮九中九丮")
  (rw 0 q14 ∷
   rw 0 q17 ∷
   rw⁻ 1 q16 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 1780 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CS03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CS03]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 : ⟪ (ℓ "九中九丮中") ⟫ʷ ≈ ⟪ (ℓ "中九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 = derive (ℓ "九中九丮中") (ℓ "中九中九丮")
  (rw 0 q14 ∷
   rw 0 q18 ∷
   rw⁻ 1 q16 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 1782 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-TOFF012-X1-X2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 TOFF012 X1 X2]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2 : ⟪ (ℓ "九中九丮丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2 = derive (ℓ "九中九丮丒丘九丒丘") (ℓ "丒丘九丒丘九中九丮")
  (rw 0 q14 ∷
   rw 0 q19 ∷
   rw⁻ 5 q16 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (ℓ "九丞") (ℓ "丞九") (low₃-comm (Toff) (X))
  q21 : Eqn
  q21 = wE 1962 W
  q22 : Eqn
  q22 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q23 : Eqn
  q23 = wE 1963 W
  q24 : Eqn
  q24 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q26 : Eqn
  q26 = wE 5 W
  q27 : Eqn
  q27 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q28 : Eqn
  q28 = wE 76 W
  q29 : Eqn
  q29 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q30 : Eqn
  q30 = wE 258 W
  q31 : Eqn
  q31 = wE 29 W
  q32 : Eqn
  q32 = wE 31 W
  q33 : Eqn
  q33 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q34 : Eqn
  q34 = wE 7 W
  q35 : Eqn
  q35 = wE 257 W
  q36 : Eqn
  q36 = wE 27 W
  q37 : Eqn
  q37 = sE 1787 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03
  q38 : Eqn
  q38 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q39 : Eqn
  q39 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q40 : Eqn
  q40 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q41 : Eqn
  q41 = wE 1964 W
  q42 : Eqn
  q42 = wE 2018 W

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [TOFF012 CS03 TOFF012 CSd03]: 139 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘丞习丽习举丘丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘丞习丽习举丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘丞习丽习举丘丞九中九丮") (ℓ "九中九丮丘丞习丽习举丘丞")
  (rw⁻ 7 q20 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q7 ∷
   rw 9 q21 ∷
   rw⁻ 8 q22 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q20 ∷
   rw 13 q1 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 14 q5 ∷
   rw 11 q7 ∷
   rw 12 q23 ∷
   rw⁻ 11 q24 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q9 ∷
   rw 14 q5 ∷
   rw 6 q8 ∷
   rw⁻ 9 q25 ∷
   rw 12 q26 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw⁻ 13 q27 ∷
   rw 12 q28 ∷
   rw⁻ 11 q27 ∷
   re 12 3 (ℓ "举") ∷
   rw⁻ 10 q29 ∷
   rw 11 q30 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q27 ∷
   rw 11 q31 ∷
   rw 12 q27 ∷
   re 10 3 (ℓ "丮") ∷
   rw 11 q29 ∷
   rw 12 q32 ∷
   rw 11 q8 ∷
   rw⁻ 14 q33 ∷
   rw 17 q26 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q27 ∷
   rw 17 q34 ∷
   rw⁻ 16 q27 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q29 ∷
   rw 16 q35 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q27 ∷
   rw 16 q36 ∷
   rw 17 q27 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q29 ∷
   rw 17 q32 ∷
   rw 2 q37 ∷
   rw⁻ 1 q38 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 3 q38 ∷
   rw⁻ 4 q39 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q5 ∷
   rw 5 q7 ∷
   rw 6 q23 ∷
   rw⁻ 5 q24 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q9 ∷
   rw 8 q5 ∷
   rw⁻ 7 q38 ∷
   rw⁻ 8 q20 ∷
   rw⁻ 9 q38 ∷
   rw⁻ 10 q40 ∷
   rw 13 q1 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   rw 11 q7 ∷
   rw 12 q21 ∷
   rw⁻ 11 q22 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q9 ∷
   rw 14 q5 ∷
   rw 0 q13 ∷
   rw⁻ 1 q25 ∷
   rw⁻ 2 q33 ∷
   rw 5 q26 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q27 ∷
   rw 5 q34 ∷
   rw⁻ 4 q27 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q29 ∷
   rw 4 q35 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q27 ∷
   rw 4 q36 ∷
   rw 5 q27 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q29 ∷
   rw 5 q32 ∷
   rw 4 q13 ∷
   rw⁻ 5 q33 ∷
   rw⁻ 6 q25 ∷
   rw 9 q26 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q27 ∷
   rw 9 q28 ∷
   rw⁻ 8 q27 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q29 ∷
   rw 8 q30 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q27 ∷
   rw 8 q31 ∷
   rw 9 q27 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q29 ∷
   rw 9 q32 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 2 q24 ∷
   rw 1 q22 ∷
   rw 2 q41 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q5 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 7 q5 ∷
   rw 4 q22 ∷
   rw 3 q24 ∷
   rw 4 q42 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 1779 lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CS30 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞中丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞中丞九中九丮") (ℓ "九中九丮丞中丞")
  (rw 3 q14 ∷
   rw 0 q43 ∷
   rw⁻ 0 q16 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 1786 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 139 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丞习丽习举丘丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丞习丽习举丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丞习丽习举丘丞中九丮九") (ℓ "中九丮九丘丞习丽习举丘丞")
  (rw 9 q1 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q7 ∷
   rw 8 q21 ∷
   rw⁻ 7 q22 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q9 ∷
   rw 10 q5 ∷
   rw⁻ 9 q20 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 13 q5 ∷
   rw 10 q7 ∷
   rw 11 q23 ∷
   rw⁻ 10 q24 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q9 ∷
   rw 13 q5 ∷
   rw⁻ 12 q20 ∷
   rw⁻ 6 q25 ∷
   rw 9 q26 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q27 ∷
   rw 9 q28 ∷
   rw⁻ 8 q27 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q29 ∷
   rw 8 q30 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q27 ∷
   rw 8 q31 ∷
   rw 9 q27 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q29 ∷
   rw 9 q32 ∷
   rw 8 q8 ∷
   rw⁻ 11 q33 ∷
   rw 14 q26 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q27 ∷
   rw 14 q34 ∷
   rw⁻ 13 q27 ∷
   re 14 3 (ℓ "丽") ∷
   rw⁻ 12 q29 ∷
   rw 13 q35 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q27 ∷
   rw 13 q36 ∷
   rw 14 q27 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q29 ∷
   rw 14 q32 ∷
   rw 13 q8 ∷
   rw 2 q44 ∷
   rw⁻ 1 q39 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q5 ∷
   rw 2 q7 ∷
   rw 3 q23 ∷
   rw⁻ 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q9 ∷
   rw 5 q5 ∷
   rw⁻ 4 q38 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q38 ∷
   rw⁻ 7 q40 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q7 ∷
   rw 9 q21 ∷
   rw⁻ 8 q22 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q38 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q38 ∷
   rw⁻ 0 q25 ∷
   rw⁻ 1 q33 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q27 ∷
   rw 4 q34 ∷
   rw⁻ 3 q27 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 2 q29 ∷
   rw 3 q35 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q27 ∷
   rw 3 q36 ∷
   rw 4 q27 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q29 ∷
   rw 4 q32 ∷
   rw 3 q13 ∷
   rw⁻ 4 q33 ∷
   rw⁻ 5 q25 ∷
   rw 8 q26 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw⁻ 9 q27 ∷
   rw 8 q28 ∷
   rw⁻ 7 q27 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 6 q29 ∷
   rw 7 q30 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q27 ∷
   rw 7 q31 ∷
   rw 8 q27 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q29 ∷
   rw 8 q32 ∷
   rw 7 q13 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 1 q24 ∷
   rw 0 q22 ∷
   rw 1 q41 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q5 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q5 ∷
   rw 3 q22 ∷
   rw 2 q24 ∷
   rw 3 q42 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q5 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 1785 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF103-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF103 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3 : ⟪ (ℓ "九中九丮丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3 = derive (ℓ "九中九丮丞乡丞") (ℓ "丞乡丞九中九丮")
  (rw 0 q14 ∷
   rw 0 q45 ∷
   rw⁻ 3 q16 ∷ []) Eq.refl
