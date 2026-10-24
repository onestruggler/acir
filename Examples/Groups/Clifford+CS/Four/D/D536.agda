{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD536 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D536 (W : Ws) (Sᴰ : SD536) where

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
  lem-CCZ013-T : St 809
  lem-CCZ013-T = pickᴰ 0 Sᴰ
  lem-CS13-passes-T : St 3
  lem-CS13-passes-T = pickᴰ 1 Sᴰ
  lem-N32-T : St 810
  lem-N32-T = pickᴰ 2 Sᴰ
  lem-comm-CCZ123-CS03 : St 54
  lem-comm-CCZ123-CS03 = pickᴰ 3 Sᴰ
  lem-comm-CCZ012-CZ13 : St 573
  lem-comm-CCZ012-CZ13 = pickᴰ 4 Sᴰ
  lem-comm-CCZ012-CCZ023 : St 811
  lem-comm-CCZ012-CCZ023 = pickᴰ 5 Sᴰ
  lem-pass-CCZ012-vs-CS12 : St 812
  lem-pass-CCZ012-vs-CS12 = pickᴰ 6 Sᴰ
  lem-pass-CCZ012-vs-CSd12 : St 813
  lem-pass-CCZ012-vs-CSd12 = pickᴰ 7 Sᴰ
  lem-pass-CCZ012-vs-CZ12 : St 814
  lem-pass-CCZ012-vs-CZ12 = pickᴰ 8 Sᴰ
  lem-pass-CCZ013-vs-CZ01 : St 815
  lem-pass-CCZ013-vs-CZ01 = pickᴰ 9 Sᴰ
  lem-pass-CS02-vs-CS03 : St 59
  lem-pass-CS02-vs-CS03 = pickᴰ 10 Sᴰ
  lem-pass-CS02-vs-CSd03 : St 816
  lem-pass-CS02-vs-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 12 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 13 Sᴰ
  lem-pass-CSd02-vs-CSd03 : St 817
  lem-pass-CSd02-vs-CSd03 = pickᴰ 14 Sᴰ
  lem-pass-CSd12-vs-CS03 : St 55
  lem-pass-CSd12-vs-CS03 = pickᴰ 15 Sᴰ
  lem-pass-S0-vs-CS03 : St 62
  lem-pass-S0-vs-CS03 = pickᴰ 16 Sᴰ
  lem-pass-S0-vs-CSd03 : St 818
  lem-pass-S0-vs-CSd03 = pickᴰ 17 Sᴰ
  lem-E-T : St 819
  lem-E-T = pickᴰ 18 Sᴰ
  lem-T-T13 : St 820
  lem-T-T13 = pickᴰ 19 Sᴰ
  lem-T1-CZ13-T1 : St 821
  lem-T1-CZ13-T1 = pickᴰ 20 Sᴰ
  lem-pass-CCZ012-vs-CS03 : St 822
  lem-pass-CCZ012-vs-CS03 = pickᴰ 21 Sᴰ
  lem-pass-CCZ013-vs-CCZ012 : St 823
  lem-pass-CCZ013-vs-CCZ012 = pickᴰ 22 Sᴰ
  lem-pass-CCZ023-vs-CCZ012 : St 824
  lem-pass-CCZ023-vs-CCZ012 = pickᴰ 23 Sᴰ

private
  q1 : Eqn
  q1 = wE 105 W
  q2 : Eqn
  q2 = sE 810 lem-N32-T
  q3 : Eqn
  q3 = wE 5 W
  q4 : Eqn
  q4 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = wE 1433 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 76 W
  q11 : Eqn
  q11 = wE 1434 W
  q12 : Eqn
  q12 = wE 29 W
  q13 : Eqn
  q13 = sE 820 lem-T-T13
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 56 W
  q20 : Eqn
  q20 = wE 1435 W
  q21 : Eqn
  q21 = wE 43 W
  q22 : Eqn
  q22 = wE 45 W
  q23 : Eqn
  q23 = sE 3 lem-CS13-passes-T
  q24 : Eqn
  q24 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)

-- N32-PP3: 123 steps
lem-N32-PP3 : ⟪ (ℓ "乖九中九丮乖") ⟫ʷ ≈ ⟪ (ℓ "丽乚乜九中九丮") ⟫ʷ
lem-N32-PP3 = derive (ℓ "乖九中九丮乖") (ℓ "丽乚乜九中九丮")
  (rw 4 q1 ∷
   rw 3 q1 ∷
   rw 2 q1 ∷
   rw 0 q2 ∷
   rw 5 q3 ∷
   rw⁻ 4 q4 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q5 ∷
   rw 4 q6 ∷
   rw⁻ 3 q5 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 2 q4 ∷
   rw 3 q7 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 3 q8 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q9 ∷
   rw 3 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw⁻ 8 q5 ∷
   rw 7 q10 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 6 q11 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 6 q12 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q9 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q15 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q17 ∷
   rw 11 q18 ∷
   rw 10 q17 ∷
   rw 9 q15 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q18 ∷
   rw 7 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q18 ∷
   rw 3 q15 ∷
   rw 4 q19 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q18 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q15 ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q17 ∷
   rw 9 q18 ∷
   rw 8 q17 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q18 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q18 ∷
   rw 1 q15 ∷
   rw 2 q19 ∷
   re 2 8 (ℓ "九") ∷
   rw 2 q20 ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw 3 q21 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q18 ∷
   rw 3 q22 ∷
   rw⁻ 0 q23 ∷
   rw 1 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 819 lem-E-T

-- CCZ123 passes T: 1 steps
lem-CCZ123-passes-T : ⟪ (ℓ "乜九") ⟫ʷ ≈ ⟪ (ℓ "九乜") ⟫ʷ
lem-CCZ123-passes-T = derive (ℓ "乜九") (ℓ "九乜")
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 809 lem-CCZ013-T
  q27 : Eqn
  q27 = sE 54 lem-comm-CCZ123-CS03
  q28 : Eqn
  q28 = wE 251 W
  q29 : Eqn
  q29 = wE 33 W
  q30 : Eqn
  q30 = wE 254 W

-- CCZ013 passes PP3: 103 steps
lem-CCZ013-passes-PP3 : ⟪ (ℓ "乚九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮乚") ⟫ʷ
lem-CCZ013-passes-PP3 = derive (ℓ "乚九中九丮") (ℓ "九中九丮乚")
  (rw 0 q26 ∷
   rw 2 q27 ∷
   rw 3 q14 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q18 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q18 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw 2 q21 ∷
   re 2 5 (ℓ "乙") ∷
   rw 2 q28 ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw 3 q21 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 3 q18 ∷
   rw 3 q25 ∷
   rw 2 q26 ∷
   rw 4 q29 ∷
   rw 5 q14 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q18 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q16 ∷
   rw 9 q14 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q18 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q18 ∷
   rw 6 q16 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q18 ∷
   rw 4 q21 ∷
   re 4 5 (ℓ "乙") ∷
   rw 4 q30 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "丮") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q18 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q18 ∷
   rw 5 q21 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q18 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 821 lem-T1-CZ13-T1
  q32 : Eqn
  q32 = sE 811 lem-comm-CCZ012-CCZ023
  q33 : Eqn
  q33 = sE 573 lem-comm-CCZ012-CZ13
  q34 : Eqn
  q34 = wE 32 W
  q35 : Eqn
  q35 = wE 1436 W

-- B=F: 5 steps
lem-B≡F : ⟪ (ℓ "乙习丿习乙丿") ⟫ʷ ≈ ⟪ (ℓ "乛") ⟫ʷ
lem-B≡F = derive (ℓ "乙习丿习乙丿") (ℓ "乛")
  (rw 1 q31 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 1 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 53 W
  q37 : Eqn
  q37 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q38 : Eqn
  q38 = wE 1339 W
  q39 : Eqn
  q39 = sE 823 lem-pass-CCZ013-vs-CCZ012
  q40 : Eqn
  q40 = wE 54 W
  q41 : Eqn
  q41 = wE 55 W

-- pass [TOFF013] [TOFF012]: 111 steps
lem-pass-TOFF013-vs-TOFF012 : ⟪ (ℓ "乞九") ⟫ʷ ≈ ⟪ (ℓ "九乞") ⟫ʷ
lem-pass-TOFF013-vs-TOFF012 = derive (ℓ "乞九") (ℓ "九乞")
  (rw 1 q36 ∷
   rw 1 q14 ∷
   re 0 1 (ℓ "乏九乏") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q15 ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q15 ∷
   rw⁻ 7 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷
   rw 6 q15 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw 0 q15 ∷
   rw 1 q19 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q36 ∷
   rw⁻ 0 q15 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q18 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q18 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q18 ∷
   rw 2 q21 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw⁻ 2 q37 ∷
   rw 3 q18 ∷
   rw 2 q38 ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 0 q41 ∷
   rw 4 q14 ∷
   rw 3 q37 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q18 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q18 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q18 ∷
   rw 3 q21 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q15 ∷
   rw 2 q41 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q15 ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q17 ∷
   rw 1 q14 ∷
   rw⁻ 2 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q17 ∷
   rw 2 q19 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q18 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 121 W
  q43 : Eqn
  q43 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q44 : Eqn
  q44 = wE 30 W
  q45 : Eqn
  q45 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q46 : Eqn
  q46 = wE 122 W
  q47 : Eqn
  q47 = wE 127 W
  q48 : Eqn
  q48 = wE 118 W
  q49 : Eqn
  q49 = wE 74 W
  q50 : Eqn
  q50 = wE 125 W
  q51 : Eqn
  q51 = wE 128 W
  q52 : Eqn
  q52 = wE 24 W
  q53 : Eqn
  q53 = wE 25 W
  q54 : Eqn
  q54 = wE 26 W
  q55 : Eqn
  q55 = wE 129 W
  q56 : Eqn
  q56 = sE 824 lem-pass-CCZ023-vs-CCZ012
  q57 : Eqn
  q57 = wE 119 W
  q58 : Eqn
  q58 = wE 1437 W
  q59 : Eqn
  q59 = wE 123 W
  q60 : Eqn
  q60 = wE 124 W

-- pass [TOFF023] [TOFF012]: 119 steps
lem-pass-TOFF023-vs-TOFF012 : ⟪ (ℓ "也九") ⟫ʷ ≈ ⟪ (ℓ "九也") ⟫ʷ
lem-pass-TOFF023-vs-TOFF012 = derive (ℓ "也九") (ℓ "九也")
  (rw 1 q36 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "並乢並") ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   rw 4 q44 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q8 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q42 ∷
   rw 7 q46 ∷
   rw 8 q9 ∷
   rw 7 q47 ∷
   rw 6 q48 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q6 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q49 ∷
   rw⁻ 3 q45 ∷
   rw 2 q49 ∷
   rw⁻ 1 q43 ∷
   rw 0 q48 ∷
   rw 1 q50 ∷
   re 1 8 (ℓ "乢") ∷
   rw 1 q51 ∷
   rw 0 q42 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   rw 4 q44 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q8 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q3 ∷
   rw 2 q43 ∷
   rw 3 q52 ∷
   rw 4 q45 ∷
   rw 5 q52 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q53 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q54 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q55 ∷
   rw 3 q9 ∷
   rw 2 q38 ∷
   rw 1 q56 ∷
   rw 2 q40 ∷
   rw 0 q41 ∷
   rw 4 q3 ∷
   rw 3 q57 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 5 q44 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q8 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q5 ∷
   rw 7 q6 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q49 ∷
   rw⁻ 4 q45 ∷
   rw 3 q49 ∷
   rw⁻ 2 q43 ∷
   rw 3 q54 ∷
   re 3 5 (ℓ "乜") ∷
   rw 1 q48 ∷
   rw 2 q58 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q42 ∷
   rw 2 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 5 q44 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q8 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q42 ∷
   rw 8 q46 ∷
   rw 1 q3 ∷
   rw 2 q59 ∷
   rw 3 q43 ∷
   rw 4 q52 ∷
   rw 5 q45 ∷
   rw 6 q52 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 8 q53 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q59 ∷
   rw 9 q60 ∷
   rw 2 q50 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 823 lem-pass-CCZ013-vs-CCZ012

-- pass [CCZ012] [CCZ013]: 1 steps
lem-pass-CCZ012-vs-CCZ013 : ⟪ (ℓ "乙乚") ⟫ʷ ≈ ⟪ (ℓ "乚乙") ⟫ʷ
lem-pass-CCZ012-vs-CCZ013 = derive (ℓ "乙乚") (ℓ "乚乙")
  (rw⁻ 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 469 W
  q63 : Eqn
  q63 = sE 822 lem-pass-CCZ012-vs-CS03
  q64 : Eqn
  q64 = sE 21 lem-pass-CS12-vs-CS03
  q65 : Eqn
  q65 = sE 59 lem-pass-CS02-vs-CS03
  q66 : Eqn
  q66 = wE 466 W
  q67 : Eqn
  q67 = wE 90 W
  q68 : Eqn
  q68 = sE 812 lem-pass-CCZ012-vs-CS12
  q69 : Eqn
  q69 = sE 814 lem-pass-CCZ012-vs-CZ12
  q70 : Eqn
  q70 = wE 1438 W
  q71 : Eqn
  q71 = sE 816 lem-pass-CS02-vs-CSd03

-- pass [CS02] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丧九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丧") ⟫ʷ
lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丧九中九丮") (ℓ "九中九丮丧")
  (rw 0 q62 ∷
   rw 3 q63 ∷
   rw 2 q64 ∷
   rw 1 q65 ∷
   rw 4 q66 ∷
   rw 3 q67 ∷
   rw 2 q62 ∷
   rw 5 q68 ∷
   rw 6 q69 ∷
   rw 4 q70 ∷
   rw 4 q34 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1439 W
  q73 : Eqn
  q73 = sE 55 lem-pass-CSd12-vs-CS03
  q74 : Eqn
  q74 = sE 60 lem-pass-CSd02-vs-CS03
  q75 : Eqn
  q75 = wE 468 W
  q76 : Eqn
  q76 = sE 813 lem-pass-CCZ012-vs-CSd12
  q77 : Eqn
  q77 = wE 1440 W
  q78 : Eqn
  q78 = sE 817 lem-pass-CSd02-vs-CSd03

-- pass [CSd02] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丨九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丨") ⟫ʷ
lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丨九中九丮") (ℓ "九中九丮丨")
  (rw 0 q72 ∷
   rw 3 q63 ∷
   rw 2 q73 ∷
   rw 1 q74 ∷
   rw 4 q66 ∷
   rw 3 q75 ∷
   rw 2 q72 ∷
   rw 5 q76 ∷
   rw 6 q69 ∷
   rw 4 q77 ∷
   rw 4 q34 ∷
   rw 3 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1441 W
  q80 : Eqn
  q80 = sE 815 lem-pass-CCZ013-vs-CZ01
  q81 : Eqn
  q81 = wE 1442 W

-- pass [TOFF013] [X2 TOFF012 X2]: 112 steps
lem-pass-TOFF013-vs-X2-TOFF012-X2 : ⟪ (ℓ "乞丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘乞") ⟫ʷ
lem-pass-TOFF013-vs-X2-TOFF012-X2 = derive (ℓ "乞丘九丘") (ℓ "丘九丘乞")
  (rw 1 q79 ∷
   rw 1 q14 ∷
   re 0 1 (ℓ "乏九乏") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q15 ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q15 ∷
   rw⁻ 7 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷
   rw 6 q15 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw 0 q15 ∷
   rw 1 q19 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q36 ∷
   rw⁻ 0 q15 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q18 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q18 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q18 ∷
   rw 2 q21 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw⁻ 2 q37 ∷
   rw 3 q18 ∷
   rw 2 q38 ∷
   rw 1 q80 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 0 q81 ∷
   rw 6 q14 ∷
   rw 5 q37 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q18 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q18 ∷
   rw 7 q16 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q18 ∷
   rw 5 q21 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q15 ∷
   rw 4 q41 ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q15 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q17 ∷
   rw 3 q14 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q18 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q18 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q17 ∷
   rw 4 q19 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 4 q18 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 1443 W
  q83 : Eqn
  q83 = sE 62 lem-pass-S0-vs-CS03
  q84 : Eqn
  q84 = sE 818 lem-pass-S0-vs-CSd03

-- pass [S0] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丈九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丈") ⟫ʷ
lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丈九中九丮") (ℓ "九中九丮丈")
  (rw 0 q82 ∷
   rw 3 q63 ∷
   rw 2 q64 ∷
   rw 1 q83 ∷
   rw 4 q66 ∷
   rw 3 q67 ∷
   rw 2 q82 ∷
   rw 5 q68 ∷
   rw 6 q69 ∷
   rw 4 q70 ∷
   rw 4 q34 ∷
   rw 3 q84 ∷ []) Eq.refl
