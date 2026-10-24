{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D016 (W : Ws) where

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
  q3 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 297 W

-- pass [X1 CS10 X1] [CS03]: 13 steps
lem-pass-X1-CS10-X1-vs-CS03 : ⟪ (ℓ "丒丠丒中") ⟫ʷ ≈ ⟪ (ℓ "中丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-CS03 = derive (ℓ "丒丠丒中") (ℓ "中丒丠丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 298 W

-- pass [X1 CS10 X1] [CSd03]: 13 steps
lem-pass-X1-CS10-X1-vs-CSd03 : ⟪ (ℓ "丒丠丒丮") ⟫ʷ ≈ ⟪ (ℓ "丮丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-CSd03 = derive (ℓ "丒丠丒丮") (ℓ "丮丒丠丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丮") ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 196 W
  q12 : Eqn
  q12 = wE 299 W
  q13 : Eqn
  q13 = wE 175 W

-- pass [CS13] [X3 TOFF103 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF103-X3 : ⟪ (ℓ "丽丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF103-X3 = derive (ℓ "丽丞乡丞") (ℓ "丞乡丞丽")
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q9 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q2 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q2 ∷
   rw 4 q9 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 2 q8 ∷
   rw 3 q11 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q7 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q8 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q1 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   rw⁻ 4 q9 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q2 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q11 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q13 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 300 W

-- pass [CSd13] [X3 TOFF103 X3]: 65 steps
lem-pass-CSd13-vs-X3-TOFF103-X3 : ⟪ (ℓ "举丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞举") ⟫ʷ
lem-pass-CSd13-vs-X3-TOFF103-X3 = derive (ℓ "举丞乡丞") (ℓ "丞乡丞举")
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q9 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q2 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q2 ∷
   rw 4 q9 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 2 q8 ∷
   rw 3 q11 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q7 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q2 ∷
   rw 1 q14 ∷
   rw 0 q13 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q8 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q1 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   rw⁻ 4 q9 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q2 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q11 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q13 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 93 W

-- pass [CS12] [CS13]: 1 steps
lem-pass-CS12-vs-CS13 : ⟪ (ℓ "丶丽") ⟫ʷ ≈ ⟪ (ℓ "丽丶") ⟫ʷ
lem-pass-CS12-vs-CS13 = derive (ℓ "丶丽") (ℓ "丽丶")
  (rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 301 W

-- pass [CCZ012] [CZ02]: 1 steps
lem-pass-CCZ012-vs-CZ02 : ⟪ (ℓ "乙丩") ⟫ʷ ≈ ⟪ (ℓ "丩乙") ⟫ʷ
lem-pass-CCZ012-vs-CZ02 = derive (ℓ "乙丩") (ℓ "丩乙")
  (rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 302 W

-- pass [CS12] [CZ02]: 1 steps
lem-pass-CS12-vs-CZ02 : ⟪ (ℓ "丶丩") ⟫ʷ ≈ ⟪ (ℓ "丩丶") ⟫ʷ
lem-pass-CS12-vs-CZ02 = derive (ℓ "丶丩") (ℓ "丩丶")
  (rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 86 W

-- pass [CS12] [CSd13]: 1 steps
lem-pass-CS12-vs-CSd13 : ⟪ (ℓ "丶举") ⟫ʷ ≈ ⟪ (ℓ "举丶") ⟫ʷ
lem-pass-CS12-vs-CSd13 = derive (ℓ "丶举") (ℓ "举丶")
  (rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 179 W

-- pass [CSd12] [CS13]: 1 steps
lem-pass-CSd12-vs-CS13 : ⟪ (ℓ "丷丽") ⟫ʷ ≈ ⟪ (ℓ "丽丷") ⟫ʷ
lem-pass-CSd12-vs-CS13 = derive (ℓ "丷丽") (ℓ "丽丷")
  (rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 303 W

-- pass [CSd12] [CZ02]: 1 steps
lem-pass-CSd12-vs-CZ02 : ⟪ (ℓ "丷丩") ⟫ʷ ≈ ⟪ (ℓ "丩丷") ⟫ʷ
lem-pass-CSd12-vs-CZ02 = derive (ℓ "丷丩") (ℓ "丩丷")
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 181 W

-- pass [CSd12] [CSd13]: 1 steps
lem-pass-CSd12-vs-CSd13 : ⟪ (ℓ "丷举") ⟫ʷ ≈ ⟪ (ℓ "举丷") ⟫ʷ
lem-pass-CSd12-vs-CSd13 = derive (ℓ "丷举") (ℓ "举丷")
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 304 W

-- pass [X3 CSd31 X3] [TOFF103]: 65 steps
lem-pass-X3-CSd31-X3-vs-TOFF103 : ⟪ (ℓ "丞举丞乡") ⟫ʷ ≈ ⟪ (ℓ "乡丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF103 = derive (ℓ "丞举丞乡") (ℓ "乡丞举丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q8 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q9 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q10 ∷
   rw 11 q2 ∷
   rw 10 q10 ∷
   rw 9 q8 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q2 ∷
   rw 3 q8 ∷
   rw 4 q11 ∷
   re 4 8 (ℓ "习") ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q2 ∷
   rw 0 q7 ∷
   rw 1 q22 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q10 ∷
   rw 0 q1 ∷
   rw⁻ 1 q8 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw⁻ 3 q9 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q2 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q11 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q13 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q13 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 249 W

-- pass [X3 CSd31 X3] [CS12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CS12 : ⟪ (ℓ "丞举丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS12 = derive (ℓ "丞举丞丶") (ℓ "丶丞举丞")
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 250 W

-- pass [X3 CSd31 X3] [CSd12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CSd12 : ⟪ (ℓ "丞举丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CSd12 = derive (ℓ "丞举丞丷") (ℓ "丷丞举丞")
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 305 W

-- pass [TOFF102] [X2 TOFF102 X2]: 1 steps
lem-pass-TOFF102-vs-X2-TOFF102-X2 : ⟪ (ℓ "习丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘习") ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF102-X2 = derive (ℓ "习丘习丘") (ℓ "丘习丘习")
  (rw 0 q25 ∷ []) Eq.refl

-- pass [CS12] [X2 TOFF102 X2]: 1 steps
lem-pass-CS12-vs-X2-TOFF102-X2 : ⟪ (ℓ "丶丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丶") ⟫ʷ
lem-pass-CS12-vs-X2-TOFF102-X2 = derive (ℓ "丶丘习丘") (ℓ "丘习丘丶")
  (rw 0 q12 ∷ []) Eq.refl

-- pass [CSd12] [X2 TOFF102 X2]: 1 steps
lem-pass-CSd12-vs-X2-TOFF102-X2 : ⟪ (ℓ "丷丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丷") ⟫ʷ
lem-pass-CSd12-vs-X2-TOFF102-X2 = derive (ℓ "丷丘习丘") (ℓ "丘习丘丷")
  (rw 0 q14 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 43 W

-- pass [CCZ013] [CZ03]: 49 steps
lem-pass-CCZ013-vs-CZ03 : ⟪ (ℓ "乚丯") ⟫ʷ ≈ ⟪ (ℓ "丯乚") ⟫ʷ
lem-pass-CCZ013-vs-CZ03 = derive (ℓ "乚丯") (ℓ "丯乚")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丩乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw 1 q26 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q16 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丯") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw⁻ 3 q9 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q2 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [CS13] [CZ03]: 11 steps
lem-pass-CS13-vs-CZ03 : ⟪ (ℓ "丽丯") ⟫ʷ ≈ ⟪ (ℓ "丯丽") ⟫ʷ
lem-pass-CS13-vs-CZ03 = derive (ℓ "丽丯") (ℓ "丯丽")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丩乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw 1 q17 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丯") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [CSd13] [CZ03]: 11 steps
lem-pass-CSd13-vs-CZ03 : ⟪ (ℓ "举丯") ⟫ʷ ≈ ⟪ (ℓ "丯举") ⟫ʷ
lem-pass-CSd13-vs-CZ03 = derive (ℓ "举丯") (ℓ "丯举")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丩乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q2 ∷
   rw 1 q20 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丯") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [X2 CSd21 X2] [TOFF102]: 1 steps
lem-pass-X2-CSd21-X2-vs-TOFF102 : ⟪ (ℓ "丘丷丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF102 = derive (ℓ "丘丷丘习") (ℓ "习丘丷丘")
  (rw 0 q22 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 287 W

-- pass [X2 CSd21 X2] [CS13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CS13 : ⟪ (ℓ "丘丷丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13 = derive (ℓ "丘丷丘丽") (ℓ "丽丘丷丘")
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 288 W

-- pass [X2 CSd21 X2] [CSd13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CSd13 : ⟪ (ℓ "丘丷丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CSd13 = derive (ℓ "丘丷丘举") (ℓ "举丘丷丘")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 306 W

-- pass [S1] [CS13]: 1 steps
lem-pass-S1-vs-CS13 : ⟪ (ℓ "与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与") ⟫ʷ
lem-pass-S1-vs-CS13 = derive (ℓ "与丽") (ℓ "丽与")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 251 W

-- pass [CCZ012] [CS02]: 1 steps
lem-pass-CCZ012-vs-CS02 : ⟪ (ℓ "乙丧") ⟫ʷ ≈ ⟪ (ℓ "丧乙") ⟫ʷ
lem-pass-CCZ012-vs-CS02 = derive (ℓ "乙丧") (ℓ "丧乙")
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 307 W

-- pass [S1] [CSd13]: 1 steps
lem-pass-S1-vs-CSd13 : ⟪ (ℓ "与举") ⟫ʷ ≈ ⟪ (ℓ "举与") ⟫ʷ
lem-pass-S1-vs-CSd13 = derive (ℓ "与举") (ℓ "举与")
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 308 W

-- pass [Sd1] [CS13]: 1 steps
lem-pass-Sd1-vs-CS13 : ⟪ (ℓ "丏丽") ⟫ʷ ≈ ⟪ (ℓ "丽丏") ⟫ʷ
lem-pass-Sd1-vs-CS13 = derive (ℓ "丏丽") (ℓ "丽丏")
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 254 W

-- pass [CCZ012] [CSd02]: 1 steps
lem-pass-CCZ012-vs-CSd02 : ⟪ (ℓ "乙丨") ⟫ʷ ≈ ⟪ (ℓ "丨乙") ⟫ʷ
lem-pass-CCZ012-vs-CSd02 = derive (ℓ "乙丨") (ℓ "丨乙")
  (rw 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 309 W

-- pass [Sd1] [CSd13]: 1 steps
lem-pass-Sd1-vs-CSd13 : ⟪ (ℓ "丏举") ⟫ʷ ≈ ⟪ (ℓ "举丏") ⟫ʷ
lem-pass-Sd1-vs-CSd13 = derive (ℓ "丏举") (ℓ "举丏")
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q36 : Eqn
  q36 = wE 27 W
  q37 : Eqn
  q37 = wE 31 W
  q38 : Eqn
  q38 = wE 310 W

-- bridge G-pp: 43 steps
lem-bridge-G-pp : ⟪ (ℓ "九並乏丶乏並九並乏丶丶丶乏並") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-bridge-G-pp = derive (ℓ "九並乏丶乏並九並乏丶丶丶乏並") (ℓ "九中九丮")
  (rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q35 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q37 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 5 q35 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q35 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q37 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   rw 4 q38 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 311 W

-- sw0 S0: 2 steps
lem-sw0-S0 : ⟪ (ℓ "並丈並") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
lem-sw0-S0 = derive (ℓ "並丈並") (ℓ "与")
  (rw 0 q39 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 312 W

-- sw0 Sd0: 2 steps
lem-sw0-Sd0 : ⟪ (ℓ "並三並") ⟫ʷ ≈ ⟪ (ℓ "丏") ⟫ʷ
lem-sw0-Sd0 = derive (ℓ "並三並") (ℓ "丏")
  (rw 0 q40 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 123 W

-- sw0 K0: 2 steps
lem-sw0-K0 : ⟪ (ℓ "並上並") ⟫ʷ ≈ ⟪ (ℓ "丐") ⟫ʷ
lem-sw0-K0 = derive (ℓ "並上並") (ℓ "丐")
  (rw 0 q41 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 313 W

-- sw0 Kd0: 2 steps
lem-sw0-Kd0 : ⟪ (ℓ "並下並") ⟫ʷ ≈ ⟪ (ℓ "丑") ⟫ʷ
lem-sw0-Kd0 = derive (ℓ "並下並") (ℓ "丑")
  (rw 0 q42 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 220 W

-- sw0 X0: 2 steps
lem-sw0-X0 : ⟪ (ℓ "並丌並") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-sw0-X0 = derive (ℓ "並丌並") (ℓ "丒")
  (rw 0 q43 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 314 W

-- sw0 Z0: 2 steps
lem-sw0-Z0 : ⟪ (ℓ "並不並") ⟫ʷ ≈ ⟪ (ℓ "专") ⟫ʷ
lem-sw0-Z0 = derive (ℓ "並不並") (ℓ "专")
  (rw 0 q44 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 315 W

-- sw0 S1: 2 steps
lem-sw0-S1 : ⟪ (ℓ "並与並") ⟫ʷ ≈ ⟪ (ℓ "丈") ⟫ʷ
lem-sw0-S1 = derive (ℓ "並与並") (ℓ "丈")
  (rw 0 q45 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 316 W

-- sw0 Sd1: 2 steps
lem-sw0-Sd1 : ⟪ (ℓ "並丏並") ⟫ʷ ≈ ⟪ (ℓ "三") ⟫ʷ
lem-sw0-Sd1 = derive (ℓ "並丏並") (ℓ "三")
  (rw 0 q46 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 121 W

-- sw0 K1: 2 steps
lem-sw0-K1 : ⟪ (ℓ "並丐並") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
lem-sw0-K1 = derive (ℓ "並丐並") (ℓ "上")
  (rw 0 q47 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 129 W

-- sw0 Kd1: 2 steps
lem-sw0-Kd1 : ⟪ (ℓ "並丑並") ⟫ʷ ≈ ⟪ (ℓ "下") ⟫ʷ
lem-sw0-Kd1 = derive (ℓ "並丑並") (ℓ "下")
  (rw 0 q48 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 317 W

-- sw0 X1: 2 steps
lem-sw0-X1 : ⟪ (ℓ "並丒並") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-sw0-X1 = derive (ℓ "並丒並") (ℓ "丌")
  (rw 0 q49 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 318 W

-- sw0 Z1: 2 steps
lem-sw0-Z1 : ⟪ (ℓ "並专並") ⟫ʷ ≈ ⟪ (ℓ "不") ⟫ʷ
lem-sw0-Z1 = derive (ℓ "並专並") (ℓ "不")
  (rw 0 q50 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))

-- sw0 S2: 2 steps
lem-sw0-S2 : ⟪ (ℓ "並且並") ⟫ʷ ≈ ⟪ (ℓ "且") ⟫ʷ
lem-sw0-S2 = derive (ℓ "並且並") (ℓ "且")
  (rw 0 q51 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (ℓ "並丕") (ℓ "丕並") (low-comm (Swap) ((S • S • S)))

-- sw0 Sd2: 2 steps
lem-sw0-Sd2 : ⟪ (ℓ "並丕並") ⟫ʷ ≈ ⟪ (ℓ "丕") ⟫ʷ
lem-sw0-Sd2 = derive (ℓ "並丕並") (ℓ "丕")
  (rw 0 q52 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))

-- sw0 K2: 2 steps
lem-sw0-K2 : ⟪ (ℓ "並世並") ⟫ʷ ≈ ⟪ (ℓ "世") ⟫ʷ
lem-sw0-K2 = derive (ℓ "並世並") (ℓ "世")
  (rw 0 q53 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "並丗") (ℓ "丗並") (low-comm (Swap) ((K • iI)))

-- sw0 Kd2: 2 steps
lem-sw0-Kd2 : ⟪ (ℓ "並丗並") ⟫ʷ ≈ ⟪ (ℓ "丗") ⟫ʷ
lem-sw0-Kd2 = derive (ℓ "並丗並") (ℓ "丗")
  (rw 0 q54 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))

-- sw0 X2: 2 steps
lem-sw0-X2 : ⟪ (ℓ "並丘並") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-sw0-X2 = derive (ℓ "並丘並") (ℓ "丘")
  (rw 0 q55 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (ℓ "並丙") (ℓ "丙並") (low-comm (Swap) (Z))

-- sw0 Z2: 2 steps
lem-sw0-Z2 : ⟪ (ℓ "並丙並") ⟫ʷ ≈ ⟪ (ℓ "丙") ⟫ʷ
lem-sw0-Z2 = derive (ℓ "並丙並") (ℓ "丙")
  (rw 0 q56 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))

-- sw0 S3: 2 steps
lem-sw0-S3 : ⟪ (ℓ "並业並") ⟫ʷ ≈ ⟪ (ℓ "业") ⟫ʷ
lem-sw0-S3 = derive (ℓ "並业並") (ℓ "业")
  (rw 0 q57 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (ℓ "並丛") (ℓ "丛並") (low-comm (Swap) (((S • S • S) ↑)))

-- sw0 Sd3: 2 steps
lem-sw0-Sd3 : ⟪ (ℓ "並丛並") ⟫ʷ ≈ ⟪ (ℓ "丛") ⟫ʷ
lem-sw0-Sd3 = derive (ℓ "並丛並") (ℓ "丛")
  (rw 0 q58 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))

-- sw0 K3: 2 steps
lem-sw0-K3 : ⟪ (ℓ "並东並") ⟫ʷ ≈ ⟪ (ℓ "东") ⟫ʷ
lem-sw0-K3 = derive (ℓ "並东並") (ℓ "东")
  (rw 0 q59 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (ℓ "並丝") (ℓ "丝並") (low-comm (Swap) (((K • iI) ↑)))

-- sw0 Kd3: 2 steps
lem-sw0-Kd3 : ⟪ (ℓ "並丝並") ⟫ʷ ≈ ⟪ (ℓ "丝") ⟫ʷ
lem-sw0-Kd3 = derive (ℓ "並丝並") (ℓ "丝")
  (rw 0 q60 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))

-- sw0 X3: 2 steps
lem-sw0-X3 : ⟪ (ℓ "並丞並") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-sw0-X3 = derive (ℓ "並丞並") (ℓ "丞")
  (rw 0 q61 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (ℓ "並丟") (ℓ "丟並") (low-comm (Swap) ((Z ↑)))

-- sw0 Z3: 2 steps
lem-sw0-Z3 : ⟪ (ℓ "並丟並") ⟫ʷ ≈ ⟪ (ℓ "丟") ⟫ʷ
lem-sw0-Z3 = derive (ℓ "並丟並") (ℓ "丟")
  (rw 0 q62 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 219 W

-- sw0 CS01: 2 steps
lem-sw0-CS01 : ⟪ (ℓ "並丠並") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
lem-sw0-CS01 = derive (ℓ "並丠並") (ℓ "丠")
  (rw 0 q63 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 319 W

-- sw0 CSd01: 2 steps
lem-sw0-CSd01 : ⟪ (ℓ "並両並") ⟫ʷ ≈ ⟪ (ℓ "両") ⟫ʷ
lem-sw0-CSd01 = derive (ℓ "並両並") (ℓ "両")
  (rw 0 q64 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 320 W

-- sw0 CZ01: 2 steps
lem-sw0-CZ01 : ⟪ (ℓ "並丢並") ⟫ʷ ≈ ⟪ (ℓ "丢") ⟫ʷ
lem-sw0-CZ01 = derive (ℓ "並丢並") (ℓ "丢")
  (rw 0 q65 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 28 W

-- sw0 CX01: 2 steps
lem-sw0-CX01 : ⟪ (ℓ "並丣並") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
lem-sw0-CX01 = derive (ℓ "並丣並") (ℓ "丳")
  (rw 0 q66 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 221 W

-- sw0 CK01: 2 steps
lem-sw0-CK01 : ⟪ (ℓ "並两並") ⟫ʷ ≈ ⟪ (ℓ "临") ⟫ʷ
lem-sw0-CK01 = derive (ℓ "並两並") (ℓ "临")
  (rw 0 q67 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 321 W

-- sw0 CKd01: 2 steps
lem-sw0-CKd01 : ⟪ (ℓ "並严並") ⟫ʷ ≈ ⟪ (ℓ "丵") ⟫ʷ
lem-sw0-CKd01 = derive (ℓ "並严並") (ℓ "丵")
  (rw 0 q68 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 25 W

-- sw0 CS02: 2 steps
lem-sw0-CS02 : ⟪ (ℓ "並丧並") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
lem-sw0-CS02 = derive (ℓ "並丧並") (ℓ "丶")
  (rw 0 q69 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 322 W

-- sw0 CSd02: 2 steps
lem-sw0-CSd02 : ⟪ (ℓ "並丨並") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
lem-sw0-CSd02 = derive (ℓ "並丨並") (ℓ "丷")
  (rw 0 q70 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 323 W

-- sw0 CZ02: 2 steps
lem-sw0-CZ02 : ⟪ (ℓ "並丩並") ⟫ʷ ≈ ⟪ (ℓ "丸") ⟫ʷ
lem-sw0-CZ02 = derive (ℓ "並丩並") (ℓ "丸")
  (rw 0 q71 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 24 W

-- sw0 CX02: 2 steps
lem-sw0-CX02 : ⟪ (ℓ "並个並") ⟫ʷ ≈ ⟪ (ℓ "丹") ⟫ʷ
lem-sw0-CX02 = derive (ℓ "並个並") (ℓ "丹")
  (rw 0 q72 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 324 W

-- sw0 CK02: 2 steps
lem-sw0-CK02 : ⟪ (ℓ "並丫並") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
lem-sw0-CK02 = derive (ℓ "並丫並") (ℓ "为")
  (rw 0 q73 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 325 W

-- sw0 CKd02: 2 steps
lem-sw0-CKd02 : ⟪ (ℓ "並丬並") ⟫ʷ ≈ ⟪ (ℓ "主") ⟫ʷ
lem-sw0-CKd02 = derive (ℓ "並丬並") (ℓ "主")
  (rw 0 q74 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS03: 6 steps
lem-sw0-CS03 : ⟪ (ℓ "並中並") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
lem-sw0-CS03 = derive (ℓ "並中並") (ℓ "丽")
  (re 1 1 (ℓ "乏丧乏") ∷
   rw 0 q35 ∷
   rw 1 q69 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丽") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CSd03: 6 steps
lem-sw0-CSd03 : ⟪ (ℓ "並丮並") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
lem-sw0-CSd03 = derive (ℓ "並丮並") (ℓ "举")
  (re 1 1 (ℓ "乏丨乏") ∷
   rw 0 q35 ∷
   rw 1 q70 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "举") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CZ03: 6 steps
lem-sw0-CZ03 : ⟪ (ℓ "並丯並") ⟫ʷ ≈ ⟪ (ℓ "丿") ⟫ʷ
lem-sw0-CZ03 = derive (ℓ "並丯並") (ℓ "丿")
  (re 1 1 (ℓ "乏丩乏") ∷
   rw 0 q35 ∷
   rw 1 q71 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丿") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX03: 6 steps
lem-sw0-CX03 : ⟪ (ℓ "並丰並") ⟫ʷ ≈ ⟪ (ℓ "乀") ⟫ʷ
lem-sw0-CX03 = derive (ℓ "並丰並") (ℓ "乀")
  (re 1 1 (ℓ "乏个乏") ∷
   rw 0 q35 ∷
   rw 1 q72 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乀") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK03: 6 steps
lem-sw0-CK03 : ⟪ (ℓ "並丱並") ⟫ʷ ≈ ⟪ (ℓ "乁") ⟫ʷ
lem-sw0-CK03 = derive (ℓ "並丱並") (ℓ "乁")
  (re 1 1 (ℓ "乏丫乏") ∷
   rw 0 q35 ∷
   rw 1 q73 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乁") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd03: 6 steps
lem-sw0-CKd03 : ⟪ (ℓ "並串並") ⟫ʷ ≈ ⟪ (ℓ "乂") ⟫ʷ
lem-sw0-CKd03 = derive (ℓ "並串並") (ℓ "乂")
  (re 1 1 (ℓ "乏丬乏") ∷
   rw 0 q35 ∷
   rw 1 q74 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乂") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 326 W

-- sw0 CX10: 2 steps
lem-sw0-CX10 : ⟪ (ℓ "並丳並") ⟫ʷ ≈ ⟪ (ℓ "丣") ⟫ʷ
lem-sw0-CX10 = derive (ℓ "並丳並") (ℓ "丣")
  (rw 0 q75 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 327 W

-- sw0 CK10: 2 steps
lem-sw0-CK10 : ⟪ (ℓ "並临並") ⟫ʷ ≈ ⟪ (ℓ "两") ⟫ʷ
lem-sw0-CK10 = derive (ℓ "並临並") (ℓ "两")
  (rw 0 q76 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 328 W

-- sw0 CKd10: 2 steps
lem-sw0-CKd10 : ⟪ (ℓ "並丵並") ⟫ʷ ≈ ⟪ (ℓ "严") ⟫ʷ
lem-sw0-CKd10 = derive (ℓ "並丵並") (ℓ "严")
  (rw 0 q77 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS12: 2 steps
lem-sw0-CS12 : ⟪ (ℓ "並丶並") ⟫ʷ ≈ ⟪ (ℓ "丧") ⟫ʷ
lem-sw0-CS12 = derive (ℓ "並丶並") (ℓ "丧")
  (rw 0 q36 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 29 W

-- sw0 CSd12: 2 steps
lem-sw0-CSd12 : ⟪ (ℓ "並丷並") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
lem-sw0-CSd12 = derive (ℓ "並丷並") (ℓ "丨")
  (rw 0 q78 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 191 W

-- sw0 CZ12: 2 steps
lem-sw0-CZ12 : ⟪ (ℓ "並丸並") ⟫ʷ ≈ ⟪ (ℓ "丩") ⟫ʷ
lem-sw0-CZ12 = derive (ℓ "並丸並") (ℓ "丩")
  (rw 0 q79 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 30 W

-- sw0 CX12: 2 steps
lem-sw0-CX12 : ⟪ (ℓ "並丹並") ⟫ʷ ≈ ⟪ (ℓ "个") ⟫ʷ
lem-sw0-CX12 = derive (ℓ "並丹並") (ℓ "个")
  (rw 0 q80 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 329 W

-- sw0 CK12: 2 steps
lem-sw0-CK12 : ⟪ (ℓ "並为並") ⟫ʷ ≈ ⟪ (ℓ "丫") ⟫ʷ
lem-sw0-CK12 = derive (ℓ "並为並") (ℓ "丫")
  (rw 0 q81 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 330 W

-- sw0 CKd12: 2 steps
lem-sw0-CKd12 : ⟪ (ℓ "並主並") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
lem-sw0-CKd12 = derive (ℓ "並主並") (ℓ "丬")
  (rw 0 q82 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS13: 6 steps
lem-sw0-CS13 : ⟪ (ℓ "並丽並") ⟫ʷ ≈ ⟪ (ℓ "中") ⟫ʷ
lem-sw0-CS13 = derive (ℓ "並丽並") (ℓ "中")
  (re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CSd13: 6 steps
lem-sw0-CSd13 : ⟪ (ℓ "並举並") ⟫ʷ ≈ ⟪ (ℓ "丮") ⟫ʷ
lem-sw0-CSd13 = derive (ℓ "並举並") (ℓ "丮")
  (re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q35 ∷
   rw 1 q78 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CZ13: 6 steps
lem-sw0-CZ13 : ⟪ (ℓ "並丿並") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
lem-sw0-CZ13 = derive (ℓ "並丿並") (ℓ "丯")
  (re 1 1 (ℓ "乏丸乏") ∷
   rw 0 q35 ∷
   rw 1 q79 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丯") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX13: 6 steps
lem-sw0-CX13 : ⟪ (ℓ "並乀並") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
lem-sw0-CX13 = derive (ℓ "並乀並") (ℓ "丰")
  (re 1 1 (ℓ "乏丹乏") ∷
   rw 0 q35 ∷
   rw 1 q80 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丰") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK13: 6 steps
lem-sw0-CK13 : ⟪ (ℓ "並乁並") ⟫ʷ ≈ ⟪ (ℓ "丱") ⟫ʷ
lem-sw0-CK13 = derive (ℓ "並乁並") (ℓ "丱")
  (re 1 1 (ℓ "乏为乏") ∷
   rw 0 q35 ∷
   rw 1 q81 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "丱") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd13: 6 steps
lem-sw0-CKd13 : ⟪ (ℓ "並乂並") ⟫ʷ ≈ ⟪ (ℓ "串") ⟫ʷ
lem-sw0-CKd13 = derive (ℓ "並乂並") (ℓ "串")
  (re 1 1 (ℓ "乏主乏") ∷
   rw 0 q35 ∷
   rw 1 q82 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "串") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 331 W

-- sw0 CX20: 2 steps
lem-sw0-CX20 : ⟪ (ℓ "並乃並") ⟫ʷ ≈ ⟪ (ℓ "乆") ⟫ʷ
lem-sw0-CX20 = derive (ℓ "並乃並") (ℓ "乆")
  (rw 0 q83 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 275 W

-- sw0 CK20: 2 steps
lem-sw0-CK20 : ⟪ (ℓ "並乄並") ⟫ʷ ≈ ⟪ (ℓ "乇") ⟫ʷ
lem-sw0-CK20 = derive (ℓ "並乄並") (ℓ "乇")
  (rw 0 q84 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 332 W

-- sw0 CKd20: 2 steps
lem-sw0-CKd20 : ⟪ (ℓ "並久並") ⟫ʷ ≈ ⟪ (ℓ "么") ⟫ʷ
lem-sw0-CKd20 = derive (ℓ "並久並") (ℓ "么")
  (rw 0 q85 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 39 W

-- sw0 CX21: 2 steps
lem-sw0-CX21 : ⟪ (ℓ "並乆並") ⟫ʷ ≈ ⟪ (ℓ "乃") ⟫ʷ
lem-sw0-CX21 = derive (ℓ "並乆並") (ℓ "乃")
  (rw 0 q86 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 142 W

-- sw0 CK21: 2 steps
lem-sw0-CK21 : ⟪ (ℓ "並乇並") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
lem-sw0-CK21 = derive (ℓ "並乇並") (ℓ "乄")
  (rw 0 q87 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = wE 139 W

-- sw0 CKd21: 2 steps
lem-sw0-CKd21 : ⟪ (ℓ "並么並") ⟫ʷ ≈ ⟪ (ℓ "久") ⟫ʷ
lem-sw0-CKd21 = derive (ℓ "並么並") (ℓ "久")
  (rw 0 q88 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))

-- sw0 CS23: 2 steps
lem-sw0-CS23 : ⟪ (ℓ "並义並") ⟫ʷ ≈ ⟪ (ℓ "义") ⟫ʷ
lem-sw0-CS23 = derive (ℓ "並义並") (ℓ "义")
  (rw 0 q89 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))

-- sw0 CSd23: 2 steps
lem-sw0-CSd23 : ⟪ (ℓ "並乊並") ⟫ʷ ≈ ⟪ (ℓ "乊") ⟫ʷ
lem-sw0-CSd23 = derive (ℓ "並乊並") (ℓ "乊")
  (rw 0 q90 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))

-- sw0 CZ23: 2 steps
lem-sw0-CZ23 : ⟪ (ℓ "並之並") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
lem-sw0-CZ23 = derive (ℓ "並之並") (ℓ "之")
  (rw 0 q91 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))

-- sw0 CX23: 2 steps
lem-sw0-CX23 : ⟪ (ℓ "並乌並") ⟫ʷ ≈ ⟪ (ℓ "乌") ⟫ʷ
lem-sw0-CX23 = derive (ℓ "並乌並") (ℓ "乌")
  (rw 0 q92 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))

-- sw0 CK23: 2 steps
lem-sw0-CK23 : ⟪ (ℓ "並乍並") ⟫ʷ ≈ ⟪ (ℓ "乍") ⟫ʷ
lem-sw0-CK23 = derive (ℓ "並乍並") (ℓ "乍")
  (rw 0 q93 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))

-- sw0 CKd23: 2 steps
lem-sw0-CKd23 : ⟪ (ℓ "並乎並") ⟫ʷ ≈ ⟪ (ℓ "乎") ⟫ʷ
lem-sw0-CKd23 = derive (ℓ "並乎並") (ℓ "乎")
  (rw 0 q94 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX30: 6 steps
lem-sw0-CX30 : ⟪ (ℓ "並乐並") ⟫ʷ ≈ ⟪ (ℓ "乓") ⟫ʷ
lem-sw0-CX30 = derive (ℓ "並乐並") (ℓ "乓")
  (re 1 1 (ℓ "乏乃乏") ∷
   rw 0 q35 ∷
   rw 1 q83 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乓") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK30: 6 steps
lem-sw0-CK30 : ⟪ (ℓ "並乑並") ⟫ʷ ≈ ⟪ (ℓ "乔") ⟫ʷ
lem-sw0-CK30 = derive (ℓ "並乑並") (ℓ "乔")
  (re 1 1 (ℓ "乏乄乏") ∷
   rw 0 q35 ∷
   rw 1 q84 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乔") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd30: 6 steps
lem-sw0-CKd30 : ⟪ (ℓ "並乒並") ⟫ʷ ≈ ⟪ (ℓ "乕") ⟫ʷ
lem-sw0-CKd30 = derive (ℓ "並乒並") (ℓ "乕")
  (re 1 1 (ℓ "乏久乏") ∷
   rw 0 q35 ∷
   rw 1 q85 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乕") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX31: 6 steps
lem-sw0-CX31 : ⟪ (ℓ "並乓並") ⟫ʷ ≈ ⟪ (ℓ "乐") ⟫ʷ
lem-sw0-CX31 = derive (ℓ "並乓並") (ℓ "乐")
  (re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q35 ∷
   rw 1 q86 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乐") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK31: 6 steps
lem-sw0-CK31 : ⟪ (ℓ "並乔並") ⟫ʷ ≈ ⟪ (ℓ "乑") ⟫ʷ
lem-sw0-CK31 = derive (ℓ "並乔並") (ℓ "乑")
  (re 1 1 (ℓ "乏乇乏") ∷
   rw 0 q35 ∷
   rw 1 q87 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd31: 6 steps
lem-sw0-CKd31 : ⟪ (ℓ "並乕並") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
lem-sw0-CKd31 = derive (ℓ "並乕並") (ℓ "乒")
  (re 1 1 (ℓ "乏么乏") ∷
   rw 0 q35 ∷
   rw 1 q88 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "乒") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))

-- sw0 CX32: 2 steps
lem-sw0-CX32 : ⟪ (ℓ "並乖並") ⟫ʷ ≈ ⟪ (ℓ "乖") ⟫ʷ
lem-sw0-CX32 = derive (ℓ "並乖並") (ℓ "乖")
  (rw 0 q95 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))

-- sw0 CK32: 2 steps
lem-sw0-CK32 : ⟪ (ℓ "並乗並") ⟫ʷ ≈ ⟪ (ℓ "乗") ⟫ʷ
lem-sw0-CK32 = derive (ℓ "並乗並") (ℓ "乗")
  (rw 0 q96 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))

-- sw0 CKd32: 2 steps
lem-sw0-CKd32 : ⟪ (ℓ "並乘並") ⟫ʷ ≈ ⟪ (ℓ "乘") ⟫ʷ
lem-sw0-CKd32 = derive (ℓ "並乘並") (ℓ "乘")
  (rw 0 q97 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 11 W

-- sw0 CCZ012: 9 steps
lem-sw0-CCZ012 : ⟪ (ℓ "並乙並") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
lem-sw0-CCZ012 = derive (ℓ "並乙並") (ℓ "乙")
  (re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 0 q36 ∷
   rw 1 q66 ∷
   rw 2 q78 ∷
   rw 3 q66 ∷
   rw 4 q69 ∷
   rw 0 q98 ∷
   re 0 5 (ℓ "乙") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))

-- sw0 CCZ013: 41 steps
lem-sw0-CCZ013 : ⟪ (ℓ "並乚並") ⟫ʷ ≈ ⟪ (ℓ "乚") ⟫ʷ
lem-sw0-CCZ013 = derive (ℓ "並乚並") (ℓ "乚")
  (re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   rw 2 q35 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q66 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q35 ∷
   rw 3 q78 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q66 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q35 ∷
   rw 5 q69 ∷
   rw 6 q35 ∷
   re 4 3 (ℓ "丽") ∷
   rw 0 q1 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 1 q2 ∷
   rw⁻ 2 q99 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 3 q2 ∷
   rw⁻ 4 q99 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 1 q98 ∷
   re 1 5 (ℓ "乙") ∷
   re 0 3 (ℓ "乚") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 26 W

-- sw0 CCZ023: 24 steps
lem-sw0-CCZ023 : ⟪ (ℓ "並乛並") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
lem-sw0-CCZ023 = derive (ℓ "並乛並") (ℓ "乜")
  (re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q89 ∷
   rw 2 q80 ∷
   rw 3 q90 ∷
   rw 4 q80 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q35 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q37 ∷
   rw 0 q89 ∷
   rw 1 q72 ∷
   rw 2 q90 ∷
   rw 3 q72 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q35 ∷
   rw 5 q69 ∷
   rw 6 q35 ∷
   re 4 3 (ℓ "丽") ∷
   rw 0 q100 ∷
   re 0 5 (ℓ "乜") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 5 W

-- sw0 CCZ123: 24 steps
lem-sw0-CCZ123 : ⟪ (ℓ "並乜並") ⟫ʷ ≈ ⟪ (ℓ "乛") ⟫ʷ
lem-sw0-CCZ123 = derive (ℓ "並乜並") (ℓ "乛")
  (re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q89 ∷
   rw 1 q80 ∷
   rw 2 q90 ∷
   rw 3 q80 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   re 4 3 (ℓ "中") ∷
   rw 0 q101 ∷
   rw 1 q89 ∷
   rw 2 q72 ∷
   rw 3 q90 ∷
   rw 4 q72 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q35 ∷
   rw 6 q69 ∷
   rw 7 q35 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q100 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 124 W
  q103 : Eqn
  q103 = wE 274 W

-- sw0 TOFF012: 12 steps
lem-sw0-TOFF012 : ⟪ (ℓ "並九並") ⟫ʷ ≈ ⟪ (ℓ "习") ⟫ʷ
lem-sw0-TOFF012 = derive (ℓ "並九並") (ℓ "习")
  (re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 0 q41 ∷
   rw 1 q36 ∷
   rw 2 q66 ∷
   rw 3 q78 ∷
   rw 4 q66 ∷
   rw 5 q69 ∷
   rw 6 q41 ∷
   rw 7 q102 ∷
   rw 0 q103 ∷
   re 0 8 (ℓ "习") ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q105 : Eqn
  q105 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))

-- sw0 TOFF013: 50 steps
lem-sw0-TOFF013 : ⟪ (ℓ "並乞並") ⟫ʷ ≈ ⟪ (ℓ "乡") ⟫ʷ
lem-sw0-TOFF013 = derive (ℓ "並乞並") (ℓ "乡")
  (re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q104 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q104 ∷
   rw⁻ 8 q10 ∷
   rw 9 q2 ∷
   rw 0 q41 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q35 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q66 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q35 ∷
   rw 4 q78 ∷
   rw 5 q35 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q66 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q35 ∷
   rw 6 q69 ∷
   rw 7 q35 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q41 ∷
   rw 7 q102 ∷
   rw 0 q1 ∷
   rw⁻ 1 q8 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw⁻ 3 q99 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q2 ∷
   rw⁻ 5 q99 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q2 ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q105 ∷
   rw 1 q103 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q37 ∷ []) Eq.refl
