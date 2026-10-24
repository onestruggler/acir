{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD759 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D759 (W : Ws) (Sᴰ : SD759) where

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
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 12 W
  q2 : Eqn
  q2 = eqn (ℓ "丼丞") (ℓ "丞丼") (low₃-comm ((Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 47 W
  q4 : Eqn
  q4 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q5 : Eqn
  q5 = wE 398 W
  q6 : Eqn
  q6 = wE 14 W
  q7 : Eqn
  q7 = wE 15 W
  q8 : Eqn
  q8 = wE 16 W
  q9 : Eqn
  q9 = wE 366 W
  q10 : Eqn
  q10 = wE 48 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 9 W
  q15 : Eqn
  q15 = wE 127 W
  q16 : Eqn
  q16 = wE 271 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 8 W
  q19 : Eqn
  q19 = wE 10 W
  q20 : Eqn
  q20 = wE 272 W
  q21 : Eqn
  q21 = sE 2674 lem-merge3
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 28 W
  q24 : Eqn
  q24 = wE 29 W
  q25 : Eqn
  q25 = wE 25 W
  q26 : Eqn
  q26 = wE 11 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 18 W
  q29 : Eqn
  q29 = wE 19 W
  q30 : Eqn
  q30 = wE 17 W

-- merge3 @2013: 155 steps
lem-merge3-at2013 : ⟪ (ℓ "乣义乣乊丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丠乙") ⟫ʷ
lem-merge3-at2013 = derive (ℓ "乣义乣乊丞乣义乣乊丞") (ℓ "丠乙")
  (rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q6 ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q7 ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q8 ∷
   rw 7 q5 ∷
   rw 8 q9 ∷
   re 8 8 (ℓ "习") ∷
   rw 6 q10 ∷
   re 5 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q6 ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q7 ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q8 ∷
   rw 5 q5 ∷
   rw 6 q9 ∷
   re 6 8 (ℓ "习") ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q6 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q7 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q8 ∷
   rw 2 q5 ∷
   rw 3 q9 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q10 ∷
   re 0 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q6 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q7 ∷
   rw 2 q1 ∷
   re 3 3 (ℓ "个") ∷
   rw 1 q8 ∷
   rw 0 q5 ∷
   rw 1 q9 ∷
   re 1 8 (ℓ "习") ∷
   rw 11 q11 ∷
   rw⁻ 10 q12 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw⁻ 11 q13 ∷
   rw 10 q14 ∷
   rw⁻ 9 q13 ∷
   re 10 3 (ℓ "丮") ∷
   re 8 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 15 q15 ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q18 ∷
   rw 11 q14 ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   rw 8 q16 ∷
   rw 9 q20 ∷
   re 9 8 (ℓ "九") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q13 ∷
   rw 8 q19 ∷
   rw⁻ 7 q13 ∷
   re 8 3 (ℓ "中") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   rw 9 q14 ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw 6 q16 ∷
   rw 7 q20 ∷
   re 7 8 (ℓ "九") ∷
   rw⁻ 5 q12 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw⁻ 6 q13 ∷
   rw 5 q14 ∷
   rw⁻ 4 q13 ∷
   re 5 3 (ℓ "丮") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q15 ∷
   rw 9 q16 ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 6 q14 ∷
   rw 5 q18 ∷
   rw 4 q19 ∷
   rw 3 q16 ∷
   rw 4 q20 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q13 ∷
   rw 3 q19 ∷
   rw⁻ 2 q13 ∷
   re 3 3 (ℓ "中") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 8 q15 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   rw 5 q18 ∷
   rw 4 q14 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   rw 1 q16 ∷
   rw 2 q20 ∷
   re 2 8 (ℓ "九") ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q22 ∷
   rw 3 q23 ∷
   rw 4 q24 ∷
   rw 5 q23 ∷
   rw 6 q25 ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乙") ∷
   rw 3 q27 ∷
   re 1 1 (ℓ "丼丠丼") ∷
   rw 0 q6 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 1 q28 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q29 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q6 ∷
   rw 1 q30 ∷
   re 1 5 (ℓ "乙") ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1 W
  q32 : Eqn
  q32 = wE 1609 W
  q33 : Eqn
  q33 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = wE 56 W
  q38 : Eqn
  q38 = wE 43 W

-- merge3 @0132: 144 steps
lem-merge3-at0132 : ⟪ (ℓ "乞丧乞丨丘乞丧乞丨丘") ⟫ʷ ≈ ⟪ (ℓ "丽乚") ⟫ʷ
lem-merge3-at0132 = derive (ℓ "乞丧乞丨丘乞丧乞丨丘") (ℓ "丽乚")
  (rw 10 q31 ∷
   rw 9 q32 ∷
   rw 8 q31 ∷
   re 9 3 (ℓ "丮") ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q33 ∷
   rw 10 q31 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q34 ∷
   rw 12 q31 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q34 ∷
   rw 14 q31 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q33 ∷
   rw⁻ 14 q35 ∷
   rw 15 q36 ∷
   rw 14 q35 ∷
   rw 13 q33 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q36 ∷
   rw 11 q34 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q36 ∷
   rw 9 q34 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q36 ∷
   rw 7 q33 ∷
   rw 8 q37 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q31 ∷
   re 7 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q33 ∷
   rw 8 q31 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q34 ∷
   rw 10 q31 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q34 ∷
   rw 12 q31 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q33 ∷
   rw⁻ 12 q35 ∷
   rw 13 q36 ∷
   rw 12 q35 ∷
   rw 11 q33 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q36 ∷
   rw 9 q34 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q36 ∷
   rw 7 q34 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q36 ∷
   rw 5 q33 ∷
   rw 6 q37 ∷
   re 6 8 (ℓ "九") ∷
   rw 4 q32 ∷
   rw 3 q31 ∷
   re 4 3 (ℓ "丮") ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q33 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q34 ∷
   rw 7 q31 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q34 ∷
   rw 9 q31 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q33 ∷
   rw⁻ 9 q35 ∷
   rw 10 q36 ∷
   rw 9 q35 ∷
   rw 8 q33 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q36 ∷
   rw 6 q34 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q36 ∷
   rw 4 q34 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q36 ∷
   rw 2 q33 ∷
   rw 3 q37 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q31 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "乏九乏") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q33 ∷
   rw 3 q31 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q34 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q34 ∷
   rw 7 q31 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q33 ∷
   rw⁻ 7 q35 ∷
   rw 8 q36 ∷
   rw 7 q35 ∷
   rw 6 q33 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q36 ∷
   rw 4 q34 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q36 ∷
   rw 2 q34 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q36 ∷
   rw 0 q33 ∷
   rw 1 q37 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q21 ∷
   rw 2 q31 ∷
   re 0 3 (ℓ "丽") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q31 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q34 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q34 ∷
   rw 7 q31 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q31 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q36 ∷
   rw⁻ 3 q34 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q36 ∷
   rw⁻ 5 q34 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q36 ∷
   rw 2 q38 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q36 ∷ []) Eq.refl
