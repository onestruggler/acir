{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD678 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D678 (W : Ws) (Sᴰ : SD678) where

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
  lem-S2 : St 1778
  lem-S2 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 9 W
  q4 : Eqn
  q4 = wE 127 W
  q5 : Eqn
  q5 = wE 271 W
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = wE 8 W
  q8 : Eqn
  q8 = wE 10 W
  q9 : Eqn
  q9 = wE 272 W
  q10 : Eqn
  q10 = wE 12 W
  q11 : Eqn
  q11 = wE 22 W
  q12 : Eqn
  q12 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q13 : Eqn
  q13 = wE 23 W
  q14 : Eqn
  q14 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q16 : Eqn
  q16 = wE 14 W
  q17 : Eqn
  q17 = wE 15 W
  q18 : Eqn
  q18 = wE 16 W
  q19 : Eqn
  q19 = wE 46 W
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = sE 1778 lem-S2
  q22 : Eqn
  q22 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = wE 1 W
  q24 : Eqn
  q24 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q26 : Eqn
  q26 = wE 3 W
  q27 : Eqn
  q27 = wE 20 W
  q28 : Eqn
  q28 = wE 21 W
  q29 : Eqn
  q29 = wE 123 W
  q30 : Eqn
  q30 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q31 : Eqn
  q31 = wE 24 W
  q32 : Eqn
  q32 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W
  q35 : Eqn
  q35 = wE 125 W
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
  q41 = wE 219 W
  q42 : Eqn
  q42 = wE 319 W

-- S2 @1203: 227 steps
lem-S2-at1203 : ⟪ (ℓ "习丽习举") ⟫ʷ ≈ ⟪ (ℓ "乢丠乢両") ⟫ʷ
lem-S2-at1203 = derive (ℓ "习丽习举") (ℓ "乢丠乢両")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (ℓ "丮") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q7 ∷
   rw 5 q3 ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q5 ∷
   rw 3 q9 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q2 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 4 q7 ∷
   rw 3 q3 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 0 q5 ∷
   rw 1 q9 ∷
   re 1 8 (ℓ "九") ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏丼両丼乏") ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 4 q13 ∷
   re 5 5 (ℓ "丮") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q16 ∷
   rw 7 q10 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q17 ∷
   rw 5 q10 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q18 ∷
   rw 3 q15 ∷
   rw 4 q19 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q11 ∷
   rw 4 q20 ∷
   rw 2 q13 ∷
   re 3 5 (ℓ "中") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 8 q14 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q16 ∷
   rw 5 q10 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q17 ∷
   rw 3 q10 ∷
   re 4 3 (ℓ "个") ∷
   rw 2 q18 ∷
   rw 1 q15 ∷
   rw 2 q19 ∷
   re 2 8 (ℓ "九") ∷
   rw 2 q21 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q22 ∷
   rw 5 q23 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q24 ∷
   rw 7 q23 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q22 ∷
   rw⁻ 9 q25 ∷
   rw 10 q26 ∷
   rw⁻ 1 q15 ∷
   rw 2 q27 ∷
   rw 5 q10 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q28 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q11 ∷
   rw⁻ 8 q20 ∷
   rw 9 q13 ∷
   re 6 5 (ℓ "中") ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q14 ∷
   rw 1 q1 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw 8 q33 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q35 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   re 3 1 (ℓ "丼丠丼") ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q22 ∷
   rw 7 q23 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q23 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q22 ∷
   rw⁻ 11 q25 ∷
   rw 12 q26 ∷
   rw⁻ 3 q15 ∷
   rw 4 q27 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q28 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q11 ∷
   rw⁻ 10 q20 ∷
   rw 11 q13 ∷
   re 8 5 (ℓ "中") ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q14 ∷
   rw 3 q1 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q32 ∷
   rw 8 q31 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   rw 10 q33 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q35 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   re 5 1 (ℓ "丼両丼") ∷
   rw 4 q16 ∷
   rw 5 q16 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q36 ∷
   rw 2 q30 ∷
   rw 3 q37 ∷
   rw 4 q32 ∷
   rw 5 q37 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q2 ∷
   rw 7 q38 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 0 q29 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q32 ∷
   rw 4 q31 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   rw 6 q33 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q29 ∷
   rw 7 q34 ∷
   rw 0 q35 ∷
   re 0 8 (ℓ "乢") ∷
   rw 1 q41 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q37 ∷
   rw 6 q32 ∷
   rw 7 q37 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw 9 q38 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 11 q40 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw 8 q33 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q35 ∷
   re 2 8 (ℓ "乢") ∷
   rw 3 q42 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 47 W
  q44 : Eqn
  q44 = wE 398 W
  q45 : Eqn
  q45 = wE 366 W
  q46 : Eqn
  q46 = wE 48 W
  q47 : Eqn
  q47 = wE 28 W
  q48 : Eqn
  q48 = wE 29 W
  q49 : Eqn
  q49 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q50 : Eqn
  q50 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q51 : Eqn
  q51 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q52 : Eqn
  q52 = wE 274 W
  q53 : Eqn
  q53 = wE 322 W
  q54 : Eqn
  q54 = wE 340 W
  q55 : Eqn
  q55 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q56 : Eqn
  q56 = wE 334 W
  q57 : Eqn
  q57 = wE 18 W
  q58 : Eqn
  q58 = wE 19 W

-- S2 @2013: 257 steps
lem-S2-at2013 : ⟪ (ℓ "乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乤丶乤丷") ⟫ʷ
lem-S2-at2013 = derive (ℓ "乣义乣乊") (ℓ "乤丶乤丷")
  (rw 4 q10 ∷
   rw 3 q43 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 9 q14 ∷
   rw 8 q44 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q16 ∷
   rw 6 q10 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q17 ∷
   rw 4 q10 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q18 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q46 ∷
   re 0 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 7 q14 ∷
   rw 6 q44 ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q16 ∷
   rw 4 q10 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q17 ∷
   rw 2 q10 ∷
   re 3 3 (ℓ "个") ∷
   rw 1 q18 ∷
   rw 0 q44 ∷
   rw 1 q45 ∷
   re 1 8 (ℓ "习") ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw⁻ 6 q2 ∷
   rw 5 q3 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (ℓ "丮") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 3 q5 ∷
   rw 4 q9 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q2 ∷
   rw 3 q8 ∷
   rw⁻ 2 q2 ∷
   re 3 3 (ℓ "中") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q3 ∷
   rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q5 ∷
   rw 2 q9 ∷
   re 2 8 (ℓ "九") ∷
   rw 2 q21 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q22 ∷
   rw 5 q23 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q24 ∷
   rw 7 q23 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q22 ∷
   rw⁻ 9 q25 ∷
   rw 10 q26 ∷
   rw 1 q29 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw 3 q38 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q47 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q2 ∷
   rw 5 q48 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丮") ∷
   rw 5 q47 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q33 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q29 ∷
   rw 8 q34 ∷
   rw 1 q23 ∷
   rw⁻ 2 q49 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q26 ∷
   rw⁻ 4 q50 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q26 ∷
   rw⁻ 6 q50 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q26 ∷
   rw⁻ 8 q49 ∷
   rw⁻ 9 q51 ∷
   rw 2 q52 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q33 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q22 ∷
   rw 7 q23 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q24 ∷
   rw 11 q23 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q22 ∷
   rw⁻ 11 q25 ∷
   rw 12 q26 ∷
   rw 3 q29 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   rw 5 q38 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q47 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q2 ∷
   rw 7 q48 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q47 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw 9 q33 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q29 ∷
   rw 10 q34 ∷
   rw 3 q23 ∷
   rw⁻ 4 q49 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q26 ∷
   rw⁻ 6 q50 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 7 q26 ∷
   rw⁻ 8 q50 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q26 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 11 q51 ∷
   rw 4 q52 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 4 q53 ∷
   rw 5 q40 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q49 ∷
   rw 4 q23 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q24 ∷
   rw 6 q23 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q24 ∷
   rw 8 q23 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q49 ∷
   rw⁻ 8 q25 ∷
   rw 9 q26 ∷
   rw 0 q54 ∷
   rw 1 q27 ∷
   rw 4 q10 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q28 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q11 ∷
   rw⁻ 7 q20 ∷
   rw 8 q13 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q54 ∷
   rw⁻ 7 q14 ∷
   rw 0 q1 ∷
   rw 1 q55 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q31 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q33 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q55 ∷
   rw 8 q34 ∷
   rw 1 q56 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q57 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q49 ∷
   rw 6 q23 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 8 q23 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 10 q23 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q49 ∷
   rw⁻ 10 q25 ∷
   rw 11 q26 ∷
   rw 2 q54 ∷
   rw 3 q27 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q28 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q11 ∷
   rw⁻ 9 q20 ∷
   rw 10 q13 ∷
   re 7 5 (ℓ "中") ∷
   rw 8 q54 ∷
   rw⁻ 9 q14 ∷
   rw 2 q1 ∷
   rw 3 q55 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q31 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw 9 q33 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q55 ∷
   rw 10 q34 ∷
   rw 3 q56 ∷
   re 3 8 (ℓ "乥") ∷
   re 2 3 (ℓ "乤") ∷
   rw 3 q58 ∷
   rw 4 q16 ∷ []) Eq.refl
