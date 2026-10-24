{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD679 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D679 (W : Ws) (Sᴰ : SD679) where

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
  q2 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q3 : Eqn
  q3 = wE 127 W
  q4 : Eqn
  q4 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 8 W
  q7 : Eqn
  q7 = wE 9 W
  q8 : Eqn
  q8 = wE 10 W
  q9 : Eqn
  q9 = wE 333 W
  q10 : Eqn
  q10 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q11 : Eqn
  q11 = wE 12 W
  q12 : Eqn
  q12 = wE 47 W
  q13 : Eqn
  q13 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q14 : Eqn
  q14 = wE 398 W
  q15 : Eqn
  q15 = wE 14 W
  q16 : Eqn
  q16 = wE 15 W
  q17 : Eqn
  q17 = wE 16 W
  q18 : Eqn
  q18 = wE 366 W
  q19 : Eqn
  q19 = wE 48 W
  q20 : Eqn
  q20 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = wE 271 W
  q22 : Eqn
  q22 = wE 272 W
  q23 : Eqn
  q23 = sE 1778 lem-S2
  q24 : Eqn
  q24 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q25 : Eqn
  q25 = wE 1 W
  q26 : Eqn
  q26 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 3 W
  q29 : Eqn
  q29 = wE 123 W
  q30 : Eqn
  q30 = wE 27 W
  q31 : Eqn
  q31 = wE 28 W
  q32 : Eqn
  q32 = wE 29 W
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W
  q35 : Eqn
  q35 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q36 : Eqn
  q36 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q37 : Eqn
  q37 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))
  q38 : Eqn
  q38 = wE 274 W
  q39 : Eqn
  q39 = wE 322 W
  q40 : Eqn
  q40 = wE 31 W
  q41 : Eqn
  q41 = wE 340 W
  q42 : Eqn
  q42 = wE 20 W
  q43 : Eqn
  q43 = wE 21 W
  q44 : Eqn
  q44 = wE 22 W
  q45 : Eqn
  q45 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q46 : Eqn
  q46 = wE 23 W
  q47 : Eqn
  q47 = wE 24 W
  q48 : Eqn
  q48 = wE 334 W
  q49 : Eqn
  q49 = wE 18 W
  q50 : Eqn
  q50 = wE 19 W
  q51 : Eqn
  q51 = wE 30 W
  q52 : Eqn
  q52 = wE 122 W

-- S2 @2103: 343 steps
lem-S2-at2103 : ⟪ (ℓ "乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乥丧乥丨") ⟫ʷ
lem-S2-at2103 = derive (ℓ "乣义乣乊") (ℓ "乥丧乥丨")
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 9 q3 ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw⁻ 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (ℓ "乣") ∷
   rw⁻ 1 q10 ∷
   re 0 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 7 q3 ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q4 ∷
   rw 1 q9 ∷
   re 1 8 (ℓ "乣") ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q15 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q16 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   rw 4 q18 ∷
   re 4 8 (ℓ "习") ∷
   rw 2 q19 ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q15 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q16 ∷
   rw 3 q11 ∷
   re 4 3 (ℓ "个") ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   rw 2 q18 ∷
   re 2 8 (ℓ "习") ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw⁻ 7 q20 ∷
   rw 6 q7 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (ℓ "丮") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q3 ∷
   rw 10 q21 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q20 ∷
   rw 4 q8 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q3 ∷
   rw 8 q21 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   re 3 8 (ℓ "九") ∷
   rw 3 q23 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q25 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q25 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q27 ∷
   rw 11 q28 ∷
   rw 2 q29 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q20 ∷
   rw 4 q30 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q31 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q20 ∷
   rw 6 q32 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q25 ∷
   rw⁻ 3 q35 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q28 ∷
   rw⁻ 5 q36 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q28 ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q37 ∷
   rw 3 q38 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 3 q33 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q24 ∷
   rw 8 q25 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q26 ∷
   rw 12 q25 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q27 ∷
   rw 13 q28 ∷
   rw 4 q29 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q20 ∷
   rw 6 q30 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q20 ∷
   rw 8 q32 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q31 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q25 ∷
   rw⁻ 5 q35 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 8 q28 ∷
   rw⁻ 9 q36 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q28 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q37 ∷
   rw 5 q38 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q35 ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q43 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q44 ∷
   rw⁻ 8 q45 ∷
   rw 9 q46 ∷
   re 6 5 (ℓ "中") ∷
   rw 7 q41 ∷
   rw⁻ 8 q13 ∷
   rw 1 q1 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q49 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q35 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q26 ∷
   rw 11 q25 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q27 ∷
   rw 12 q28 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q43 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q44 ∷
   rw⁻ 10 q45 ∷
   rw 11 q46 ∷
   re 8 5 (ℓ "中") ∷
   rw 9 q41 ∷
   rw⁻ 10 q13 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q47 ∷
   rw 7 q2 ∷
   rw 8 q47 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q4 ∷
   rw 11 q34 ∷
   rw 4 q48 ∷
   re 4 8 (ℓ "乥") ∷
   re 3 3 (ℓ "乤") ∷
   rw 4 q50 ∷
   rw 5 q15 ∷
   re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q51 ∷
   rw 4 q2 ∷
   rw 5 q51 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q20 ∷
   rw 7 q30 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q4 ∷
   rw 8 q52 ∷
   rw 9 q40 ∷
   rw 0 q4 ∷
   rw 1 q10 ∷
   rw 2 q47 ∷
   rw 3 q2 ∷
   rw 4 q47 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q20 ∷
   rw 6 q33 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q4 ∷
   rw 7 q34 ∷
   rw 0 q48 ∷
   re 0 8 (ℓ "乥") ∷
   rw 1 q30 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   rw 5 q51 ∷
   rw 6 q2 ∷
   rw 7 q51 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q20 ∷
   rw 9 q30 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q4 ∷
   rw 10 q52 ∷
   rw 11 q40 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (ℓ "乥") ∷
   rw 3 q32 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 1882 W
  q54 : Eqn
  q54 = wE 335 W
  q55 : Eqn
  q55 = wE 1294 W
  q56 : Eqn
  q56 = wE 368 W
  q57 : Eqn
  q57 = wE 1883 W
  q58 : Eqn
  q58 = wE 71 W
  q59 : Eqn
  q59 = wE 72 W
  q60 : Eqn
  q60 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q61 : Eqn
  q61 = wE 385 W

-- S2 @3012: 411 steps
lem-S2-at3012 : ⟪ (ℓ "书义书乊") ⟫ʷ ≈ ⟪ (ℓ "乧丽乧举") ⟫ʷ
lem-S2-at3012 = derive (ℓ "书义书乊") (ℓ "乧丽乧举")
  (rw 4 q25 ∷
   rw 3 q53 ∷
   re 2 1 (ℓ "乏乣乏") ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 2 q54 ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q54 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 9 q27 ∷
   rw 8 q55 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q28 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q28 ∷
   rw 2 q55 ∷
   rw 3 q56 ∷
   re 3 8 (ℓ "乣") ∷
   rw 1 q57 ∷
   re 0 1 (ℓ "乏乣乏") ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q54 ∷
   rw 3 q25 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q54 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q55 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw 0 q55 ∷
   rw 1 q56 ∷
   re 1 8 (ℓ "乣") ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q15 ∷
   rw 7 q11 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q16 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   rw 4 q18 ∷
   re 4 8 (ℓ "习") ∷
   rw 2 q19 ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q15 ∷
   rw 5 q11 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q16 ∷
   rw 3 q11 ∷
   re 4 3 (ℓ "个") ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   rw 2 q18 ∷
   re 2 8 (ℓ "习") ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw⁻ 7 q20 ∷
   rw 6 q7 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (ℓ "丮") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q3 ∷
   rw 10 q21 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q20 ∷
   rw 4 q8 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q3 ∷
   rw 8 q21 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   re 3 8 (ℓ "九") ∷
   rw 3 q23 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q25 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q25 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q27 ∷
   rw 11 q28 ∷
   rw 2 q29 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q20 ∷
   rw 4 q30 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q31 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q20 ∷
   rw 6 q32 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q25 ∷
   rw⁻ 3 q35 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q28 ∷
   rw⁻ 5 q36 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q28 ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q37 ∷
   rw 3 q38 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 3 q33 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q24 ∷
   rw 8 q25 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q26 ∷
   rw 12 q25 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q27 ∷
   rw 13 q28 ∷
   rw 4 q29 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q20 ∷
   rw 6 q30 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q31 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q20 ∷
   rw 8 q32 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q31 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q25 ∷
   rw⁻ 5 q35 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 8 q28 ∷
   rw⁻ 9 q36 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q28 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q37 ∷
   rw 5 q38 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q35 ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q43 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q44 ∷
   rw⁻ 8 q45 ∷
   rw 9 q46 ∷
   re 6 5 (ℓ "中") ∷
   rw 7 q41 ∷
   rw⁻ 8 q13 ∷
   rw 1 q1 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q49 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q35 ∷
   rw 7 q25 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q26 ∷
   rw 11 q25 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q27 ∷
   rw 12 q28 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q43 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q44 ∷
   rw⁻ 10 q45 ∷
   rw 11 q46 ∷
   re 8 5 (ℓ "中") ∷
   rw 9 q41 ∷
   rw⁻ 10 q13 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q47 ∷
   rw 7 q2 ∷
   rw 8 q47 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q4 ∷
   rw 11 q34 ∷
   rw 4 q48 ∷
   re 4 8 (ℓ "乥") ∷
   re 3 3 (ℓ "乤") ∷
   rw 4 q50 ∷
   rw 5 q15 ∷
   re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q51 ∷
   rw 4 q2 ∷
   rw 5 q51 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q20 ∷
   rw 7 q30 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q4 ∷
   rw 8 q52 ∷
   rw 9 q40 ∷
   rw 0 q54 ∷
   rw 1 q58 ∷
   rw 4 q25 ∷
   re 2 3 (ℓ "丰") ∷
   rw 3 q59 ∷
   rw 6 q25 ∷
   re 4 3 (ℓ "丰") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q28 ∷
   rw 6 q54 ∷
   rw⁻ 7 q27 ∷
   rw 0 q1 ∷
   rw 1 q60 ∷
   rw 2 q10 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw 3 q20 ∷
   rw 4 q47 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "乀") ∷
   rw 4 q2 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q20 ∷
   rw 6 q47 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q33 ∷
   rw 7 q60 ∷
   rw 8 q34 ∷
   rw 1 q61 ∷
   re 1 8 (ℓ "乨") ∷
   re 0 3 (ℓ "乧") ∷
   rw 3 q25 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   rw 5 q51 ∷
   rw 6 q2 ∷
   rw 7 q51 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q20 ∷
   rw 9 q30 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q4 ∷
   rw 10 q52 ∷
   rw 11 q40 ∷
   rw 2 q54 ∷
   rw 3 q58 ∷
   rw 6 q25 ∷
   re 4 3 (ℓ "丰") ∷
   rw 5 q59 ∷
   rw 8 q25 ∷
   re 6 3 (ℓ "丰") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw 8 q54 ∷
   rw⁻ 9 q27 ∷
   rw 2 q1 ∷
   rw 3 q60 ∷
   rw 4 q10 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q20 ∷
   rw 6 q47 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q2 ∷
   re 8 1 (ℓ "乏个乏") ∷
   rw 7 q20 ∷
   rw 8 q47 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "乀") ∷
   rw 8 q33 ∷
   rw 9 q60 ∷
   rw 10 q34 ∷
   rw 3 q61 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "举") ∷
   rw 4 q28 ∷ []) Eq.refl
