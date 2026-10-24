{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D017 (W : Ws) where

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
  q1 = wE 121 W
  q2 : Eqn
  q2 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = wE 30 W
  q4 : Eqn
  q4 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 122 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 123 W
  q10 : Eqn
  q10 = wE 24 W
  q11 : Eqn
  q11 = wE 25 W
  q12 : Eqn
  q12 = wE 124 W
  q13 : Eqn
  q13 = wE 125 W

-- sw0 TOFF023: 30 steps
lem-sw0-TOFF023 : ⟪ (ℓ "並也並") ⟫ʷ ≈ ⟪ (ℓ "乢") ⟫ʷ
lem-sw0-TOFF023 = derive (ℓ "並也並") (ℓ "乢")
  (re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q1 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q9 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q9 ∷
   rw 7 q12 ∷
   rw 0 q13 ∷
   re 0 8 (ℓ "乢") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 28 W
  q15 : Eqn
  q15 = wE 29 W
  q16 : Eqn
  q16 = wE 272 W

-- sw0 TOFF102: 12 steps
lem-sw0-TOFF102 : ⟪ (ℓ "並习並") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
lem-sw0-TOFF102 = derive (ℓ "並习並") (ℓ "九")
  (re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 0 q1 ∷
   rw 1 q6 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   rw 5 q11 ∷
   rw 6 q1 ∷
   rw 7 q12 ∷
   rw 0 q16 ∷
   re 0 8 (ℓ "九") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q24 : Eqn
  q24 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))

-- sw0 TOFF103: 50 steps
lem-sw0-TOFF103 : ⟪ (ℓ "並乡並") ⟫ʷ ≈ ⟪ (ℓ "乞") ⟫ʷ
lem-sw0-TOFF103 = derive (ℓ "並乡並") (ℓ "乞")
  (re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q17 ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q17 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw 0 q1 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw 4 q15 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q1 ∷
   rw 7 q12 ∷
   rw 0 q18 ∷
   rw⁻ 1 q22 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q21 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q21 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q24 ∷
   rw 1 q16 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 5 W

-- sw0 TOFF123: 30 steps
lem-sw0-TOFF123 : ⟪ (ℓ "並乢並") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
lem-sw0-TOFF123 = derive (ℓ "並乢並") (ℓ "也")
  (re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q1 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   rw 1 q13 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q27 : Eqn
  q27 = wE 333 W

-- sw0 TOFF201: 12 steps
lem-sw0-TOFF201 : ⟪ (ℓ "並乣並") ⟫ʷ ≈ ⟪ (ℓ "乣") ⟫ʷ
lem-sw0-TOFF201 = derive (ℓ "並乣並") (ℓ "乣")
  (re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q26 ∷
   rw 1 q6 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q14 ∷
   rw 5 q11 ∷
   rw 6 q26 ∷
   rw 7 q12 ∷
   rw 0 q27 ∷
   re 0 8 (ℓ "乣") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 334 W

-- sw0 TOFF203: 30 steps
lem-sw0-TOFF203 : ⟪ (ℓ "並乤並") ⟫ʷ ≈ ⟪ (ℓ "乥") ⟫ʷ
lem-sw0-TOFF203 = derive (ℓ "並乤並") (ℓ "乥")
  (re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q26 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q26 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q26 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q26 ∷
   rw 7 q12 ∷
   rw 0 q28 ∷
   re 0 8 (ℓ "乥") ∷
   rw 1 q8 ∷ []) Eq.refl

-- sw0 TOFF213: 30 steps
lem-sw0-TOFF213 : ⟪ (ℓ "並乥並") ⟫ʷ ≈ ⟪ (ℓ "乤") ⟫ʷ
lem-sw0-TOFF213 = derive (ℓ "並乥並") (ℓ "乤")
  (re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q26 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q26 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q26 ∷
   rw 8 q12 ∷
   rw 1 q28 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 335 W
  q30 : Eqn
  q30 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q31 : Eqn
  q31 = wE 336 W

-- sw0 TOFF301: 50 steps
lem-sw0-TOFF301 : ⟪ (ℓ "並书並") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
lem-sw0-TOFF301 = derive (ℓ "並书並") (ℓ "书")
  (re 1 1 (ℓ "乏乣乏") ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q29 ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q29 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw 0 q30 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw 4 q15 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q30 ∷
   rw 7 q12 ∷
   rw 0 q18 ∷
   rw 1 q31 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q21 ∷
   rw⁻ 3 q23 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q21 ∷
   rw⁻ 5 q23 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 7 q31 ∷
   rw⁻ 8 q24 ∷
   rw 1 q27 ∷
   re 1 8 (ℓ "乣") ∷
   re 0 3 (ℓ "书") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 337 W

-- sw0 TOFF302: 30 steps
lem-sw0-TOFF302 : ⟪ (ℓ "並乧並") ⟫ʷ ≈ ⟪ (ℓ "乨") ⟫ʷ
lem-sw0-TOFF302 = derive (ℓ "並乧並") (ℓ "乨")
  (re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q30 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q30 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 0 q30 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q30 ∷
   rw 7 q12 ∷
   rw 0 q32 ∷
   re 0 8 (ℓ "乨") ∷
   rw 1 q8 ∷ []) Eq.refl

-- sw0 TOFF312: 30 steps
lem-sw0-TOFF312 : ⟪ (ℓ "並乨並") ⟫ʷ ≈ ⟪ (ℓ "乧") ⟫ʷ
lem-sw0-TOFF312 = derive (ℓ "並乨並") (ℓ "乧")
  (re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q30 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q30 ∷
   rw 7 q7 ∷
   rw 0 q25 ∷
   rw 1 q30 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q30 ∷
   rw 8 q12 ∷
   rw 1 q32 ∷
   re 1 8 (ℓ "乨") ∷
   re 0 3 (ℓ "乧") ∷
   rw 1 q8 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (ℓ "丈丼") (ℓ "丼丈") (low₁-comm (S) (Swap))
  q34 : Eqn
  q34 = wE 14 W

-- sw1 S0: 2 steps
lem-sw1-S0 : ⟪ (ℓ "丼丈丼") ⟫ʷ ≈ ⟪ (ℓ "丈") ⟫ʷ
lem-sw1-S0 = derive (ℓ "丼丈丼") (ℓ "丈")
  (rw⁻ 0 q33 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (ℓ "三丼") (ℓ "丼三") (low₁-comm ((S • S • S)) (Swap))

-- sw1 Sd0: 2 steps
lem-sw1-Sd0 : ⟪ (ℓ "丼三丼") ⟫ʷ ≈ ⟪ (ℓ "三") ⟫ʷ
lem-sw1-Sd0 = derive (ℓ "丼三丼") (ℓ "三")
  (rw⁻ 0 q35 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))

-- sw1 K0: 2 steps
lem-sw1-K0 : ⟪ (ℓ "丼上丼") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
lem-sw1-K0 = derive (ℓ "丼上丼") (ℓ "上")
  (rw⁻ 0 q36 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (ℓ "下丼") (ℓ "丼下") (low₁-comm ((K • iI)) (Swap))

-- sw1 Kd0: 2 steps
lem-sw1-Kd0 : ⟪ (ℓ "丼下丼") ⟫ʷ ≈ ⟪ (ℓ "下") ⟫ʷ
lem-sw1-Kd0 = derive (ℓ "丼下丼") (ℓ "下")
  (rw⁻ 0 q37 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (ℓ "丌丼") (ℓ "丼丌") (low₁-comm (X) (Swap))

-- sw1 X0: 2 steps
lem-sw1-X0 : ⟪ (ℓ "丼丌丼") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-sw1-X0 = derive (ℓ "丼丌丼") (ℓ "丌")
  (rw⁻ 0 q38 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (ℓ "不丼") (ℓ "丼不") (low₁-comm (Z) (Swap))

-- sw1 Z0: 2 steps
lem-sw1-Z0 : ⟪ (ℓ "丼不丼") ⟫ʷ ≈ ⟪ (ℓ "不") ⟫ʷ
lem-sw1-Z0 = derive (ℓ "丼不丼") (ℓ "不")
  (rw⁻ 0 q39 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 338 W

-- sw1 S1: 2 steps
lem-sw1-S1 : ⟪ (ℓ "丼与丼") ⟫ʷ ≈ ⟪ (ℓ "且") ⟫ʷ
lem-sw1-S1 = derive (ℓ "丼与丼") (ℓ "且")
  (rw 0 q40 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 339 W

-- sw1 Sd1: 2 steps
lem-sw1-Sd1 : ⟪ (ℓ "丼丏丼") ⟫ʷ ≈ ⟪ (ℓ "丕") ⟫ʷ
lem-sw1-Sd1 = derive (ℓ "丼丏丼") (ℓ "丕")
  (rw 0 q41 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 340 W

-- sw1 K1: 2 steps
lem-sw1-K1 : ⟪ (ℓ "丼丐丼") ⟫ʷ ≈ ⟪ (ℓ "世") ⟫ʷ
lem-sw1-K1 = derive (ℓ "丼丐丼") (ℓ "世")
  (rw 0 q42 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 341 W

-- sw1 Kd1: 2 steps
lem-sw1-Kd1 : ⟪ (ℓ "丼丑丼") ⟫ʷ ≈ ⟪ (ℓ "丗") ⟫ʷ
lem-sw1-Kd1 = derive (ℓ "丼丑丼") (ℓ "丗")
  (rw 0 q43 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 222 W

-- sw1 X1: 2 steps
lem-sw1-X1 : ⟪ (ℓ "丼丒丼") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-sw1-X1 = derive (ℓ "丼丒丼") (ℓ "丘")
  (rw 0 q44 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 342 W

-- sw1 Z1: 2 steps
lem-sw1-Z1 : ⟪ (ℓ "丼专丼") ⟫ʷ ≈ ⟪ (ℓ "丙") ⟫ʷ
lem-sw1-Z1 = derive (ℓ "丼专丼") (ℓ "丙")
  (rw 0 q45 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 343 W

-- sw1 S2: 2 steps
lem-sw1-S2 : ⟪ (ℓ "丼且丼") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
lem-sw1-S2 = derive (ℓ "丼且丼") (ℓ "与")
  (rw 0 q46 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 344 W

-- sw1 Sd2: 2 steps
lem-sw1-Sd2 : ⟪ (ℓ "丼丕丼") ⟫ʷ ≈ ⟪ (ℓ "丏") ⟫ʷ
lem-sw1-Sd2 = derive (ℓ "丼丕丼") (ℓ "丏")
  (rw 0 q47 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 345 W

-- sw1 K2: 2 steps
lem-sw1-K2 : ⟪ (ℓ "丼世丼") ⟫ʷ ≈ ⟪ (ℓ "丐") ⟫ʷ
lem-sw1-K2 = derive (ℓ "丼世丼") (ℓ "丐")
  (rw 0 q48 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 346 W

-- sw1 Kd2: 2 steps
lem-sw1-Kd2 : ⟪ (ℓ "丼丗丼") ⟫ʷ ≈ ⟪ (ℓ "丑") ⟫ʷ
lem-sw1-Kd2 = derive (ℓ "丼丗丼") (ℓ "丑")
  (rw 0 q49 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 347 W

-- sw1 X2: 2 steps
lem-sw1-X2 : ⟪ (ℓ "丼丘丼") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-sw1-X2 = derive (ℓ "丼丘丼") (ℓ "丒")
  (rw 0 q50 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 348 W

-- sw1 Z2: 2 steps
lem-sw1-Z2 : ⟪ (ℓ "丼丙丼") ⟫ʷ ≈ ⟪ (ℓ "专") ⟫ʷ
lem-sw1-Z2 = derive (ℓ "丼丙丼") (ℓ "专")
  (rw 0 q51 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))

-- sw1 S3: 2 steps
lem-sw1-S3 : ⟪ (ℓ "丼业丼") ⟫ʷ ≈ ⟪ (ℓ "业") ⟫ʷ
lem-sw1-S3 = derive (ℓ "丼业丼") (ℓ "业")
  (rw 0 q52 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (ℓ "丼丛") (ℓ "丛丼") (low₃-comm ((Swap ↑)) ((S • S • S)))

-- sw1 Sd3: 2 steps
lem-sw1-Sd3 : ⟪ (ℓ "丼丛丼") ⟫ʷ ≈ ⟪ (ℓ "丛") ⟫ʷ
lem-sw1-Sd3 = derive (ℓ "丼丛丼") (ℓ "丛")
  (rw 0 q53 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))

-- sw1 K3: 2 steps
lem-sw1-K3 : ⟪ (ℓ "丼东丼") ⟫ʷ ≈ ⟪ (ℓ "东") ⟫ʷ
lem-sw1-K3 = derive (ℓ "丼东丼") (ℓ "东")
  (rw 0 q54 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (ℓ "丼丝") (ℓ "丝丼") (low₃-comm ((Swap ↑)) ((K • iI)))

-- sw1 Kd3: 2 steps
lem-sw1-Kd3 : ⟪ (ℓ "丼丝丼") ⟫ʷ ≈ ⟪ (ℓ "丝") ⟫ʷ
lem-sw1-Kd3 = derive (ℓ "丼丝丼") (ℓ "丝")
  (rw 0 q55 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (ℓ "丼丞") (ℓ "丞丼") (low₃-comm ((Swap ↑)) (X))

-- sw1 X3: 2 steps
lem-sw1-X3 : ⟪ (ℓ "丼丞丼") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-sw1-X3 = derive (ℓ "丼丞丼") (ℓ "丞")
  (rw 0 q56 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (ℓ "丼丟") (ℓ "丟丼") (low₃-comm ((Swap ↑)) (Z))

-- sw1 Z3: 2 steps
lem-sw1-Z3 : ⟪ (ℓ "丼丟丼") ⟫ʷ ≈ ⟪ (ℓ "丟") ⟫ʷ
lem-sw1-Z3 = derive (ℓ "丼丟丼") (ℓ "丟")
  (rw 0 q57 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 12 W

-- sw1 CS01: 3 steps
lem-sw1-CS01 : ⟪ (ℓ "丼丠丼") ⟫ʷ ≈ ⟪ (ℓ "丧") ⟫ʷ
lem-sw1-CS01 = derive (ℓ "丼丠丼") (ℓ "丧")
  (rw 2 q58 ∷
   re 0 3 (ℓ "丧") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CSd01: 3 steps
lem-sw1-CSd01 : ⟪ (ℓ "丼両丼") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
lem-sw1-CSd01 = derive (ℓ "丼両丼") (ℓ "丨")
  (rw 2 q58 ∷
   re 0 3 (ℓ "丨") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CZ01: 3 steps
lem-sw1-CZ01 : ⟪ (ℓ "丼丢丼") ⟫ʷ ≈ ⟪ (ℓ "丩") ⟫ʷ
lem-sw1-CZ01 = derive (ℓ "丼丢丼") (ℓ "丩")
  (rw 2 q58 ∷
   re 0 3 (ℓ "丩") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX01: 3 steps
lem-sw1-CX01 : ⟪ (ℓ "丼丣丼") ⟫ʷ ≈ ⟪ (ℓ "个") ⟫ʷ
lem-sw1-CX01 = derive (ℓ "丼丣丼") (ℓ "个")
  (rw 2 q58 ∷
   re 0 3 (ℓ "个") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK01: 3 steps
lem-sw1-CK01 : ⟪ (ℓ "丼两丼") ⟫ʷ ≈ ⟪ (ℓ "丫") ⟫ʷ
lem-sw1-CK01 = derive (ℓ "丼两丼") (ℓ "丫")
  (rw 2 q58 ∷
   re 0 3 (ℓ "丫") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd01: 3 steps
lem-sw1-CKd01 : ⟪ (ℓ "丼严丼") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
lem-sw1-CKd01 = derive (ℓ "丼严丼") (ℓ "丬")
  (rw 2 q58 ∷
   re 0 3 (ℓ "丬") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CS02: 3 steps
lem-sw1-CS02 : ⟪ (ℓ "丼丧丼") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
lem-sw1-CS02 = derive (ℓ "丼丧丼") (ℓ "丠")
  (re 1 1 (ℓ "丼丠丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CSd02: 3 steps
lem-sw1-CSd02 : ⟪ (ℓ "丼丨丼") ⟫ʷ ≈ ⟪ (ℓ "両") ⟫ʷ
lem-sw1-CSd02 = derive (ℓ "丼丨丼") (ℓ "両")
  (re 1 1 (ℓ "丼両丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CZ02: 3 steps
lem-sw1-CZ02 : ⟪ (ℓ "丼丩丼") ⟫ʷ ≈ ⟪ (ℓ "丢") ⟫ʷ
lem-sw1-CZ02 = derive (ℓ "丼丩丼") (ℓ "丢")
  (re 1 1 (ℓ "丼丢丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX02: 3 steps
lem-sw1-CX02 : ⟪ (ℓ "丼个丼") ⟫ʷ ≈ ⟪ (ℓ "丣") ⟫ʷ
lem-sw1-CX02 = derive (ℓ "丼个丼") (ℓ "丣")
  (re 1 1 (ℓ "丼丣丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK02: 3 steps
lem-sw1-CK02 : ⟪ (ℓ "丼丫丼") ⟫ʷ ≈ ⟪ (ℓ "两") ⟫ʷ
lem-sw1-CK02 = derive (ℓ "丼丫丼") (ℓ "两")
  (re 1 1 (ℓ "丼两丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd02: 3 steps
lem-sw1-CKd02 : ⟪ (ℓ "丼丬丼") ⟫ʷ ≈ ⟪ (ℓ "严") ⟫ʷ
lem-sw1-CKd02 = derive (ℓ "丼丬丼") (ℓ "严")
  (re 1 1 (ℓ "丼严丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 22 W
  q60 : Eqn
  q60 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q61 : Eqn
  q61 = wE 23 W

-- sw1 CS03: 6 steps
lem-sw1-CS03 : ⟪ (ℓ "丼中丼") ⟫ʷ ≈ ⟪ (ℓ "中") ⟫ʷ
lem-sw1-CS03 = derive (ℓ "丼中丼") (ℓ "中")
  (re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q60 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "中") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))

-- sw1 CSd03: 6 steps
lem-sw1-CSd03 : ⟪ (ℓ "丼丮丼") ⟫ʷ ≈ ⟪ (ℓ "丮") ⟫ʷ
lem-sw1-CSd03 = derive (ℓ "丼丮丼") (ℓ "丮")
  (re 1 1 (ℓ "乏丼両丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q62 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "丮") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (ℓ "丢乏") (ℓ "乏丢") (low-comm (CZ) (Swap))

-- sw1 CZ03: 6 steps
lem-sw1-CZ03 : ⟪ (ℓ "丼丯丼") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
lem-sw1-CZ03 = derive (ℓ "丼丯丼") (ℓ "丯")
  (re 1 1 (ℓ "乏丼丢丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q63 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "丯") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX03: 6 steps
lem-sw1-CX03 : ⟪ (ℓ "丼丰丼") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
lem-sw1-CX03 = derive (ℓ "丼丰丼") (ℓ "丰")
  (re 1 1 (ℓ "乏丼丣丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q19 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "丰") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))

-- sw1 CK03: 6 steps
lem-sw1-CK03 : ⟪ (ℓ "丼丱丼") ⟫ʷ ≈ ⟪ (ℓ "丱") ⟫ʷ
lem-sw1-CK03 = derive (ℓ "丼丱丼") (ℓ "丱")
  (re 1 1 (ℓ "乏丼两丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q64 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "丱") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (ℓ "严乏") (ℓ "乏严") (low-comm ((S • CK₀₁)) (Swap))

-- sw1 CKd03: 6 steps
lem-sw1-CKd03 : ⟪ (ℓ "丼串丼") ⟫ʷ ≈ ⟪ (ℓ "串") ⟫ʷ
lem-sw1-CKd03 = derive (ℓ "丼串丼") (ℓ "串")
  (re 1 1 (ℓ "乏丼严丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q65 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "串") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX10: 3 steps
lem-sw1-CX10 : ⟪ (ℓ "丼丳丼") ⟫ʷ ≈ ⟪ (ℓ "乃") ⟫ʷ
lem-sw1-CX10 = derive (ℓ "丼丳丼") (ℓ "乃")
  (rw 2 q58 ∷
   re 0 3 (ℓ "乃") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK10: 3 steps
lem-sw1-CK10 : ⟪ (ℓ "丼临丼") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
lem-sw1-CK10 = derive (ℓ "丼临丼") (ℓ "乄")
  (rw 2 q58 ∷
   re 0 3 (ℓ "乄") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd10: 3 steps
lem-sw1-CKd10 : ⟪ (ℓ "丼丵丼") ⟫ʷ ≈ ⟪ (ℓ "久") ⟫ʷ
lem-sw1-CKd10 = derive (ℓ "丼丵丼") (ℓ "久")
  (rw 2 q58 ∷
   re 0 3 (ℓ "久") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 18 W

-- sw1 CS12: 2 steps
lem-sw1-CS12 : ⟪ (ℓ "丼丶丼") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
lem-sw1-CS12 = derive (ℓ "丼丶丼") (ℓ "丶")
  (rw 0 q66 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 19 W

-- sw1 CSd12: 2 steps
lem-sw1-CSd12 : ⟪ (ℓ "丼丷丼") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
lem-sw1-CSd12 = derive (ℓ "丼丷丼") (ℓ "丷")
  (rw 0 q67 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 349 W

-- sw1 CZ12: 2 steps
lem-sw1-CZ12 : ⟪ (ℓ "丼丸丼") ⟫ʷ ≈ ⟪ (ℓ "丸") ⟫ʷ
lem-sw1-CZ12 = derive (ℓ "丼丸丼") (ℓ "丸")
  (rw 0 q68 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 50 W

-- sw1 CX12: 2 steps
lem-sw1-CX12 : ⟪ (ℓ "丼丹丼") ⟫ʷ ≈ ⟪ (ℓ "乆") ⟫ʷ
lem-sw1-CX12 = derive (ℓ "丼丹丼") (ℓ "乆")
  (rw 0 q69 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 350 W

-- sw1 CK12: 2 steps
lem-sw1-CK12 : ⟪ (ℓ "丼为丼") ⟫ʷ ≈ ⟪ (ℓ "乇") ⟫ʷ
lem-sw1-CK12 = derive (ℓ "丼为丼") (ℓ "乇")
  (rw 0 q70 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 351 W

-- sw1 CKd12: 2 steps
lem-sw1-CKd12 : ⟪ (ℓ "丼主丼") ⟫ʷ ≈ ⟪ (ℓ "么") ⟫ʷ
lem-sw1-CKd12 = derive (ℓ "丼主丼") (ℓ "么")
  (rw 0 q71 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 20 W

-- sw1 CS13: 2 steps
lem-sw1-CS13 : ⟪ (ℓ "丼丽丼") ⟫ʷ ≈ ⟪ (ℓ "义") ⟫ʷ
lem-sw1-CS13 = derive (ℓ "丼丽丼") (ℓ "义")
  (rw 0 q72 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 21 W

-- sw1 CSd13: 2 steps
lem-sw1-CSd13 : ⟪ (ℓ "丼举丼") ⟫ʷ ≈ ⟪ (ℓ "乊") ⟫ʷ
lem-sw1-CSd13 = derive (ℓ "丼举丼") (ℓ "乊")
  (rw 0 q73 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 107 W

-- sw1 CZ13: 2 steps
lem-sw1-CZ13 : ⟪ (ℓ "丼丿丼") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
lem-sw1-CZ13 = derive (ℓ "丼丿丼") (ℓ "之")
  (rw 0 q74 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 157 W

-- sw1 CX13: 2 steps
lem-sw1-CX13 : ⟪ (ℓ "丼乀丼") ⟫ʷ ≈ ⟪ (ℓ "乌") ⟫ʷ
lem-sw1-CX13 = derive (ℓ "丼乀丼") (ℓ "乌")
  (rw 0 q75 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 352 W

-- sw1 CK13: 2 steps
lem-sw1-CK13 : ⟪ (ℓ "丼乁丼") ⟫ʷ ≈ ⟪ (ℓ "乍") ⟫ʷ
lem-sw1-CK13 = derive (ℓ "丼乁丼") (ℓ "乍")
  (rw 0 q76 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 353 W

-- sw1 CKd13: 2 steps
lem-sw1-CKd13 : ⟪ (ℓ "丼乂丼") ⟫ʷ ≈ ⟪ (ℓ "乎") ⟫ʷ
lem-sw1-CKd13 = derive (ℓ "丼乂丼") (ℓ "乎")
  (rw 0 q77 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX20: 3 steps
lem-sw1-CX20 : ⟪ (ℓ "丼乃丼") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
lem-sw1-CX20 = derive (ℓ "丼乃丼") (ℓ "丳")
  (re 1 1 (ℓ "丼丳丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CK20: 3 steps
lem-sw1-CK20 : ⟪ (ℓ "丼乄丼") ⟫ʷ ≈ ⟪ (ℓ "临") ⟫ʷ
lem-sw1-CK20 = derive (ℓ "丼乄丼") (ℓ "临")
  (re 1 1 (ℓ "丼临丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CKd20: 3 steps
lem-sw1-CKd20 : ⟪ (ℓ "丼久丼") ⟫ʷ ≈ ⟪ (ℓ "丵") ⟫ʷ
lem-sw1-CKd20 = derive (ℓ "丼久丼") (ℓ "丵")
  (re 1 1 (ℓ "丼丵丼") ∷
   rw 0 q34 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 354 W

-- sw1 CX21: 2 steps
lem-sw1-CX21 : ⟪ (ℓ "丼乆丼") ⟫ʷ ≈ ⟪ (ℓ "丹") ⟫ʷ
lem-sw1-CX21 = derive (ℓ "丼乆丼") (ℓ "丹")
  (rw 0 q78 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 355 W

-- sw1 CK21: 2 steps
lem-sw1-CK21 : ⟪ (ℓ "丼乇丼") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
lem-sw1-CK21 = derive (ℓ "丼乇丼") (ℓ "为")
  (rw 0 q79 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 356 W

-- sw1 CKd21: 2 steps
lem-sw1-CKd21 : ⟪ (ℓ "丼么丼") ⟫ʷ ≈ ⟪ (ℓ "主") ⟫ʷ
lem-sw1-CKd21 = derive (ℓ "丼么丼") (ℓ "主")
  (rw 0 q80 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 49 W

-- sw1 CS23: 2 steps
lem-sw1-CS23 : ⟪ (ℓ "丼义丼") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
lem-sw1-CS23 = derive (ℓ "丼义丼") (ℓ "丽")
  (rw 0 q81 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 51 W

-- sw1 CSd23: 2 steps
lem-sw1-CSd23 : ⟪ (ℓ "丼乊丼") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
lem-sw1-CSd23 = derive (ℓ "丼乊丼") (ℓ "举")
  (rw 0 q82 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 108 W

-- sw1 CZ23: 2 steps
lem-sw1-CZ23 : ⟪ (ℓ "丼之丼") ⟫ʷ ≈ ⟪ (ℓ "丿") ⟫ʷ
lem-sw1-CZ23 = derive (ℓ "丼之丼") (ℓ "丿")
  (rw 0 q83 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 158 W

-- sw1 CX23: 2 steps
lem-sw1-CX23 : ⟪ (ℓ "丼乌丼") ⟫ʷ ≈ ⟪ (ℓ "乀") ⟫ʷ
lem-sw1-CX23 = derive (ℓ "丼乌丼") (ℓ "乀")
  (rw 0 q84 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 357 W

-- sw1 CK23: 2 steps
lem-sw1-CK23 : ⟪ (ℓ "丼乍丼") ⟫ʷ ≈ ⟪ (ℓ "乁") ⟫ʷ
lem-sw1-CK23 = derive (ℓ "丼乍丼") (ℓ "乁")
  (rw 0 q85 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 358 W

-- sw1 CKd23: 2 steps
lem-sw1-CKd23 : ⟪ (ℓ "丼乎丼") ⟫ʷ ≈ ⟪ (ℓ "乂") ⟫ʷ
lem-sw1-CKd23 = derive (ℓ "丼乎丼") (ℓ "乂")
  (rw 0 q86 ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 CX30: 6 steps
lem-sw1-CX30 : ⟪ (ℓ "丼乐丼") ⟫ʷ ≈ ⟪ (ℓ "乐") ⟫ʷ
lem-sw1-CX30 = derive (ℓ "丼乐丼") (ℓ "乐")
  (re 1 1 (ℓ "乏丼丳丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q23 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "乐") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))

-- sw1 CK30: 6 steps
lem-sw1-CK30 : ⟪ (ℓ "丼乑丼") ⟫ʷ ≈ ⟪ (ℓ "乑") ⟫ʷ
lem-sw1-CK30 = derive (ℓ "丼乑丼") (ℓ "乑")
  (re 1 1 (ℓ "乏丼临丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q87 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "乑") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))

-- sw1 CKd30: 6 steps
lem-sw1-CKd30 : ⟪ (ℓ "丼乒丼") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
lem-sw1-CKd30 = derive (ℓ "丼乒丼") (ℓ "乒")
  (re 1 1 (ℓ "乏丼丵丼乏") ∷
   rw 0 q59 ∷
   rw⁻ 2 q88 ∷
   rw 3 q61 ∷
   re 0 5 (ℓ "乒") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 113 W

-- sw1 CX31: 2 steps
lem-sw1-CX31 : ⟪ (ℓ "丼乓丼") ⟫ʷ ≈ ⟪ (ℓ "乖") ⟫ʷ
lem-sw1-CX31 = derive (ℓ "丼乓丼") (ℓ "乖")
  (rw 0 q89 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 359 W

-- sw1 CK31: 2 steps
lem-sw1-CK31 : ⟪ (ℓ "丼乔丼") ⟫ʷ ≈ ⟪ (ℓ "乗") ⟫ʷ
lem-sw1-CK31 = derive (ℓ "丼乔丼") (ℓ "乗")
  (rw 0 q90 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 360 W

-- sw1 CKd31: 2 steps
lem-sw1-CKd31 : ⟪ (ℓ "丼乕丼") ⟫ʷ ≈ ⟪ (ℓ "乘") ⟫ʷ
lem-sw1-CKd31 = derive (ℓ "丼乕丼") (ℓ "乘")
  (rw 0 q91 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 114 W

-- sw1 CX32: 2 steps
lem-sw1-CX32 : ⟪ (ℓ "丼乖丼") ⟫ʷ ≈ ⟪ (ℓ "乓") ⟫ʷ
lem-sw1-CX32 = derive (ℓ "丼乖丼") (ℓ "乓")
  (rw 0 q92 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 361 W

-- sw1 CK32: 2 steps
lem-sw1-CK32 : ⟪ (ℓ "丼乗丼") ⟫ʷ ≈ ⟪ (ℓ "乔") ⟫ʷ
lem-sw1-CK32 = derive (ℓ "丼乗丼") (ℓ "乔")
  (rw 0 q93 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 362 W

-- sw1 CKd32: 2 steps
lem-sw1-CKd32 : ⟪ (ℓ "丼乘丼") ⟫ʷ ≈ ⟪ (ℓ "乕") ⟫ʷ
lem-sw1-CKd32 = derive (ℓ "丼乘丼") (ℓ "乕")
  (rw 0 q94 ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 17 W

-- sw1 CCZ012: 12 steps
lem-sw1-CCZ012 : ⟪ (ℓ "丼乙丼") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
lem-sw1-CCZ012 = derive (ℓ "丼乙丼") (ℓ "乙")
  (re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 0 q66 ∷
   rw 3 q58 ∷
   re 1 3 (ℓ "个") ∷
   rw 2 q67 ∷
   rw 5 q58 ∷
   re 3 3 (ℓ "个") ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 4 q34 ∷
   rw 0 q95 ∷
   re 0 5 (ℓ "乙") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 26 W

-- sw1 CCZ013: 36 steps
lem-sw1-CCZ013 : ⟪ (ℓ "丼乚丼") ⟫ʷ ≈ ⟪ (ℓ "乛") ⟫ʷ
lem-sw1-CCZ013 = derive (ℓ "丼乚丼") (ℓ "乛")
  (re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q19 ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q19 ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q21 ∷
   rw 0 q72 ∷
   rw 3 q58 ∷
   re 1 3 (ℓ "个") ∷
   rw 2 q73 ∷
   rw 5 q58 ∷
   re 3 3 (ℓ "个") ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q59 ∷
   rw⁻ 6 q60 ∷
   rw 7 q61 ∷
   re 4 5 (ℓ "中") ∷
   rw 0 q25 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q96 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 43 W

-- sw1 CCZ023: 36 steps
lem-sw1-CCZ023 : ⟪ (ℓ "丼乛丼") ⟫ʷ ≈ ⟪ (ℓ "乚") ⟫ʷ
lem-sw1-CCZ023 = derive (ℓ "丼乛丼") (ℓ "乚")
  (re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q8 ∷
   rw 0 q81 ∷
   re 2 1 (ℓ "丼丣丼") ∷
   rw 1 q34 ∷
   rw 2 q82 ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 3 q34 ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q59 ∷
   rw⁻ 6 q60 ∷
   rw 7 q61 ∷
   re 4 5 (ℓ "中") ∷
   rw 0 q18 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q21 ∷
   rw⁻ 2 q19 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q21 ∷
   rw⁻ 4 q19 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q21 ∷
   rw 1 q97 ∷
   re 1 5 (ℓ "乙") ∷
   re 0 3 (ℓ "乚") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 52 W

-- sw1 CCZ123: 9 steps
lem-sw1-CCZ123 : ⟪ (ℓ "丼乜丼") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
lem-sw1-CCZ123 = derive (ℓ "丼乜丼") (ℓ "乜")
  (re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q81 ∷
   rw 1 q69 ∷
   rw 2 q82 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 0 q98 ∷
   re 0 5 (ℓ "乜") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q100 : Eqn
  q100 = wE 46 W

-- sw1 TOFF012: 15 steps
lem-sw1-TOFF012 : ⟪ (ℓ "丼九丼") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
lem-sw1-TOFF012 = derive (ℓ "丼九丼") (ℓ "九")
  (re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q36 ∷
   rw 1 q66 ∷
   rw 4 q58 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q67 ∷
   rw 6 q58 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q34 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q100 ∷
   re 0 8 (ℓ "九") ∷
   rw 1 q34 ∷ []) Eq.refl

-- sw1 TOFF013: 45 steps
lem-sw1-TOFF013 : ⟪ (ℓ "丼乞丼") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
lem-sw1-TOFF013 = derive (ℓ "丼乞丼") (ℓ "也")
  (re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q22 ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q20 ∷
   rw 9 q21 ∷
   rw⁻ 0 q36 ∷
   rw 1 q72 ∷
   rw 4 q58 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q73 ∷
   rw 6 q58 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q59 ∷
   rw⁻ 7 q60 ∷
   rw 8 q61 ∷
   re 5 5 (ℓ "中") ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q25 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q9 ∷
   rw 8 q12 ∷
   rw 1 q13 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 56 W

-- sw1 TOFF023: 45 steps
lem-sw1-TOFF023 : ⟪ (ℓ "丼也丼") ⟫ʷ ≈ ⟪ (ℓ "乞") ⟫ʷ
lem-sw1-TOFF023 = derive (ℓ "丼也丼") (ℓ "乞")
  (re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q1 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw⁻ 0 q36 ∷
   rw 1 q81 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 2 q34 ∷
   rw 3 q82 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q34 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q59 ∷
   rw⁻ 7 q60 ∷
   rw 8 q61 ∷
   re 5 5 (ℓ "中") ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q99 ∷
   rw 0 q18 ∷
   rw⁻ 1 q22 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw⁻ 3 q19 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q21 ∷
   rw⁻ 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   rw⁻ 8 q20 ∷
   rw 1 q101 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 1 q34 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 363 W

-- sw1 TOFF102: 15 steps
lem-sw1-TOFF102 : ⟪ (ℓ "丼习丼") ⟫ʷ ≈ ⟪ (ℓ "乣") ⟫ʷ
lem-sw1-TOFF102 = derive (ℓ "丼习丼") (ℓ "乣")
  (re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 0 q42 ∷
   rw 1 q66 ∷
   rw 4 q58 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q67 ∷
   rw 6 q58 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q34 ∷
   rw 6 q42 ∷
   rw⁻ 7 q99 ∷
   rw 0 q102 ∷
   re 0 8 (ℓ "乣") ∷
   rw 1 q34 ∷ []) Eq.refl
