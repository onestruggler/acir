{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D018 (W : Ws) where

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
  q1 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 340 W
  q7 : Eqn
  q7 = wE 20 W
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = wE 21 W
  q10 : Eqn
  q10 = wE 22 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 23 W
  q13 : Eqn
  q13 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q16 : Eqn
  q16 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 334 W
  q23 : Eqn
  q23 = wE 14 W

-- sw1 TOFF103: 45 steps
lem-sw1-TOFF103 : ⟪ (ℓ "丼乡丼") ⟫ʷ ≈ ⟪ (ℓ "乤") ⟫ʷ
lem-sw1-TOFF103 = derive (ℓ "丼乡丼") (ℓ "乤")
  (re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q1 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q9 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q6 ∷
   rw⁻ 7 q13 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q15 ∷
   rw 8 q21 ∷
   rw 1 q22 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 49 W
  q25 : Eqn
  q25 = wE 50 W
  q26 : Eqn
  q26 = wE 51 W
  q27 : Eqn
  q27 = wE 364 W
  q28 : Eqn
  q28 = wE 365 W

-- sw1 TOFF123: 12 steps
lem-sw1-TOFF123 : ⟪ (ℓ "丼乢丼") ⟫ʷ ≈ ⟪ (ℓ "乥") ⟫ʷ
lem-sw1-TOFF123 = derive (ℓ "丼乢丼") (ℓ "乥")
  (re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q6 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q6 ∷
   rw 7 q27 ∷
   rw 0 q28 ∷
   re 0 8 (ℓ "乥") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 345 W
  q30 : Eqn
  q30 = wE 18 W
  q31 : Eqn
  q31 = wE 19 W
  q32 : Eqn
  q32 = wE 366 W

-- sw1 TOFF201: 15 steps
lem-sw1-TOFF201 : ⟪ (ℓ "丼乣丼") ⟫ʷ ≈ ⟪ (ℓ "习") ⟫ʷ
lem-sw1-TOFF201 = derive (ℓ "丼乣丼") (ℓ "习")
  (re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q29 ∷
   rw 1 q30 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q31 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q23 ∷
   rw 6 q29 ∷
   rw⁻ 7 q13 ∷
   rw 0 q32 ∷
   re 0 8 (ℓ "习") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 30 W
  q34 : Eqn
  q34 = wE 27 W
  q35 : Eqn
  q35 = wE 122 W
  q36 : Eqn
  q36 = wE 31 W
  q37 : Eqn
  q37 = wE 196 W

-- sw1 TOFF203: 45 steps
lem-sw1-TOFF203 : ⟪ (ℓ "丼乤丼") ⟫ʷ ≈ ⟪ (ℓ "乡") ⟫ʷ
lem-sw1-TOFF203 = derive (ℓ "丼乤丼") (ℓ "乡")
  (re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q15 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q29 ∷
   rw 1 q24 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 2 q23 ∷
   rw 3 q26 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q23 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q29 ∷
   rw⁻ 7 q13 ∷
   rw 0 q2 ∷
   rw⁻ 1 q1 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 1 q37 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 367 W

-- sw1 TOFF213: 12 steps
lem-sw1-TOFF213 : ⟪ (ℓ "丼乥丼") ⟫ʷ ≈ ⟪ (ℓ "乢") ⟫ʷ
lem-sw1-TOFF213 = derive (ℓ "丼乥丼") (ℓ "乢")
  (re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q29 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q29 ∷
   rw 7 q27 ∷
   rw 0 q38 ∷
   re 0 8 (ℓ "乢") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 335 W
  q40 : Eqn
  q40 = eqn (ℓ "丼东") (ℓ "东丼") (low₃-comm ((Swap ↑)) (K))
  q41 : Eqn
  q41 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q42 : Eqn
  q42 = wE 337 W

-- sw1 TOFF301: 45 steps
lem-sw1-TOFF301 : ⟪ (ℓ "丼书丼") ⟫ʷ ≈ ⟪ (ℓ "乧") ⟫ʷ
lem-sw1-TOFF301 = derive (ℓ "丼书丼") (ℓ "乧")
  (re 1 1 (ℓ "乏乣乏") ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q39 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q39 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 0 q40 ∷
   rw 1 q7 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q9 ∷
   rw 6 q8 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q40 ∷
   rw⁻ 7 q13 ∷
   rw 0 q14 ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q19 ∷
   rw 7 q20 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q41 ∷
   rw 8 q21 ∷
   rw 1 q42 ∷
   re 1 8 (ℓ "乨") ∷
   re 0 3 (ℓ "乧") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 336 W
  q44 : Eqn
  q44 = wE 368 W

-- sw1 TOFF302: 45 steps
lem-sw1-TOFF302 : ⟪ (ℓ "丼乧丼") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
lem-sw1-TOFF302 = derive (ℓ "丼乧丼") (ℓ "书")
  (re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q41 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q40 ∷
   rw 1 q24 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 2 q23 ∷
   rw 3 q26 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 4 q23 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q10 ∷
   rw⁻ 7 q11 ∷
   rw 8 q12 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q40 ∷
   rw⁻ 7 q13 ∷
   rw 0 q2 ∷
   rw 1 q43 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q43 ∷
   rw⁻ 8 q4 ∷
   rw 1 q44 ∷
   re 1 8 (ℓ "乣") ∷
   re 0 3 (ℓ "书") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 369 W

-- sw1 TOFF312: 12 steps
lem-sw1-TOFF312 : ⟪ (ℓ "丼乨丼") ⟫ʷ ≈ ⟪ (ℓ "乨") ⟫ʷ
lem-sw1-TOFF312 = derive (ℓ "丼乨丼") (ℓ "乨")
  (re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q40 ∷
   rw 1 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw 4 q25 ∷
   rw 5 q7 ∷
   rw 6 q40 ∷
   rw 7 q27 ∷
   rw 0 q45 ∷
   re 0 8 (ℓ "乨") ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))

-- sw2 S0: 2 steps
lem-sw2-S0 : ⟪ (ℓ "乏丈乏") ⟫ʷ ≈ ⟪ (ℓ "丈") ⟫ʷ
lem-sw2-S0 = derive (ℓ "乏丈乏") (ℓ "丈")
  (rw⁻ 0 q46 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))

-- sw2 Sd0: 2 steps
lem-sw2-Sd0 : ⟪ (ℓ "乏三乏") ⟫ʷ ≈ ⟪ (ℓ "三") ⟫ʷ
lem-sw2-Sd0 = derive (ℓ "乏三乏") (ℓ "三")
  (rw⁻ 0 q47 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))

-- sw2 K0: 2 steps
lem-sw2-K0 : ⟪ (ℓ "乏上乏") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
lem-sw2-K0 = derive (ℓ "乏上乏") (ℓ "上")
  (rw⁻ 0 q48 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))

-- sw2 Kd0: 2 steps
lem-sw2-Kd0 : ⟪ (ℓ "乏下乏") ⟫ʷ ≈ ⟪ (ℓ "下") ⟫ʷ
lem-sw2-Kd0 = derive (ℓ "乏下乏") (ℓ "下")
  (rw⁻ 0 q49 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))

-- sw2 X0: 2 steps
lem-sw2-X0 : ⟪ (ℓ "乏丌乏") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-sw2-X0 = derive (ℓ "乏丌乏") (ℓ "丌")
  (rw⁻ 0 q50 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (ℓ "不乏") (ℓ "乏不") (low₁-comm (Z) ((Swap ↑)))

-- sw2 Z0: 2 steps
lem-sw2-Z0 : ⟪ (ℓ "乏不乏") ⟫ʷ ≈ ⟪ (ℓ "不") ⟫ʷ
lem-sw2-Z0 = derive (ℓ "乏不乏") (ℓ "不")
  (rw⁻ 0 q51 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))

-- sw2 S1: 2 steps
lem-sw2-S1 : ⟪ (ℓ "乏与乏") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
lem-sw2-S1 = derive (ℓ "乏与乏") (ℓ "与")
  (rw⁻ 0 q52 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))

-- sw2 Sd1: 2 steps
lem-sw2-Sd1 : ⟪ (ℓ "乏丏乏") ⟫ʷ ≈ ⟪ (ℓ "丏") ⟫ʷ
lem-sw2-Sd1 = derive (ℓ "乏丏乏") (ℓ "丏")
  (rw⁻ 0 q53 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K1: 2 steps
lem-sw2-K1 : ⟪ (ℓ "乏丐乏") ⟫ʷ ≈ ⟪ (ℓ "丐") ⟫ʷ
lem-sw2-K1 = derive (ℓ "乏丐乏") (ℓ "丐")
  (rw⁻ 0 q1 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "丑乏") (ℓ "乏丑") (low-comm (((K • iI) ↑)) (Swap))

-- sw2 Kd1: 2 steps
lem-sw2-Kd1 : ⟪ (ℓ "乏丑乏") ⟫ʷ ≈ ⟪ (ℓ "丑") ⟫ʷ
lem-sw2-Kd1 = derive (ℓ "乏丑乏") (ℓ "丑")
  (rw⁻ 0 q54 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))

-- sw2 X1: 2 steps
lem-sw2-X1 : ⟪ (ℓ "乏丒乏") ⟫ʷ ≈ ⟪ (ℓ "丒") ⟫ʷ
lem-sw2-X1 = derive (ℓ "乏丒乏") (ℓ "丒")
  (rw⁻ 0 q55 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (ℓ "专乏") (ℓ "乏专") (low-comm ((Z ↑)) (Swap))

-- sw2 Z1: 2 steps
lem-sw2-Z1 : ⟪ (ℓ "乏专乏") ⟫ʷ ≈ ⟪ (ℓ "专") ⟫ʷ
lem-sw2-Z1 = derive (ℓ "乏专乏") (ℓ "专")
  (rw⁻ 0 q56 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 151 W

-- sw2 S2: 2 steps
lem-sw2-S2 : ⟪ (ℓ "乏且乏") ⟫ʷ ≈ ⟪ (ℓ "业") ⟫ʷ
lem-sw2-S2 = derive (ℓ "乏且乏") (ℓ "业")
  (rw 0 q57 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 153 W

-- sw2 Sd2: 2 steps
lem-sw2-Sd2 : ⟪ (ℓ "乏丕乏") ⟫ʷ ≈ ⟪ (ℓ "丛") ⟫ʷ
lem-sw2-Sd2 = derive (ℓ "乏丕乏") (ℓ "丛")
  (rw 0 q58 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K2: 2 steps
lem-sw2-K2 : ⟪ (ℓ "乏世乏") ⟫ʷ ≈ ⟪ (ℓ "东") ⟫ʷ
lem-sw2-K2 = derive (ℓ "乏世乏") (ℓ "东")
  (rw 0 q39 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 370 W

-- sw2 Kd2: 2 steps
lem-sw2-Kd2 : ⟪ (ℓ "乏丗乏") ⟫ʷ ≈ ⟪ (ℓ "丝") ⟫ʷ
lem-sw2-Kd2 = derive (ℓ "乏丗乏") (ℓ "丝")
  (rw 0 q59 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 175 W

-- sw2 X2: 2 steps
lem-sw2-X2 : ⟪ (ℓ "乏丘乏") ⟫ʷ ≈ ⟪ (ℓ "丞") ⟫ʷ
lem-sw2-X2 = derive (ℓ "乏丘乏") (ℓ "丞")
  (rw 0 q60 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 371 W

-- sw2 Z2: 2 steps
lem-sw2-Z2 : ⟪ (ℓ "乏丙乏") ⟫ʷ ≈ ⟪ (ℓ "丟") ⟫ʷ
lem-sw2-Z2 = derive (ℓ "乏丙乏") (ℓ "丟")
  (rw 0 q61 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 372 W

-- sw2 S3: 2 steps
lem-sw2-S3 : ⟪ (ℓ "乏业乏") ⟫ʷ ≈ ⟪ (ℓ "且") ⟫ʷ
lem-sw2-S3 = derive (ℓ "乏业乏") (ℓ "且")
  (rw 0 q62 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 373 W

-- sw2 Sd3: 2 steps
lem-sw2-Sd3 : ⟪ (ℓ "乏丛乏") ⟫ʷ ≈ ⟪ (ℓ "丕") ⟫ʷ
lem-sw2-Sd3 = derive (ℓ "乏丛乏") (ℓ "丕")
  (rw 0 q63 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 K3: 2 steps
lem-sw2-K3 : ⟪ (ℓ "乏东乏") ⟫ʷ ≈ ⟪ (ℓ "世") ⟫ʷ
lem-sw2-K3 = derive (ℓ "乏东乏") (ℓ "世")
  (rw 0 q43 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 374 W

-- sw2 Kd3: 2 steps
lem-sw2-Kd3 : ⟪ (ℓ "乏丝乏") ⟫ʷ ≈ ⟪ (ℓ "丗") ⟫ʷ
lem-sw2-Kd3 = derive (ℓ "乏丝乏") (ℓ "丗")
  (rw 0 q64 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 375 W

-- sw2 X3: 2 steps
lem-sw2-X3 : ⟪ (ℓ "乏丞乏") ⟫ʷ ≈ ⟪ (ℓ "丘") ⟫ʷ
lem-sw2-X3 = derive (ℓ "乏丞乏") (ℓ "丘")
  (rw 0 q65 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 376 W

-- sw2 Z3: 2 steps
lem-sw2-Z3 : ⟪ (ℓ "乏丟乏") ⟫ʷ ≈ ⟪ (ℓ "丙") ⟫ʷ
lem-sw2-Z3 = derive (ℓ "乏丟乏") (ℓ "丙")
  (rw 0 q66 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS01: 2 steps
lem-sw2-CS01 : ⟪ (ℓ "乏丠乏") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
lem-sw2-CS01 = derive (ℓ "乏丠乏") (ℓ "丠")
  (rw⁻ 0 q11 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))

-- sw2 CSd01: 2 steps
lem-sw2-CSd01 : ⟪ (ℓ "乏両乏") ⟫ʷ ≈ ⟪ (ℓ "両") ⟫ʷ
lem-sw2-CSd01 = derive (ℓ "乏両乏") (ℓ "両")
  (rw⁻ 0 q67 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (ℓ "丢乏") (ℓ "乏丢") (low-comm (CZ) (Swap))

-- sw2 CZ01: 2 steps
lem-sw2-CZ01 : ⟪ (ℓ "乏丢乏") ⟫ʷ ≈ ⟪ (ℓ "丢") ⟫ʷ
lem-sw2-CZ01 = derive (ℓ "乏丢乏") (ℓ "丢")
  (rw⁻ 0 q68 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX01: 2 steps
lem-sw2-CX01 : ⟪ (ℓ "乏丣乏") ⟫ʷ ≈ ⟪ (ℓ "丣") ⟫ʷ
lem-sw2-CX01 = derive (ℓ "乏丣乏") (ℓ "丣")
  (rw⁻ 0 q3 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))

-- sw2 CK01: 2 steps
lem-sw2-CK01 : ⟪ (ℓ "乏两乏") ⟫ʷ ≈ ⟪ (ℓ "两") ⟫ʷ
lem-sw2-CK01 = derive (ℓ "乏两乏") (ℓ "两")
  (rw⁻ 0 q69 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (ℓ "严乏") (ℓ "乏严") (low-comm ((S • CK₀₁)) (Swap))

-- sw2 CKd01: 2 steps
lem-sw2-CKd01 : ⟪ (ℓ "乏严乏") ⟫ʷ ≈ ⟪ (ℓ "严") ⟫ʷ
lem-sw2-CKd01 = derive (ℓ "乏严乏") (ℓ "严")
  (rw⁻ 0 q70 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS02: 3 steps
lem-sw2-CS02 : ⟪ (ℓ "乏丧乏") ⟫ʷ ≈ ⟪ (ℓ "中") ⟫ʷ
lem-sw2-CS02 = derive (ℓ "乏丧乏") (ℓ "中")
  (rw 2 q2 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd02: 3 steps
lem-sw2-CSd02 : ⟪ (ℓ "乏丨乏") ⟫ʷ ≈ ⟪ (ℓ "丮") ⟫ʷ
lem-sw2-CSd02 = derive (ℓ "乏丨乏") (ℓ "丮")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ02: 3 steps
lem-sw2-CZ02 : ⟪ (ℓ "乏丩乏") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
lem-sw2-CZ02 = derive (ℓ "乏丩乏") (ℓ "丯")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丯") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX02: 3 steps
lem-sw2-CX02 : ⟪ (ℓ "乏个乏") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
lem-sw2-CX02 = derive (ℓ "乏个乏") (ℓ "丰")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丰") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK02: 3 steps
lem-sw2-CK02 : ⟪ (ℓ "乏丫乏") ⟫ʷ ≈ ⟪ (ℓ "丱") ⟫ʷ
lem-sw2-CK02 = derive (ℓ "乏丫乏") (ℓ "丱")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丱") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd02: 3 steps
lem-sw2-CKd02 : ⟪ (ℓ "乏丬乏") ⟫ʷ ≈ ⟪ (ℓ "串") ⟫ʷ
lem-sw2-CKd02 = derive (ℓ "乏丬乏") (ℓ "串")
  (rw 2 q2 ∷
   re 0 3 (ℓ "串") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS03: 3 steps
lem-sw2-CS03 : ⟪ (ℓ "乏中乏") ⟫ʷ ≈ ⟪ (ℓ "丧") ⟫ʷ
lem-sw2-CS03 = derive (ℓ "乏中乏") (ℓ "丧")
  (re 1 1 (ℓ "乏丧乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd03: 3 steps
lem-sw2-CSd03 : ⟪ (ℓ "乏丮乏") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
lem-sw2-CSd03 = derive (ℓ "乏丮乏") (ℓ "丨")
  (re 1 1 (ℓ "乏丨乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ03: 3 steps
lem-sw2-CZ03 : ⟪ (ℓ "乏丯乏") ⟫ʷ ≈ ⟪ (ℓ "丩") ⟫ʷ
lem-sw2-CZ03 = derive (ℓ "乏丯乏") (ℓ "丩")
  (re 1 1 (ℓ "乏丩乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX03: 3 steps
lem-sw2-CX03 : ⟪ (ℓ "乏丰乏") ⟫ʷ ≈ ⟪ (ℓ "个") ⟫ʷ
lem-sw2-CX03 = derive (ℓ "乏丰乏") (ℓ "个")
  (re 1 1 (ℓ "乏个乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK03: 3 steps
lem-sw2-CK03 : ⟪ (ℓ "乏丱乏") ⟫ʷ ≈ ⟪ (ℓ "丫") ⟫ʷ
lem-sw2-CK03 = derive (ℓ "乏丱乏") (ℓ "丫")
  (re 1 1 (ℓ "乏丫乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd03: 3 steps
lem-sw2-CKd03 : ⟪ (ℓ "乏串乏") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
lem-sw2-CKd03 = derive (ℓ "乏串乏") (ℓ "丬")
  (re 1 1 (ℓ "乏丬乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))

-- sw2 CX10: 2 steps
lem-sw2-CX10 : ⟪ (ℓ "乏丳乏") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
lem-sw2-CX10 = derive (ℓ "乏丳乏") (ℓ "丳")
  (rw⁻ 0 q71 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))

-- sw2 CK10: 2 steps
lem-sw2-CK10 : ⟪ (ℓ "乏临乏") ⟫ʷ ≈ ⟪ (ℓ "临") ⟫ʷ
lem-sw2-CK10 = derive (ℓ "乏临乏") (ℓ "临")
  (rw⁻ 0 q72 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))

-- sw2 CKd10: 2 steps
lem-sw2-CKd10 : ⟪ (ℓ "乏丵乏") ⟫ʷ ≈ ⟪ (ℓ "丵") ⟫ʷ
lem-sw2-CKd10 = derive (ℓ "乏丵乏") (ℓ "丵")
  (rw⁻ 0 q73 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS12: 3 steps
lem-sw2-CS12 : ⟪ (ℓ "乏丶乏") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
lem-sw2-CS12 = derive (ℓ "乏丶乏") (ℓ "丽")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丽") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd12: 3 steps
lem-sw2-CSd12 : ⟪ (ℓ "乏丷乏") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
lem-sw2-CSd12 = derive (ℓ "乏丷乏") (ℓ "举")
  (rw 2 q2 ∷
   re 0 3 (ℓ "举") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ12: 3 steps
lem-sw2-CZ12 : ⟪ (ℓ "乏丸乏") ⟫ʷ ≈ ⟪ (ℓ "丿") ⟫ʷ
lem-sw2-CZ12 = derive (ℓ "乏丸乏") (ℓ "丿")
  (rw 2 q2 ∷
   re 0 3 (ℓ "丿") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX12: 3 steps
lem-sw2-CX12 : ⟪ (ℓ "乏丹乏") ⟫ʷ ≈ ⟪ (ℓ "乀") ⟫ʷ
lem-sw2-CX12 = derive (ℓ "乏丹乏") (ℓ "乀")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乀") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK12: 3 steps
lem-sw2-CK12 : ⟪ (ℓ "乏为乏") ⟫ʷ ≈ ⟪ (ℓ "乁") ⟫ʷ
lem-sw2-CK12 = derive (ℓ "乏为乏") (ℓ "乁")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乁") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd12: 3 steps
lem-sw2-CKd12 : ⟪ (ℓ "乏主乏") ⟫ʷ ≈ ⟪ (ℓ "乂") ⟫ʷ
lem-sw2-CKd12 = derive (ℓ "乏主乏") (ℓ "乂")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乂") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CS13: 3 steps
lem-sw2-CS13 : ⟪ (ℓ "乏丽乏") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
lem-sw2-CS13 = derive (ℓ "乏丽乏") (ℓ "丶")
  (re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CSd13: 3 steps
lem-sw2-CSd13 : ⟪ (ℓ "乏举乏") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
lem-sw2-CSd13 = derive (ℓ "乏举乏") (ℓ "丷")
  (re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CZ13: 3 steps
lem-sw2-CZ13 : ⟪ (ℓ "乏丿乏") ⟫ʷ ≈ ⟪ (ℓ "丸") ⟫ʷ
lem-sw2-CZ13 = derive (ℓ "乏丿乏") (ℓ "丸")
  (re 1 1 (ℓ "乏丸乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX13: 3 steps
lem-sw2-CX13 : ⟪ (ℓ "乏乀乏") ⟫ʷ ≈ ⟪ (ℓ "丹") ⟫ʷ
lem-sw2-CX13 = derive (ℓ "乏乀乏") (ℓ "丹")
  (re 1 1 (ℓ "乏丹乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK13: 3 steps
lem-sw2-CK13 : ⟪ (ℓ "乏乁乏") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
lem-sw2-CK13 = derive (ℓ "乏乁乏") (ℓ "为")
  (re 1 1 (ℓ "乏为乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd13: 3 steps
lem-sw2-CKd13 : ⟪ (ℓ "乏乂乏") ⟫ʷ ≈ ⟪ (ℓ "主") ⟫ʷ
lem-sw2-CKd13 = derive (ℓ "乏乂乏") (ℓ "主")
  (re 1 1 (ℓ "乏主乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX20: 3 steps
lem-sw2-CX20 : ⟪ (ℓ "乏乃乏") ⟫ʷ ≈ ⟪ (ℓ "乐") ⟫ʷ
lem-sw2-CX20 = derive (ℓ "乏乃乏") (ℓ "乐")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乐") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK20: 3 steps
lem-sw2-CK20 : ⟪ (ℓ "乏乄乏") ⟫ʷ ≈ ⟪ (ℓ "乑") ⟫ʷ
lem-sw2-CK20 = derive (ℓ "乏乄乏") (ℓ "乑")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd20: 3 steps
lem-sw2-CKd20 : ⟪ (ℓ "乏久乏") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
lem-sw2-CKd20 = derive (ℓ "乏久乏") (ℓ "乒")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乒") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX21: 3 steps
lem-sw2-CX21 : ⟪ (ℓ "乏乆乏") ⟫ʷ ≈ ⟪ (ℓ "乓") ⟫ʷ
lem-sw2-CX21 = derive (ℓ "乏乆乏") (ℓ "乓")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乓") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK21: 3 steps
lem-sw2-CK21 : ⟪ (ℓ "乏乇乏") ⟫ʷ ≈ ⟪ (ℓ "乔") ⟫ʷ
lem-sw2-CK21 = derive (ℓ "乏乇乏") (ℓ "乔")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乔") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd21: 3 steps
lem-sw2-CKd21 : ⟪ (ℓ "乏么乏") ⟫ʷ ≈ ⟪ (ℓ "乕") ⟫ʷ
lem-sw2-CKd21 = derive (ℓ "乏么乏") (ℓ "乕")
  (rw 2 q2 ∷
   re 0 3 (ℓ "乕") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 71 W

-- sw2 CS23: 2 steps
lem-sw2-CS23 : ⟪ (ℓ "乏义乏") ⟫ʷ ≈ ⟪ (ℓ "义") ⟫ʷ
lem-sw2-CS23 = derive (ℓ "乏义乏") (ℓ "义")
  (rw 0 q74 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 72 W

-- sw2 CSd23: 2 steps
lem-sw2-CSd23 : ⟪ (ℓ "乏乊乏") ⟫ʷ ≈ ⟪ (ℓ "乊") ⟫ʷ
lem-sw2-CSd23 = derive (ℓ "乏乊乏") (ℓ "乊")
  (rw 0 q75 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 377 W

-- sw2 CZ23: 2 steps
lem-sw2-CZ23 : ⟪ (ℓ "乏之乏") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
lem-sw2-CZ23 = derive (ℓ "乏之乏") (ℓ "之")
  (rw 0 q76 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 378 W

-- sw2 CX23: 2 steps
lem-sw2-CX23 : ⟪ (ℓ "乏乌乏") ⟫ʷ ≈ ⟪ (ℓ "乖") ⟫ʷ
lem-sw2-CX23 = derive (ℓ "乏乌乏") (ℓ "乖")
  (rw 0 q77 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 379 W

-- sw2 CK23: 2 steps
lem-sw2-CK23 : ⟪ (ℓ "乏乍乏") ⟫ʷ ≈ ⟪ (ℓ "乗") ⟫ʷ
lem-sw2-CK23 = derive (ℓ "乏乍乏") (ℓ "乗")
  (rw 0 q78 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 380 W

-- sw2 CKd23: 2 steps
lem-sw2-CKd23 : ⟪ (ℓ "乏乎乏") ⟫ʷ ≈ ⟪ (ℓ "乘") ⟫ʷ
lem-sw2-CKd23 = derive (ℓ "乏乎乏") (ℓ "乘")
  (rw 0 q79 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX30: 3 steps
lem-sw2-CX30 : ⟪ (ℓ "乏乐乏") ⟫ʷ ≈ ⟪ (ℓ "乃") ⟫ʷ
lem-sw2-CX30 = derive (ℓ "乏乐乏") (ℓ "乃")
  (re 1 1 (ℓ "乏乃乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK30: 3 steps
lem-sw2-CK30 : ⟪ (ℓ "乏乑乏") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
lem-sw2-CK30 = derive (ℓ "乏乑乏") (ℓ "乄")
  (re 1 1 (ℓ "乏乄乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd30: 3 steps
lem-sw2-CKd30 : ⟪ (ℓ "乏乒乏") ⟫ʷ ≈ ⟪ (ℓ "久") ⟫ʷ
lem-sw2-CKd30 = derive (ℓ "乏乒乏") (ℓ "久")
  (re 1 1 (ℓ "乏久乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CX31: 3 steps
lem-sw2-CX31 : ⟪ (ℓ "乏乓乏") ⟫ʷ ≈ ⟪ (ℓ "乆") ⟫ʷ
lem-sw2-CX31 = derive (ℓ "乏乓乏") (ℓ "乆")
  (re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CK31: 3 steps
lem-sw2-CK31 : ⟪ (ℓ "乏乔乏") ⟫ʷ ≈ ⟪ (ℓ "乇") ⟫ʷ
lem-sw2-CK31 = derive (ℓ "乏乔乏") (ℓ "乇")
  (re 1 1 (ℓ "乏乇乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CKd31: 3 steps
lem-sw2-CKd31 : ⟪ (ℓ "乏乕乏") ⟫ʷ ≈ ⟪ (ℓ "么") ⟫ʷ
lem-sw2-CKd31 = derive (ℓ "乏乕乏") (ℓ "么")
  (re 1 1 (ℓ "乏么乏") ∷
   rw 0 q5 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 381 W

-- sw2 CX32: 2 steps
lem-sw2-CX32 : ⟪ (ℓ "乏乖乏") ⟫ʷ ≈ ⟪ (ℓ "乌") ⟫ʷ
lem-sw2-CX32 = derive (ℓ "乏乖乏") (ℓ "乌")
  (rw 0 q80 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 382 W

-- sw2 CK32: 2 steps
lem-sw2-CK32 : ⟪ (ℓ "乏乗乏") ⟫ʷ ≈ ⟪ (ℓ "乍") ⟫ʷ
lem-sw2-CK32 = derive (ℓ "乏乗乏") (ℓ "乍")
  (rw 0 q81 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 383 W

-- sw2 CKd32: 2 steps
lem-sw2-CKd32 : ⟪ (ℓ "乏乘乏") ⟫ʷ ≈ ⟪ (ℓ "乎") ⟫ʷ
lem-sw2-CKd32 = derive (ℓ "乏乘乏") (ℓ "乎")
  (rw 0 q82 ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 43 W

-- sw2 CCZ012: 22 steps
lem-sw2-CCZ012 : ⟪ (ℓ "乏乙乏") ⟫ʷ ≈ ⟪ (ℓ "乚") ⟫ʷ
lem-sw2-CCZ012 = derive (ℓ "乏乙乏") (ℓ "乚")
  (re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 1 q83 ∷
   re 1 5 (ℓ "乙") ∷
   re 0 3 (ℓ "乚") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CCZ013: 22 steps
lem-sw2-CCZ013 : ⟪ (ℓ "乏乚乏") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
lem-sw2-CCZ013 = derive (ℓ "乏乚乏") (ℓ "乙")
  (re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q5 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q5 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 0 q83 ∷
   re 0 5 (ℓ "乙") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 73 W

-- sw2 CCZ023: 38 steps
lem-sw2-CCZ023 : ⟪ (ℓ "乏乛乏") ⟫ʷ ≈ ⟪ (ℓ "乛") ⟫ʷ
lem-sw2-CCZ023 = derive (ℓ "乏乛乏") (ℓ "乛")
  (re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q16 ∷
   rw 2 q33 ∷
   rw 3 q18 ∷
   rw 4 q33 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q19 ∷
   rw 6 q34 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q36 ∷
   rw 0 q74 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丰") ∷
   rw 2 q75 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丰") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 0 q14 ∷
   rw 1 q16 ∷
   re 3 1 (ℓ "乏个乏") ∷
   rw 2 q19 ∷
   rw 3 q17 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "乀") ∷
   rw 3 q18 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw 4 q19 ∷
   rw 5 q17 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "乀") ∷
   rw 5 q20 ∷
   rw 1 q84 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 CCZ123: 12 steps
lem-sw2-CCZ123 : ⟪ (ℓ "乏乜乏") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
lem-sw2-CCZ123 = derive (ℓ "乏乜乏") (ℓ "乜")
  (re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q74 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "乀") ∷
   rw 2 q75 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乀") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 0 q84 ∷
   re 0 5 (ℓ "乜") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 56 W

-- sw2 TOFF012: 28 steps
lem-sw2-TOFF012 : ⟪ (ℓ "乏九乏") ⟫ʷ ≈ ⟪ (ℓ "乞") ⟫ʷ
lem-sw2-TOFF012 = derive (ℓ "乏九乏") (ℓ "乞")
  (re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q48 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw⁻ 1 q48 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q48 ∷
   rw⁻ 8 q4 ∷
   rw 1 q85 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF013: 28 steps
lem-sw2-TOFF013 : ⟪ (ℓ "乏乞乏") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
lem-sw2-TOFF013 = derive (ℓ "乏乞乏") (ℓ "九")
  (re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q48 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q48 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw⁻ 0 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q85 ∷
   re 0 8 (ℓ "九") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 121 W
  q87 : Eqn
  q87 = wE 123 W
  q88 : Eqn
  q88 = wE 384 W

-- sw2 TOFF023: 47 steps
lem-sw2-TOFF023 : ⟪ (ℓ "乏也乏") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
lem-sw2-TOFF023 = derive (ℓ "乏也乏") (ℓ "也")
  (re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q86 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q86 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw⁻ 0 q48 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丰") ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丰") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q4 ∷
   rw 0 q14 ∷
   rw 1 q87 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw 3 q19 ∷
   rw 4 q17 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q19 ∷
   rw 6 q17 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q20 ∷
   rw 7 q87 ∷
   rw 8 q21 ∷
   rw 1 q88 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF102: 28 steps
lem-sw2-TOFF102 : ⟪ (ℓ "乏习乏") ⟫ʷ ≈ ⟪ (ℓ "乡") ⟫ʷ
lem-sw2-TOFF102 = derive (ℓ "乏习乏") (ℓ "乡")
  (re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q1 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw⁻ 1 q1 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 1 q37 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF103: 28 steps
lem-sw2-TOFF103 : ⟪ (ℓ "乏乡乏") ⟫ʷ ≈ ⟪ (ℓ "习") ⟫ʷ
lem-sw2-TOFF103 = derive (ℓ "乏乡乏") (ℓ "习")
  (re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q1 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q1 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw⁻ 0 q1 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q4 ∷
   rw 0 q37 ∷
   re 0 8 (ℓ "习") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (ℓ "丁乏") (ℓ "乏丁") (low-comm ((iI ↑)) (Swap))

-- sw2 TOFF123: 15 steps
lem-sw2-TOFF123 : ⟪ (ℓ "乏乢乏") ⟫ʷ ≈ ⟪ (ℓ "乢") ⟫ʷ
lem-sw2-TOFF123 = derive (ℓ "乏乢乏") (ℓ "乢")
  (re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw⁻ 0 q1 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乀") ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乀") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q1 ∷
   rw⁻ 7 q89 ∷
   rw 0 q88 ∷
   re 0 8 (ℓ "乢") ∷
   rw 1 q5 ∷ []) Eq.refl

-- sw2 TOFF201: 28 steps
lem-sw2-TOFF201 : ⟪ (ℓ "乏乣乏") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
lem-sw2-TOFF201 = derive (ℓ "乏乣乏") (ℓ "书")
  (re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q39 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q39 ∷
   rw⁻ 7 q4 ∷
   rw 0 q2 ∷
   rw 1 q43 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q43 ∷
   rw⁻ 8 q4 ∷
   rw 1 q44 ∷
   re 1 8 (ℓ "乣") ∷
   re 0 3 (ℓ "书") ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 385 W

-- sw2 TOFF203: 47 steps
lem-sw2-TOFF203 : ⟪ (ℓ "乏乤乏") ⟫ʷ ≈ ⟪ (ℓ "乧") ⟫ʷ
lem-sw2-TOFF203 = derive (ℓ "乏乤乏") (ℓ "乧")
  (re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q33 ∷
   rw 4 q18 ∷
   rw 5 q33 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   rw 7 q34 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q15 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw 0 q39 ∷
   rw 1 q74 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丰") ∷
   rw 3 q75 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丰") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q39 ∷
   rw⁻ 7 q4 ∷
   rw 0 q14 ∷
   rw 1 q41 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw 3 q19 ∷
   rw 4 q17 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q19 ∷
   rw 6 q17 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q20 ∷
   rw 7 q41 ∷
   rw 8 q21 ∷
   rw 1 q90 ∷
   re 1 8 (ℓ "乨") ∷
   re 0 3 (ℓ "乧") ∷
   rw 1 q5 ∷ []) Eq.refl
