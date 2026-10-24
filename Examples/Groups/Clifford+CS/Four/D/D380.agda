{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D380 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = wE 1048 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CSd01 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒両丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒両丒") (ℓ "丒両丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   rw 15 q5 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q4 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q4 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q4 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q6 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q9 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q9 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q9 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q4 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1049 W
  q11 : Eqn
  q11 = wE 65 W
  q12 : Eqn
  q12 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q13 : Eqn
  q13 = wE 48 W

-- pass [X1 CS13 X1] [CS02]: 7 steps
lem-pass-X1-CS13-X1-vs-CS02 : ⟪ (ℓ "丒丽丒丧") ⟫ʷ ≈ ⟪ (ℓ "丧丒丽丒") ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS02 = derive (ℓ "丒丽丒丧") (ℓ "丧丒丽丒")
  (rw 2 q10 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q11 ∷
   rw⁻ 2 q12 ∷
   rw 3 q13 ∷
   re 1 3 (ℓ "丧") ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 56 W
  q18 : Eqn
  q18 = wE 1050 W

-- pass [X1 CS13 X1] [TOFF013]: 65 steps
lem-pass-X1-CS13-X1-vs-TOFF013 : ⟪ (ℓ "丒丽丒乞") ⟫ʷ ≈ ⟪ (ℓ "乞丒丽丒") ⟫ʷ
lem-pass-X1-CS13-X1-vs-TOFF013 = derive (ℓ "丒丽丒乞") (ℓ "乞丒丽丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q18 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1051 W
  q20 : Eqn
  q20 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))

-- pass [X1 CS13 X1] [CSd02]: 7 steps
lem-pass-X1-CS13-X1-vs-CSd02 : ⟪ (ℓ "丒丽丒丨") ⟫ʷ ≈ ⟪ (ℓ "丨丒丽丒") ⟫ʷ
lem-pass-X1-CS13-X1-vs-CSd02 = derive (ℓ "丒丽丒丨") (ℓ "丨丒丽丒")
  (rw 2 q19 ∷
   re 2 1 (ℓ "丼両丼") ∷
   rw 1 q11 ∷
   rw⁻ 2 q20 ∷
   rw 3 q13 ∷
   re 1 3 (ℓ "丨") ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1052 W
  q22 : Eqn
  q22 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q23 : Eqn
  q23 = wE 1053 W

-- pass [X1 CK13 X1] [CS02]: 7 steps
lem-pass-X1-CK13-X1-vs-CS02 : ⟪ (ℓ "丒乁丒丧") ⟫ʷ ≈ ⟪ (ℓ "丧丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS02 = derive (ℓ "丒乁丒丧") (ℓ "丧丒乁丒")
  (rw 2 q10 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q21 ∷
   rw⁻ 2 q22 ∷
   rw 3 q23 ∷
   re 1 3 (ℓ "丧") ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1054 W

-- pass [X1 CK13 X1] [TOFF013]: 65 steps
lem-pass-X1-CK13-X1-vs-TOFF013 : ⟪ (ℓ "丒乁丒乞") ⟫ʷ ≈ ⟪ (ℓ "乞丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-TOFF013 = derive (ℓ "丒乁丒乞") (ℓ "乞丒乁丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏为乏") ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q24 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乁") ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (ℓ "両乍") (ℓ "乍両") (low-comm ((CS • CS • CS)) (CK₀₁))

-- pass [X1 CK13 X1] [CSd02]: 7 steps
lem-pass-X1-CK13-X1-vs-CSd02 : ⟪ (ℓ "丒乁丒丨") ⟫ʷ ≈ ⟪ (ℓ "丨丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-CSd02 = derive (ℓ "丒乁丒丨") (ℓ "丨丒乁丒")
  (rw 2 q19 ∷
   re 2 1 (ℓ "丼両丼") ∷
   rw 1 q21 ∷
   rw⁻ 2 q25 ∷
   rw 3 q23 ∷
   re 1 3 (ℓ "丨") ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 84 W
  q27 : Eqn
  q27 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q28 : Eqn
  q28 = wE 47 W

-- pass [X1 CSd13 X1] [CS02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CS02 : ⟪ (ℓ "丒举丒丧") ⟫ʷ ≈ ⟪ (ℓ "丧丒举丒") ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS02 = derive (ℓ "丒举丒丧") (ℓ "丧丒举丒")
  (rw 2 q10 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q26 ∷
   rw⁻ 2 q27 ∷
   rw 3 q28 ∷
   re 1 3 (ℓ "丧") ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1055 W

-- pass [X1 CSd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CSd13-X1-vs-TOFF013 : ⟪ (ℓ "丒举丒乞") ⟫ʷ ≈ ⟪ (ℓ "乞丒举丒") ⟫ʷ
lem-pass-X1-CSd13-X1-vs-TOFF013 = derive (ℓ "丒举丒乞") (ℓ "乞丒举丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q29 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X1 CSd13 X1] [CSd02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CSd02 : ⟪ (ℓ "丒举丒丨") ⟫ʷ ≈ ⟪ (ℓ "丨丒举丒") ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CSd02 = derive (ℓ "丒举丒丨") (ℓ "丨丒举丒")
  (rw 2 q19 ∷
   re 2 1 (ℓ "丼両丼") ∷
   rw 1 q26 ∷
   rw⁻ 2 q30 ∷
   rw 3 q28 ∷
   re 1 3 (ℓ "丨") ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1056 W
  q32 : Eqn
  q32 = eqn (ℓ "丒乌") (ℓ "乌丒") (low-comm ((X ↑)) (CX₀₁))
  q33 : Eqn
  q33 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q34 : Eqn
  q34 = wE 1057 W
  q35 : Eqn
  q35 = wE 1058 W
  q36 : Eqn
  q36 = wE 1059 W

-- pass [CCZ123] [X1 CS01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CS01-X1 : ⟪ (ℓ "乜丒丠丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丒乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-CS01-X1 = derive (ℓ "乜丒丠丒") (ℓ "丒丠丒乜")
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q33 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q7 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw 4 q34 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q7 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 2 q35 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q7 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q4 ∷
   rw 0 q35 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q38 : Eqn
  q38 = wE 1060 W
  q39 : Eqn
  q39 = wE 1061 W

-- pass [CCZ123] [X1 CK10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CK10-X1 : ⟪ (ℓ "乜丒临丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丒乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-CK10-X1 = derive (ℓ "乜丒临丒") (ℓ "丒临丒乜")
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q37 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw 4 q38 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q37 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 2 q39 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q4 ∷
   rw 0 q39 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1062 W

-- pass [CS03] [iI]: 9 steps
lem-pass-CS03-vs-iI : ⟪ (ℓ "中一") ⟫ʷ ≈ ⟪ (ℓ "一中") ⟫ʷ
lem-pass-CS03-vs-iI = derive (ℓ "中一") (ℓ "一中")
  (rw 2 q1 ∷
   rw 1 q16 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q40 ∷
   rw⁻ 0 q16 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (ℓ "专乏") (ℓ "乏专") (low-comm ((Z ↑)) (Swap))
  q42 : Eqn
  q42 = wE 1063 W

-- pass [CS03] [Z1]: 9 steps
lem-pass-CS03-vs-Z1 : ⟪ (ℓ "中专") ⟫ʷ ≈ ⟪ (ℓ "专中") ⟫ʷ
lem-pass-CS03-vs-Z1 = derive (ℓ "中专") (ℓ "专中")
  (rw 2 q1 ∷
   rw 1 q41 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q42 ∷
   rw⁻ 0 q41 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 5 W
  q44 : Eqn
  q44 = eqn (ℓ "並丙") (ℓ "丙並") (low-comm (Swap) (Z))
  q45 : Eqn
  q45 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q46 : Eqn
  q46 = wE 7 W
  q47 : Eqn
  q47 = wE 1064 W
  q48 : Eqn
  q48 = wE 27 W
  q49 : Eqn
  q49 = wE 31 W

-- pass [CS03] [Z2]: 15 steps
lem-pass-CS03-vs-Z2 : ⟪ (ℓ "中丙") ⟫ʷ ≈ ⟪ (ℓ "丙中") ⟫ʷ
lem-pass-CS03-vs-Z2 = derive (ℓ "中丙") (ℓ "丙中")
  (rw 2 q43 ∷
   rw⁻ 1 q44 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q45 ∷
   rw 1 q46 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q47 ∷
   rw 0 q44 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q45 ∷
   rw 2 q48 ∷
   rw 3 q45 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1065 W
  q51 : Eqn
  q51 = wE 1066 W
  q52 : Eqn
  q52 = wE 371 W

-- pass [CS03] [Z3]: 9 steps
lem-pass-CS03-vs-Z3 : ⟪ (ℓ "中丟") ⟫ʷ ≈ ⟪ (ℓ "丟中") ⟫ʷ
lem-pass-CS03-vs-Z3 = derive (ℓ "中丟") (ℓ "丟中")
  (rw 2 q1 ∷
   rw 1 q50 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q51 ∷
   rw 0 q52 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 552 W

-- pass [CS03] [CZ13]: 11 steps
lem-pass-CS03-vs-CZ13 : ⟪ (ℓ "中丿") ⟫ʷ ≈ ⟪ (ℓ "丿中") ⟫ʷ
lem-pass-CS03-vs-CZ13 = derive (ℓ "中丿") (ℓ "丿中")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q53 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丿") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q55 : Eqn
  q55 = wE 890 W

-- pass [CS03] [CZ23]: 15 steps
lem-pass-CS03-vs-CZ23 : ⟪ (ℓ "中之") ⟫ʷ ≈ ⟪ (ℓ "之中") ⟫ʷ
lem-pass-CS03-vs-CZ23 = derive (ℓ "中之") (ℓ "之中")
  (rw 2 q43 ∷
   rw⁻ 1 q54 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q45 ∷
   rw 1 q46 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q55 ∷
   rw 0 q54 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q45 ∷
   rw 2 q48 ∷
   rw 3 q45 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1067 W

-- pass [TOFF012] [iI]: 1 steps
lem-pass-TOFF012-vs-iI : ⟪ (ℓ "九一") ⟫ʷ ≈ ⟪ (ℓ "一九") ⟫ʷ
lem-pass-TOFF012-vs-iI = derive (ℓ "九一") (ℓ "一九")
  (rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1068 W

-- pass [TOFF012] [Z1]: 1 steps
lem-pass-TOFF012-vs-Z1 : ⟪ (ℓ "九专") ⟫ʷ ≈ ⟪ (ℓ "专九") ⟫ʷ
lem-pass-TOFF012-vs-Z1 = derive (ℓ "九专") (ℓ "专九")
  (rw 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 1069 W

-- pass [TOFF012] [Z2]: 1 steps
lem-pass-TOFF012-vs-Z2 : ⟪ (ℓ "九丙") ⟫ʷ ≈ ⟪ (ℓ "丙九") ⟫ʷ
lem-pass-TOFF012-vs-Z2 = derive (ℓ "九丙") (ℓ "丙九")
  (rw 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 1070 W

-- pass [TOFF012] [CZ12]: 1 steps
lem-pass-TOFF012-vs-CZ12 : ⟪ (ℓ "九丸") ⟫ʷ ≈ ⟪ (ℓ "丸九") ⟫ʷ
lem-pass-TOFF012-vs-CZ12 = derive (ℓ "九丸") (ℓ "丸九")
  (rw 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (ℓ "九丟") (ℓ "丟九") (low₃-comm (Toff) (Z))

-- pass [TOFF012] [Z3]: 1 steps
lem-pass-TOFF012-vs-Z3 : ⟪ (ℓ "九丟") ⟫ʷ ≈ ⟪ (ℓ "丟九") ⟫ʷ
lem-pass-TOFF012-vs-Z3 = derive (ℓ "九丟") (ℓ "丟九")
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 100 W
  q62 : Eqn
  q62 = wE 909 W
  q63 : Eqn
  q63 = wE 6 W
  q64 : Eqn
  q64 = wE 908 W
  q65 : Eqn
  q65 = wE 39 W
  q66 : Eqn
  q66 = eqn (ℓ "両之") (ℓ "之両") (low-comm ((CS • CS • CS)) (CZ))
  q67 : Eqn
  q67 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q68 : Eqn
  q68 = wE 104 W

-- comm CCZ012 CZ23: 19 steps
lem-comm-CCZ012-CZ23 : ⟪ (ℓ "乙之") ⟫ʷ ≈ ⟪ (ℓ "之乙") ⟫ʷ
lem-comm-CCZ012-CZ23 = derive (ℓ "乙之") (ℓ "之乙")
  (rw 0 q61 ∷
   rw 4 q62 ∷
   rw 5 q43 ∷
   rw⁻ 4 q54 ∷
   rw 3 q63 ∷
   rw 4 q64 ∷
   rw 3 q54 ∷
   rw 4 q65 ∷
   rw 5 q49 ∷
   rw 2 q66 ∷
   rw 3 q43 ∷
   rw⁻ 2 q54 ∷
   rw 1 q63 ∷
   rw 2 q64 ∷
   rw 1 q54 ∷
   rw 2 q65 ∷
   rw 3 q49 ∷
   rw 0 q67 ∷
   rw 1 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 1071 W

-- pass [CSd03] [iI]: 9 steps
lem-pass-CSd03-vs-iI : ⟪ (ℓ "丮一") ⟫ʷ ≈ ⟪ (ℓ "一丮") ⟫ʷ
lem-pass-CSd03-vs-iI = derive (ℓ "丮一") (ℓ "一丮")
  (rw 2 q1 ∷
   rw 1 q16 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q69 ∷
   rw⁻ 0 q16 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1072 W

-- pass [CSd03] [Z1]: 9 steps
lem-pass-CSd03-vs-Z1 : ⟪ (ℓ "丮专") ⟫ʷ ≈ ⟪ (ℓ "专丮") ⟫ʷ
lem-pass-CSd03-vs-Z1 = derive (ℓ "丮专") (ℓ "专丮")
  (rw 2 q1 ∷
   rw 1 q41 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q70 ∷
   rw⁻ 0 q41 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 76 W
  q72 : Eqn
  q72 = wE 1073 W
  q73 : Eqn
  q73 = wE 29 W

-- pass [CSd03] [Z2]: 15 steps
lem-pass-CSd03-vs-Z2 : ⟪ (ℓ "丮丙") ⟫ʷ ≈ ⟪ (ℓ "丙丮") ⟫ʷ
lem-pass-CSd03-vs-Z2 = derive (ℓ "丮丙") (ℓ "丙丮")
  (rw 2 q43 ∷
   rw⁻ 1 q44 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw⁻ 2 q45 ∷
   rw 1 q71 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (ℓ "举") ∷
   rw 1 q72 ∷
   rw 0 q44 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q45 ∷
   rw 2 q73 ∷
   rw 3 q45 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 1074 W

-- pass [CSd03] [Z3]: 9 steps
lem-pass-CSd03-vs-Z3 : ⟪ (ℓ "丮丟") ⟫ʷ ≈ ⟪ (ℓ "丟丮") ⟫ʷ
lem-pass-CSd03-vs-Z3 = derive (ℓ "丮丟") (ℓ "丟丮")
  (rw 2 q1 ∷
   rw 1 q50 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q74 ∷
   rw 0 q52 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 551 W

-- pass [CSd03] [CZ13]: 11 steps
lem-pass-CSd03-vs-CZ13 : ⟪ (ℓ "丮丿") ⟫ʷ ≈ ⟪ (ℓ "丿丮") ⟫ʷ
lem-pass-CSd03-vs-CZ13 = derive (ℓ "丮丿") (ℓ "丿丮")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q75 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丿") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 1075 W

-- pass [CSd03] [CZ23]: 15 steps
lem-pass-CSd03-vs-CZ23 : ⟪ (ℓ "丮之") ⟫ʷ ≈ ⟪ (ℓ "之丮") ⟫ʷ
lem-pass-CSd03-vs-CZ23 = derive (ℓ "丮之") (ℓ "之丮")
  (rw 2 q43 ∷
   rw⁻ 1 q54 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw⁻ 2 q45 ∷
   rw 1 q71 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (ℓ "举") ∷
   rw 1 q76 ∷
   rw 0 q54 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q45 ∷
   rw 2 q73 ∷
   rw 3 q45 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q78 : Eqn
  q78 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q79 : Eqn
  q79 = wE 1076 W
  q80 : Eqn
  q80 = wE 1077 W

-- pass [CCZ123] [X1 CKd10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CKd10-X1 : ⟪ (ℓ "乜丒丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒丵丒乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-CKd10-X1 = derive (ℓ "乜丒丵丒") (ℓ "丒丵丒乜")
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q77 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q78 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw 4 q79 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q78 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q77 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q78 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 2 q80 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q78 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q4 ∷
   rw 0 q80 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q82 : Eqn
  q82 = wE 1078 W
  q83 : Eqn
  q83 = wE 1079 W

-- pass [CCZ123] [X1 CSd01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CSd01-X1 : ⟪ (ℓ "乜丒両丒") ⟫ʷ ≈ ⟪ (ℓ "丒両丒乜") ⟫ʷ
lem-pass-CCZ123-vs-X1-CSd01-X1 = derive (ℓ "乜丒両丒") (ℓ "丒両丒乜")
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q81 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q3 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw 4 q82 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q81 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 2 q83 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q4 ∷
   rw 0 q83 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 1080 W
  q85 : Eqn
  q85 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))
  q86 : Eqn
  q86 = wE 1081 W

-- pass [X1 CKd13 X1] [CS02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CS02 : ⟪ (ℓ "丒乂丒丧") ⟫ʷ ≈ ⟪ (ℓ "丧丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02 = derive (ℓ "丒乂丒丧") (ℓ "丧丒乂丒")
  (rw 2 q10 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q84 ∷
   rw⁻ 2 q85 ∷
   rw 3 q86 ∷
   re 1 3 (ℓ "丧") ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 1082 W

-- pass [X1 CKd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CKd13-X1-vs-TOFF013 : ⟪ (ℓ "丒乂丒乞") ⟫ʷ ≈ ⟪ (ℓ "乞丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013 = derive (ℓ "丒乂丒乞") (ℓ "乞丒乂丒")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏主乏") ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q87 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乂") ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (ℓ "両乎") (ℓ "乎両") (low-comm ((CS • CS • CS)) ((S • CK₀₁)))

-- pass [X1 CKd13 X1] [CSd02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CSd02 : ⟪ (ℓ "丒乂丒丨") ⟫ʷ ≈ ⟪ (ℓ "丨丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CSd02 = derive (ℓ "丒乂丒丨") (ℓ "丨丒乂丒")
  (rw 2 q19 ∷
   re 2 1 (ℓ "丼両丼") ∷
   rw 1 q84 ∷
   rw⁻ 2 q88 ∷
   rw 3 q86 ∷
   re 1 3 (ℓ "丨") ∷
   rw 0 q19 ∷ []) Eq.refl
