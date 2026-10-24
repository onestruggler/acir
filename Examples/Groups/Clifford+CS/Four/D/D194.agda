{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D194 (W : Ws) where

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
  q1 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q2 : Eqn
  q2 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q3 : Eqn
  q3 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q4 : Eqn
  q4 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q5 : Eqn
  q5 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q6 : Eqn
  q6 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q8 : Eqn
  q8 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = wE 758 W
  q10 : Eqn
  q10 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q11 : Eqn
  q11 = eqn (ℓ "与乗") (ℓ "乗与") (low-comm ((S ↑)) (CK₁₀))
  q12 : Eqn
  q12 = eqn (ℓ "与义") (ℓ "义与") (low-comm ((S ↑)) (CS))
  q13 : Eqn
  q13 = eqn (ℓ "与乘") (ℓ "乘与") (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q17 : Eqn
  q17 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = wE 760 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = wE 140 W
  q25 : Eqn
  q25 = wE 759 W
  q26 : Eqn
  q26 = wE 142 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK32 CS23 CS23 CKd32 X3]: 290 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-CS23-CS23-CKd32-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗义义乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗义义乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-CS23-CS23-CKd32-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗义义乘丞") (ℓ "丞乗义义乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q3 ∷
   rw 33 q3 ∷
   rw 34 q4 ∷
   rw 35 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q3 ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q1 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q7 ∷
   rw 31 q7 ∷
   rw 32 q8 ∷
   rw 33 q5 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q3 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   rw 24 q9 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q3 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q3 ∷
   rw 25 q3 ∷
   rw 26 q4 ∷
   rw 27 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q3 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q3 ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q3 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q1 ∷
   rw 15 q1 ∷
   rw 16 q2 ∷
   rw 17 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q1 ∷
   rw 14 q10 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q12 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   rw 13 q5 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q7 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q3 ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q1 ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q3 ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q1 ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q3 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q1 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q1 ∷
   rw 8 q1 ∷
   rw 9 q2 ∷
   rw 10 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q1 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q3 ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q1 ∷
   rw 6 q9 ∷
   rw 12 q14 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q15 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q19 ∷
   rw 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 6 3 (ℓ "丽") ∷
   rw 6 q21 ∷
   rw 5 q15 ∷
   rw 6 q18 ∷
   rw 7 q17 ∷
   rw 8 q17 ∷
   rw 9 q16 ∷
   rw 10 q15 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q19 ∷
   rw 12 q22 ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q23 ∷
   rw 11 q14 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q15 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q19 ∷
   rw 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q21 ∷
   rw 4 q15 ∷
   rw 5 q18 ∷
   rw 6 q17 ∷
   rw 7 q17 ∷
   rw 8 q16 ∷
   rw 9 q15 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q19 ∷
   rw 11 q22 ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q23 ∷
   rw 10 q14 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q15 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q19 ∷
   rw 4 q24 ∷
   rw⁻ 3 q19 ∷
   re 4 3 (ℓ "乔") ∷
   rw 4 q25 ∷
   rw 3 q15 ∷
   rw 4 q18 ∷
   rw 5 q17 ∷
   rw 6 q17 ∷
   rw 7 q16 ∷
   rw 8 q15 ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q19 ∷
   rw 10 q26 ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q23 ∷
   rw 9 q14 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q15 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q19 ∷
   rw 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q21 ∷
   rw 2 q15 ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   rw 5 q17 ∷
   rw 6 q16 ∷
   rw 7 q15 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q19 ∷
   rw 9 q22 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q23 ∷
   rw 8 q14 ∷
   rw⁻ 7 q15 ∷
   rw⁻ 6 q16 ∷
   rw⁻ 5 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q18 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q19 ∷
   rw 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q21 ∷
   rw 1 q15 ∷
   rw 2 q18 ∷
   rw 3 q17 ∷
   rw 4 q17 ∷
   rw 5 q16 ∷
   rw 6 q15 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q19 ∷
   rw 8 q22 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q23 ∷
   rw 7 q14 ∷
   rw⁻ 6 q15 ∷
   rw⁻ 5 q16 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw⁻ 1 q15 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q19 ∷
   rw 1 q20 ∷
   rw⁻ 0 q19 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q21 ∷
   rw 0 q15 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   rw 3 q17 ∷
   rw 4 q16 ∷
   rw 5 q15 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q19 ∷
   rw 7 q22 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q23 ∷ []) Eq.refl
