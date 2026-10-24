{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D474 (W : Ws) where

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
  q1 = wE 65 W
  q2 : Eqn
  q2 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q3 : Eqn
  q3 = wE 48 W
  q4 : Eqn
  q4 = wE 279 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q6 : Eqn
  q6 = wE 280 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 74 W
  q11 : Eqn
  q11 = wE 606 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 30 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = eqn (ℓ "丧业") (ℓ "业丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (S))
  q16 : Eqn
  q16 = wE 95 W
  q17 : Eqn
  q17 = wE 1226 W

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CS02]: 147 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丧") ⟫ʷ ≈ ⟪ (ℓ "丧丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CS02 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丧") (ℓ "丧丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q1 ∷
   rw⁻ 31 q2 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q1 ∷
   rw⁻ 30 q2 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "丧") ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q1 ∷
   rw⁻ 27 q2 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "丧") ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "丧") ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q9 ∷
   rw 25 q10 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (ℓ "乀") ∷
   rw 25 q11 ∷
   rw 24 q12 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q9 ∷
   rw 26 q13 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q14 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q1 ∷
   rw⁻ 24 q2 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "丧") ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q1 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "丧") ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "丧") ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q1 ∷
   rw⁻ 21 q2 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "丧") ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q1 ∷
   rw⁻ 20 q2 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "丧") ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q1 ∷
   rw⁻ 19 q2 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "丧") ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q1 ∷
   rw⁻ 18 q2 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "丧") ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q1 ∷
   rw⁻ 17 q2 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "丧") ∷
   re 16 1 (ℓ "丼丠丼") ∷
   rw 15 q1 ∷
   rw⁻ 16 q2 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "丧") ∷
   rw⁻ 14 q15 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q4 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "丧") ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "丧") ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q1 ∷
   rw⁻ 12 q2 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "丧") ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 10 q1 ∷
   rw⁻ 11 q2 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "丧") ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "丧") ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "丧") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q1 ∷
   rw⁻ 8 q2 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丧") ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (ℓ "乀") ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q14 ∷
   rw 5 q16 ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   rw 2 q16 ∷
   rw 1 q16 ∷
   rw 0 q16 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = wE 464 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q23 : Eqn
  q23 = wE 1238 W
  q24 : Eqn
  q24 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q26 : Eqn
  q26 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q27 : Eqn
  q27 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q28 : Eqn
  q28 = wE 6 W
  q29 : Eqn
  q29 = wE 892 W
  q30 : Eqn
  q30 = wE 39 W
  q31 : Eqn
  q31 = eqn (ℓ "丈乖") (ℓ "乖丈") (low₁-comm (S) ((CX₁₀ ↑)))
  q32 : Eqn
  q32 = wE 894 W
  q33 : Eqn
  q33 = wE 893 W
  q34 : Eqn
  q34 = wE 1239 W
  q35 : Eqn
  q35 = wE 151 W

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CX32]: 253 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽乖") ⟫ʷ ≈ ⟪ (ℓ "乖丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CX32 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽乖") (ℓ "乖丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (rw 31 q18 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q19 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q19 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q19 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q19 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q19 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw 26 q19 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q19 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q19 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q19 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q19 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q19 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q19 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q19 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q19 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q19 ∷
   rw 14 q20 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 15 q19 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q19 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 12 q19 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q19 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q19 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q19 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q19 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 1 q23 ∷
   rw 2 q18 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q18 ∷
   re 2 3 (ℓ "丽") ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "乔") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "乐") ∷
   rw⁻ 7 q21 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q21 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q21 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q22 ∷
   rw⁻ 14 q24 ∷
   rw⁻ 15 q21 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q21 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 21 q21 ∷
   rw⁻ 22 q21 ∷
   rw⁻ 23 q21 ∷
   rw 26 q18 ∷
   re 24 3 (ℓ "乐") ∷
   rw⁻ 25 q21 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 28 q22 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 30 q21 ∷
   rw 31 q19 ∷
   rw 30 q25 ∷
   rw 29 q25 ∷
   rw 28 q26 ∷
   rw 27 q25 ∷
   rw 26 q25 ∷
   rw 25 q25 ∷
   rw 26 q7 ∷
   rw⁻ 25 q27 ∷
   re 24 1 (ℓ "乏乃乏") ∷
   rw⁻ 26 q9 ∷
   rw 25 q28 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (ℓ "乓") ∷
   rw 25 q29 ∷
   rw 24 q27 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q9 ∷
   rw 26 q30 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q14 ∷
   rw 23 q25 ∷
   rw 22 q25 ∷
   rw 21 q25 ∷
   rw 20 q25 ∷
   rw 19 q25 ∷
   rw 18 q25 ∷
   rw 17 q25 ∷
   rw 16 q25 ∷
   rw 15 q25 ∷
   rw 14 q31 ∷
   rw 13 q26 ∷
   rw 12 q25 ∷
   rw 11 q25 ∷
   rw 10 q25 ∷
   rw 9 q25 ∷
   rw 8 q25 ∷
   rw 7 q25 ∷
   rw 8 q7 ∷
   rw⁻ 7 q27 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q9 ∷
   rw 7 q28 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (ℓ "乓") ∷
   rw 7 q29 ∷
   rw 6 q27 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q9 ∷
   rw 8 q30 ∷
   rw 9 q9 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q14 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 32 q18 ∷
   rw 31 q21 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q21 ∷
   re 25 1 (ℓ "乏乃乏") ∷
   rw 27 q19 ∷
   rw 24 q21 ∷
   rw 23 q21 ∷
   rw 22 q21 ∷
   rw 21 q21 ∷
   rw 20 q21 ∷
   rw 19 q21 ∷
   rw 18 q21 ∷
   rw 17 q21 ∷
   rw 16 q21 ∷
   rw 15 q24 ∷
   rw 14 q22 ∷
   rw 13 q21 ∷
   rw 12 q21 ∷
   rw 11 q21 ∷
   rw 10 q21 ∷
   rw 9 q21 ∷
   rw 8 q21 ∷
   re 7 1 (ℓ "乏乃乏") ∷
   rw 9 q19 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q19 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q19 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 6 q19 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q19 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q19 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q19 ∷
   rw 2 q34 ∷
   rw⁻ 1 q21 ∷
   rw⁻ 2 q21 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 4 q22 ∷
   rw⁻ 5 q21 ∷
   rw⁻ 6 q21 ∷
   rw 9 q18 ∷
   re 7 3 (ℓ "丰") ∷
   rw 10 q18 ∷
   re 8 3 (ℓ "丽") ∷
   rw 11 q18 ∷
   re 9 3 (ℓ "丽") ∷
   rw 12 q18 ∷
   re 10 3 (ℓ "丽") ∷
   rw 13 q18 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q18 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q18 ∷
   re 14 3 (ℓ "乔") ∷
   rw 15 q35 ∷
   rw 18 q18 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q18 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q18 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q18 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q18 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q18 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q18 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q18 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q18 ∷
   re 25 3 (ℓ "丰") ∷
   rw 28 q18 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q18 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q18 ∷
   re 28 3 (ℓ "丽") ∷
   rw 31 q18 ∷
   re 29 3 (ℓ "乔") ∷
   rw 32 q18 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q18 ∷
   re 31 3 (ℓ "丽") ∷
   rw 32 q19 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q37 : Eqn
  q37 = eqn (ℓ "両乗") (ℓ "乗両") (low-comm ((CS • CS • CS)) (CK₁₀))
  q38 : Eqn
  q38 = wE 76 W
  q39 : Eqn
  q39 = wE 608 W
  q40 : Eqn
  q40 = wE 29 W
  q41 : Eqn
  q41 = eqn (ℓ "丨业") (ℓ "业丨") (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (S))
  q42 : Eqn
  q42 = wE 88 W
  q43 : Eqn
  q43 = wE 1227 W

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [CSd02]: 147 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丨") ⟫ʷ ≈ ⟪ (ℓ "丨丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-CSd02 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丨") (ℓ "丨丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (re 31 1 (ℓ "丼両丼") ∷
   rw 30 q1 ∷
   rw⁻ 31 q36 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "丨") ∷
   re 30 1 (ℓ "丼両丼") ∷
   rw 29 q1 ∷
   rw⁻ 30 q36 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "丨") ∷
   re 29 1 (ℓ "丼両丼") ∷
   rw 28 q4 ∷
   rw⁻ 29 q37 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "丨") ∷
   re 28 1 (ℓ "丼両丼") ∷
   rw 27 q1 ∷
   rw⁻ 28 q36 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "丨") ∷
   re 27 1 (ℓ "丼両丼") ∷
   rw 26 q1 ∷
   rw⁻ 27 q36 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "丨") ∷
   re 26 1 (ℓ "丼両丼") ∷
   rw 25 q1 ∷
   rw⁻ 26 q36 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "丨") ∷
   rw 26 q7 ∷
   rw 25 q38 ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw⁻ 26 q9 ∷
   rw 25 q10 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (ℓ "乀") ∷
   rw 25 q39 ∷
   rw 24 q40 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q9 ∷
   rw 26 q13 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "丰") ∷
   rw 26 q14 ∷
   re 24 1 (ℓ "丼両丼") ∷
   rw 23 q1 ∷
   rw⁻ 24 q36 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "丨") ∷
   re 23 1 (ℓ "丼両丼") ∷
   rw 22 q1 ∷
   rw⁻ 23 q36 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "丨") ∷
   re 22 1 (ℓ "丼両丼") ∷
   rw 21 q1 ∷
   rw⁻ 22 q36 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "丨") ∷
   re 21 1 (ℓ "丼両丼") ∷
   rw 20 q1 ∷
   rw⁻ 21 q36 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "丨") ∷
   re 20 1 (ℓ "丼両丼") ∷
   rw 19 q1 ∷
   rw⁻ 20 q36 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "丨") ∷
   re 19 1 (ℓ "丼両丼") ∷
   rw 18 q1 ∷
   rw⁻ 19 q36 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "丨") ∷
   re 18 1 (ℓ "丼両丼") ∷
   rw 17 q1 ∷
   rw⁻ 18 q36 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "丨") ∷
   re 17 1 (ℓ "丼両丼") ∷
   rw 16 q1 ∷
   rw⁻ 17 q36 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "丨") ∷
   re 16 1 (ℓ "丼両丼") ∷
   rw 15 q1 ∷
   rw⁻ 16 q36 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "丨") ∷
   rw⁻ 14 q41 ∷
   re 14 1 (ℓ "丼両丼") ∷
   rw 13 q4 ∷
   rw⁻ 14 q37 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "丨") ∷
   re 13 1 (ℓ "丼両丼") ∷
   rw 12 q1 ∷
   rw⁻ 13 q36 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "丨") ∷
   re 12 1 (ℓ "丼両丼") ∷
   rw 11 q1 ∷
   rw⁻ 12 q36 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "丨") ∷
   re 11 1 (ℓ "丼両丼") ∷
   rw 10 q1 ∷
   rw⁻ 11 q36 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "丨") ∷
   re 10 1 (ℓ "丼両丼") ∷
   rw 9 q1 ∷
   rw⁻ 10 q36 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "丨") ∷
   re 9 1 (ℓ "丼両丼") ∷
   rw 8 q1 ∷
   rw⁻ 9 q36 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "丨") ∷
   re 8 1 (ℓ "丼両丼") ∷
   rw 7 q1 ∷
   rw⁻ 8 q36 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "丨") ∷
   rw 8 q7 ∷
   rw 7 q38 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (ℓ "乀") ∷
   rw 7 q39 ∷
   rw 6 q40 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q14 ∷
   rw 5 q42 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷
   rw 2 q42 ∷
   rw 1 q42 ∷
   rw 0 q42 ∷ []) Eq.refl
