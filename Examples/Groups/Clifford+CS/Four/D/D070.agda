{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D070 (W : Ws) where

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
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q9 : Eqn
  q9 = wE 572 W
  q10 : Eqn
  q10 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3]: 155 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞") (ℓ "丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 60 q1 ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw 54 q5 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q6 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   rw 29 q2 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q4 ∷
   rw 25 q7 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q5 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q8 ∷
   rw 14 q7 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q8 ∷
   rw 9 q7 ∷
   rw 8 q8 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q5 ∷
   rw 1 q9 ∷
   rw 0 q10 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乔") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乔") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乔") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乐") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乐") ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q3 ∷
   rw 30 q10 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乑") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw⁻ 38 q7 ∷
   rw⁻ 39 q8 ∷
   rw⁻ 40 q7 ∷
   rw⁻ 41 q8 ∷
   rw⁻ 42 q4 ∷
   rw⁻ 43 q4 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 46 q8 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q4 ∷
   rw⁻ 49 q4 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q4 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw⁻ 54 q4 ∷
   rw⁻ 55 q4 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 58 q7 ∷
   rw⁻ 59 q7 ∷
   rw 60 q5 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q15 : Eqn
  q15 = wE 528 W
  q16 : Eqn
  q16 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "与乗") (ℓ "乗与") (low-comm ((S ↑)) (CK₁₀))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 140 W
  q23 : Eqn
  q23 = wE 529 W
  q24 : Eqn
  q24 = wE 142 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 7 W
  q27 : Eqn
  q27 = wE 530 W
  q28 : Eqn
  q28 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CK32 X3]: 179 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞") (ℓ "丞乗丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 28 q11 ∷
   rw 29 q12 ∷
   rw 30 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q13 ∷
   rw 27 q14 ∷
   rw 28 q13 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q13 ∷
   rw 25 q14 ∷
   rw 26 q13 ∷
   rw 23 q13 ∷
   rw 24 q14 ∷
   rw 25 q13 ∷
   rw 22 q15 ∷
   rw 21 q13 ∷
   rw 22 q14 ∷
   rw 23 q13 ∷
   rw 20 q13 ∷
   rw 21 q14 ∷
   rw 22 q13 ∷
   rw 19 q13 ∷
   rw 20 q14 ∷
   rw 21 q13 ∷
   rw 18 q13 ∷
   rw 19 q14 ∷
   rw 20 q13 ∷
   rw 17 q13 ∷
   rw 18 q14 ∷
   rw 19 q13 ∷
   rw 16 q13 ∷
   rw 17 q14 ∷
   rw 18 q13 ∷
   rw 15 q16 ∷
   rw 16 q17 ∷
   rw 17 q16 ∷
   rw 14 q11 ∷
   rw 15 q12 ∷
   rw 16 q11 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q13 ∷
   rw 12 q13 ∷
   rw 13 q14 ∷
   rw 14 q13 ∷
   rw 11 q13 ∷
   rw 12 q14 ∷
   rw 13 q13 ∷
   rw 10 q16 ∷
   rw 11 q17 ∷
   rw 12 q16 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   rw 8 q16 ∷
   rw 9 q17 ∷
   rw 10 q16 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   rw 6 q15 ∷
   rw 9 q18 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 6 q19 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q21 ∷
   rw 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (ℓ "乔") ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q21 ∷
   rw 9 q24 ∷
   rw 10 q21 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q25 ∷
   rw 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q21 ∷
   rw 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (ℓ "乔") ∷
   rw 5 q23 ∷
   rw 4 q19 ∷
   rw 5 q20 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q25 ∷
   rw 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q21 ∷
   rw 4 q26 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q27 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 7 q28 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q25 ∷
   rw 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 3 q19 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q21 ∷
   rw 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (ℓ "乔") ∷
   rw 3 q23 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q19 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q21 ∷
   rw 6 q24 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q25 ∷
   rw 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q21 ∷
   rw 2 q26 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q27 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q19 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw 5 q28 ∷
   rw 6 q21 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q25 ∷
   rw 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q21 ∷
   rw 1 q26 ∷
   rw⁻ 0 q21 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q27 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q21 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q25 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 573 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CK30 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑丞") (ℓ "丞乑丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q5 ∷
   rw 29 q2 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q4 ∷
   rw 25 q7 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q5 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q8 ∷
   rw 14 q7 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q8 ∷
   rw 9 q7 ∷
   rw 8 q8 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q5 ∷
   rw 1 q29 ∷
   rw 0 q10 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q10 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q8 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 17 q7 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 24 q4 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q7 ∷
   rw 32 q5 ∷ []) Eq.refl
