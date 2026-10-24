{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D150 (W : Ws) where

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
  q1 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q2 : Eqn
  q2 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))
  q3 : Eqn
  q3 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q4 : Eqn
  q4 = eqn (ℓ "临乎") (ℓ "乎临") (low-comm (CK₁₀) ((S • CK₀₁)))
  q5 : Eqn
  q5 = wE 691 W
  q6 : Eqn
  q6 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q7 : Eqn
  q7 = eqn (ℓ "与乎") (ℓ "乎与") (low-comm ((S ↑)) ((S • CK₀₁)))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 693 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 692 W
  q17 : Eqn
  q17 = wE 142 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CKd23 X2]: 137 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd23-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乎丘") ⟫ʷ ≈ ⟪ (ℓ "丘乎丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd23-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乎丘") (ℓ "丘乎丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q1 ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q3 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q5 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 15 q1 ∷
   rw 16 q2 ∷
   rw 17 q1 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q6 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q1 ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q1 ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q1 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q1 ∷
   rw 9 q2 ∷
   rw 10 q1 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 6 q5 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q9 ∷
   rw 5 q11 ∷
   rw 6 q12 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 8 q8 ∷
   rw⁻ 7 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q9 ∷
   rw 4 q11 ∷
   rw 5 q12 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   rw 7 q13 ∷
   rw 8 q14 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q9 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   rw 6 q17 ∷
   rw 7 q14 ∷
   rw 6 q8 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q9 ∷
   rw 2 q11 ∷
   rw 3 q12 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 5 q8 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q9 ∷
   rw 1 q11 ∷
   rw 2 q12 ∷
   rw 1 q9 ∷
   rw 2 q10 ∷
   rw 3 q9 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 4 q8 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q9 ∷
   rw 0 q11 ∷
   rw 1 q12 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 737 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS12 CS12 CK21 CS12 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-CS12-CK21-CS12-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丶丶乇丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶乇丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-CS12-CK21-CS12-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丶丶乇丶丘") (ℓ "丘丶丶乇丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 655 W
  q20 : Eqn
  q20 = wE 1 W
  q21 : Eqn
  q21 = wE 20 W
  q22 : Eqn
  q22 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q23 : Eqn
  q23 = wE 49 W
  q24 : Eqn
  q24 = wE 3 W
  q25 : Eqn
  q25 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q26 : Eqn
  q26 = wE 695 W
  q27 : Eqn
  q27 = wE 210 W
  q28 : Eqn
  q28 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q29 : Eqn
  q29 = wE 103 W
  q30 : Eqn
  q30 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q31 : Eqn
  q31 = wE 607 W
  q32 : Eqn
  q32 = wE 656 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [CS13]: 389 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS13 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丽") ⟫ʷ ≈ ⟪ (ℓ "丽丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS13 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丽") (ℓ "丽丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q19 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q20 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q20 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q21 ∷
   rw 33 q22 ∷
   rw 32 q23 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q24 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q24 ∷
   re 30 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q20 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q20 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q21 ∷
   rw 32 q22 ∷
   rw 31 q23 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q24 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q24 ∷
   re 29 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q20 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q20 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q21 ∷
   rw 31 q25 ∷
   rw 30 q23 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q24 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q24 ∷
   re 28 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q20 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q20 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   rw 29 q23 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q24 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q24 ∷
   re 27 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q20 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q20 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   rw 28 q23 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q24 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q24 ∷
   re 26 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q20 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q20 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q21 ∷
   rw 28 q22 ∷
   rw 27 q23 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q24 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q24 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q26 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q20 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q20 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q21 ∷
   rw 26 q22 ∷
   rw 25 q23 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q24 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q24 ∷
   re 23 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q20 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q20 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q21 ∷
   rw 25 q22 ∷
   rw 24 q23 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q24 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q24 ∷
   re 22 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q20 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q20 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q21 ∷
   rw 24 q22 ∷
   rw 23 q23 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q24 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q24 ∷
   re 21 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q20 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q20 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q21 ∷
   rw 23 q22 ∷
   rw 22 q23 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q24 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q24 ∷
   re 20 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q20 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q20 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q21 ∷
   rw 22 q22 ∷
   rw 21 q23 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q24 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q24 ∷
   re 19 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q20 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q20 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q21 ∷
   rw 21 q22 ∷
   rw 20 q23 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q24 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q24 ∷
   re 18 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q20 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q20 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q21 ∷
   rw 20 q22 ∷
   rw 19 q23 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q24 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q24 ∷
   re 17 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q20 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q20 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q21 ∷
   rw 19 q22 ∷
   rw 18 q23 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q24 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q24 ∷
   re 16 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q20 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q20 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q21 ∷
   rw 18 q22 ∷
   rw 17 q23 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q24 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q24 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q27 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q20 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q20 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q21 ∷
   rw 16 q25 ∷
   rw 15 q23 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q24 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q24 ∷
   re 13 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q20 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q20 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q21 ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q24 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q24 ∷
   re 12 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q20 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q20 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q21 ∷
   rw 14 q22 ∷
   rw 13 q23 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q24 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q24 ∷
   re 11 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q20 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q20 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q21 ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q24 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q24 ∷
   re 10 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q20 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q20 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q21 ∷
   rw 12 q22 ∷
   rw 11 q23 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q24 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q24 ∷
   re 9 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q20 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q20 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q21 ∷
   rw 11 q22 ∷
   rw 10 q23 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q24 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q24 ∷
   re 8 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q20 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q20 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q21 ∷
   rw 10 q22 ∷
   rw 9 q23 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q24 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q24 ∷
   re 7 3 (ℓ "丽") ∷
   rw 6 q26 ∷
   rw 7 q20 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q24 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q28 ∷
   rw 7 q24 ∷
   rw 6 q20 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q24 ∷
   rw 4 q28 ∷
   rw 5 q29 ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q28 ∷
   rw 6 q24 ∷
   rw 5 q20 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q24 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q30 ∷
   rw 5 q24 ∷
   rw 4 q20 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q24 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q20 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q28 ∷
   rw 4 q24 ∷
   rw 3 q20 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q24 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 3 q20 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q28 ∷
   rw 3 q24 ∷
   rw 2 q20 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q24 ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q20 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q28 ∷
   rw 2 q24 ∷
   rw 1 q32 ∷ []) Eq.refl
