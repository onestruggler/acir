{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D201 (W : Ws) where

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
  q3 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 196 W
  q8 : Eqn
  q8 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = wE 803 W
  q12 : Eqn
  q12 = wE 175 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 TOFF103 X3]: 139 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF103-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF103-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乡丞") (ℓ "丞乡丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (ℓ "乏习乏") ∷
   re 33 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 32 q3 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "举") ∷
   rw⁻ 36 q4 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw⁻ 38 q3 ∷
   rw⁻ 39 q5 ∷
   rw 40 q6 ∷
   rw 39 q5 ∷
   rw 38 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q6 ∷
   rw 36 q4 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q6 ∷
   rw 32 q3 ∷
   rw 33 q7 ∷
   re 33 8 (ℓ "习") ∷
   rw 31 q2 ∷
   rw 30 q8 ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   rw 27 q8 ∷
   rw 26 q8 ∷
   rw 25 q8 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q6 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   rw 21 q8 ∷
   rw 20 q8 ∷
   rw 19 q8 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   rw 16 q8 ∷
   rw 15 q8 ∷
   rw 14 q10 ∷
   rw 13 q9 ∷
   rw 12 q8 ∷
   rw 11 q8 ∷
   rw 10 q8 ∷
   rw 9 q8 ∷
   rw 8 q8 ∷
   rw 7 q8 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q6 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q6 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q6 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q12 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q8 ∷
   rw⁻ 11 q8 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q8 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 16 q9 ∷
   rw⁻ 17 q10 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 19 q8 ∷
   rw⁻ 20 q8 ∷
   rw⁻ 21 q8 ∷
   rw⁻ 22 q8 ∷
   rw⁻ 23 q8 ∷
   rw⁻ 24 q8 ∷
   rw⁻ 25 q8 ∷
   rw⁻ 26 q8 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q8 ∷
   rw⁻ 29 q8 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 33 q8 ∷
   rw 34 q6 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q15 : Eqn
  q15 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q17 : Eqn
  q17 = wE 595 W
  q18 : Eqn
  q18 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "与义") (ℓ "义与") (low-comm ((S ↑)) (CS))
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q23 : Eqn
  q23 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q24 : Eqn
  q24 = wE 7 W
  q25 : Eqn
  q25 = wE 597 W
  q26 : Eqn
  q26 = wE 27 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 140 W
  q29 : Eqn
  q29 = wE 596 W
  q30 : Eqn
  q30 = wE 142 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 X3]: 185 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义丞") (ℓ "丞义丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 28 q15 ∷
   rw 29 q16 ∷
   rw 30 q15 ∷
   rw 27 q13 ∷
   rw 28 q14 ∷
   rw 29 q13 ∷
   rw 26 q13 ∷
   rw 27 q14 ∷
   rw 28 q13 ∷
   rw 25 q13 ∷
   rw 26 q14 ∷
   rw 27 q13 ∷
   rw 24 q17 ∷
   rw 23 q13 ∷
   rw 24 q14 ∷
   rw 25 q13 ∷
   rw 22 q13 ∷
   rw 23 q14 ∷
   rw 24 q13 ∷
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
   rw 15 q13 ∷
   rw 16 q14 ∷
   rw 17 q13 ∷
   rw 14 q18 ∷
   rw 15 q19 ∷
   rw 16 q18 ∷
   rw 13 q15 ∷
   rw 14 q16 ∷
   rw 15 q15 ∷
   rw 12 q13 ∷
   rw 13 q14 ∷
   rw 14 q13 ∷
   rw 11 q13 ∷
   rw 12 q14 ∷
   rw 13 q13 ∷
   rw 10 q13 ∷
   rw 11 q14 ∷
   rw 12 q13 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 11 q13 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q13 ∷
   rw 7 q13 ∷
   rw 8 q14 ∷
   rw 9 q13 ∷
   rw 6 q17 ∷
   rw 9 q20 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 7 q22 ∷
   rw⁻ 6 q21 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q23 ∷
   rw 6 q24 ∷
   rw⁻ 5 q23 ∷
   re 6 3 (ℓ "丽") ∷
   rw 6 q25 ∷
   rw 5 q21 ∷
   rw 6 q22 ∷
   rw 7 q21 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q23 ∷
   rw 9 q26 ∷
   rw 10 q23 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q27 ∷
   rw 8 q20 ∷
   rw⁻ 7 q21 ∷
   rw⁻ 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q23 ∷
   rw 5 q24 ∷
   rw⁻ 4 q23 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q25 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q21 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q23 ∷
   rw 8 q26 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q27 ∷
   rw 7 q20 ∷
   rw⁻ 6 q21 ∷
   rw⁻ 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q23 ∷
   rw 4 q28 ∷
   rw⁻ 3 q23 ∷
   re 4 3 (ℓ "乔") ∷
   rw 4 q29 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q21 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q23 ∷
   rw 7 q30 ∷
   rw 8 q23 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q27 ∷
   rw 6 q20 ∷
   rw⁻ 5 q21 ∷
   rw⁻ 4 q22 ∷
   rw⁻ 3 q21 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q23 ∷
   rw 3 q24 ∷
   rw⁻ 2 q23 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q25 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q21 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q23 ∷
   rw 6 q26 ∷
   rw 7 q23 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q27 ∷
   rw 5 q20 ∷
   rw⁻ 4 q21 ∷
   rw⁻ 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q23 ∷
   rw 2 q24 ∷
   rw⁻ 1 q23 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q25 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 3 q21 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q23 ∷
   rw 5 q26 ∷
   rw 6 q23 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q27 ∷
   rw 4 q20 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 2 q22 ∷
   rw⁻ 1 q21 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q23 ∷
   rw 1 q24 ∷
   rw⁻ 0 q23 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q25 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw 2 q21 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q23 ∷
   rw 4 q26 ∷
   rw 5 q23 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q27 ∷ []) Eq.refl
