{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D259 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q6 : Eqn
  q6 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 840 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20 X3]: 223 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 62 q1 ∷
   rw⁻ 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q4 ∷
   rw⁻ 54 q5 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw⁻ 47 q6 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw⁻ 42 q6 ∷
   rw 41 q3 ∷
   rw⁻ 40 q6 ∷
   rw 39 q3 ∷
   rw⁻ 38 q5 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q7 ∷
   rw 38 q3 ∷
   rw⁻ 37 q7 ∷
   re 38 3 (ℓ "乔") ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q7 ∷
   rw 37 q3 ∷
   rw⁻ 36 q7 ∷
   re 37 3 (ℓ "乔") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q4 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q7 ∷
   rw 35 q3 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q4 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q4 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q5 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q6 ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q5 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q7 ∷
   rw 6 q4 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q4 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q7 ∷
   rw 4 q3 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q7 ∷
   rw 3 q4 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q4 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q7 ∷
   rw 1 q4 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q7 ∷
   rw 2 q9 ∷
   rw 3 q7 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw 5 q9 ∷
   rw 6 q7 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q6 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q6 ∷
   rw 17 q9 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q5 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q7 ∷
   rw 32 q9 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q7 ∷
   rw 33 q9 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q7 ∷
   rw 34 q9 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q7 ∷
   rw 35 q10 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q9 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q7 ∷
   rw 37 q9 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q5 ∷
   rw 38 q9 ∷
   rw 39 q9 ∷
   rw 40 q9 ∷
   rw 41 q9 ∷
   rw 42 q9 ∷
   rw 43 q9 ∷
   rw 44 q10 ∷
   rw 45 q6 ∷
   rw 46 q9 ∷
   rw 47 q9 ∷
   rw 48 q9 ∷
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 51 q9 ∷
   rw 52 q9 ∷
   rw 53 q9 ∷
   rw 54 q9 ∷
   rw 55 q5 ∷
   rw 56 q9 ∷
   rw 57 q9 ∷
   rw 58 q9 ∷
   rw 59 q10 ∷
   rw 60 q9 ∷
   rw 61 q9 ∷
   rw 62 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q18 : Eqn
  q18 = wE 841 W
  q19 : Eqn
  q19 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CK30 CS03 CS03 CKd30 X3]: 97 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-CS03-CS03-CKd30-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑中中乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑中中乒丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-CS03-CS03-CKd30-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑中中乒丞") (ℓ "丞乑中中乒丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 35 q12 ∷
   rw 34 q13 ∷
   re 33 1 (ℓ "乏久乏") ∷
   rw 35 q14 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q14 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q14 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q14 ∷
   rw 29 q13 ∷
   rw 28 q15 ∷
   rw 27 q15 ∷
   rw 26 q16 ∷
   rw 25 q15 ∷
   rw 24 q16 ∷
   rw 23 q16 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q14 ∷
   rw 21 q16 ∷
   rw 20 q16 ∷
   rw 19 q16 ∷
   rw 18 q16 ∷
   rw 17 q16 ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   rw 12 q16 ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   rw 9 q15 ∷
   rw 8 q17 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q14 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q14 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q14 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q14 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q14 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q14 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q14 ∷
   rw 1 q18 ∷
   rw 0 q19 ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "乑") ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q19 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q12 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q12 ∷
   re 11 3 (ℓ "乑") ∷
   rw 14 q12 ∷
   re 12 3 (ℓ "乓") ∷
   rw⁻ 13 q15 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q16 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 23 q16 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 26 q16 ∷
   rw⁻ 27 q16 ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "乓") ∷
   rw⁻ 29 q16 ∷
   rw⁻ 30 q16 ∷
   rw⁻ 31 q15 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 33 q15 ∷
   rw⁻ 34 q15 ∷
   rw 35 q14 ∷ []) Eq.refl
