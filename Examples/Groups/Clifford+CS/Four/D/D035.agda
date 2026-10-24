{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D035 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 493 W
  q5 : Eqn
  q5 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q6 : Eqn
  q6 = wE 29 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q10 : Eqn
  q10 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q11 : Eqn
  q11 = wE 31 W

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part5: 88 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中乑並乏丶乏乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞举举举丞並") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中乑並乏丶乏乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞举举举丞並") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏乄乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "乔") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q3 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q1 ∷
   rw 63 q3 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q1 ∷
   rw 64 q6 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "丮") ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q1 ∷
   rw 65 q6 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "丮") ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q1 ∷
   rw 66 q6 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "丮") ∷
   rw 66 q5 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q1 ∷
   rw 68 q7 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q7 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q1 ∷
   rw 70 q8 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q1 ∷
   rw 71 q7 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q1 ∷
   rw 72 q8 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乑") ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw 72 q1 ∷
   rw 73 q8 ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "乑") ∷
   rw 73 q9 ∷
   rw 74 q8 ∷
   rw 75 q10 ∷
   rw 76 q8 ∷
   rw 77 q10 ∷
   rw 78 q7 ∷
   rw 79 q7 ∷
   rw 80 q7 ∷
   rw 81 q8 ∷
   rw 82 q10 ∷
   rw 83 q7 ∷
   rw 84 q7 ∷
   rw 85 q7 ∷
   rw 86 q7 ∷
   rw 87 q7 ∷
   rw 88 q7 ∷
   rw 89 q9 ∷
   rw 90 q7 ∷
   rw 91 q7 ∷
   rw 92 q8 ∷
   rw 93 q7 ∷
   rw 94 q8 ∷
   rw 95 q8 ∷
   rw 96 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 359 W
  q15 : Eqn
  q15 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q16 : Eqn
  q16 = wE 361 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q20 : Eqn
  q20 = wE 494 W
  q21 : Eqn
  q21 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q22 : Eqn
  q22 = wE 495 W
  q23 : Eqn
  q23 = wE 173 W
  q24 : Eqn
  q24 = wE 496 W
  q25 : Eqn
  q25 = wE 175 W
  q26 : Eqn
  q26 = wE 497 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK31 X3]: 407 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乔丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乔丞") (ℓ "丞乔丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 28 q12 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q13 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q13 ∷
   re 34 3 (ℓ "乔") ∷
   rw 33 q14 ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q17 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q17 ∷
   re 29 3 (ℓ "乔") ∷
   rw 30 q12 ∷
   rw 27 q12 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q13 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q13 ∷
   re 33 3 (ℓ "乔") ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q17 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q17 ∷
   re 28 3 (ℓ "乔") ∷
   rw 29 q12 ∷
   rw 26 q18 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q13 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "乔") ∷
   rw 31 q14 ∷
   rw 30 q19 ∷
   rw 29 q16 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q17 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q17 ∷
   re 27 3 (ℓ "乔") ∷
   rw 28 q18 ∷
   rw 25 q12 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q13 ∷
   re 27 3 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "乔") ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q17 ∷
   re 28 5 (ℓ "乑") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q17 ∷
   re 26 3 (ℓ "乔") ∷
   rw 27 q12 ∷
   rw 24 q18 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q13 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "乔") ∷
   rw 29 q14 ∷
   rw 28 q19 ∷
   rw 27 q16 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q17 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q17 ∷
   re 25 3 (ℓ "乔") ∷
   rw 26 q18 ∷
   rw 23 q18 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 24 q13 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q13 ∷
   re 29 3 (ℓ "乔") ∷
   rw 28 q14 ∷
   rw 27 q19 ∷
   rw 26 q16 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q17 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q17 ∷
   re 24 3 (ℓ "乔") ∷
   rw 25 q18 ∷
   rw 22 q20 ∷
   rw 21 q18 ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q13 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "乔") ∷
   rw 26 q14 ∷
   rw 25 q19 ∷
   rw 24 q16 ∷
   re 24 1 (ℓ "乏乇乏") ∷
   rw 23 q17 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q17 ∷
   re 22 3 (ℓ "乔") ∷
   rw 23 q18 ∷
   rw 20 q18 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q13 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "乔") ∷
   rw 25 q14 ∷
   rw 24 q19 ∷
   rw 23 q16 ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q17 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q17 ∷
   re 21 3 (ℓ "乔") ∷
   rw 22 q18 ∷
   rw 19 q18 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q13 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q13 ∷
   re 25 3 (ℓ "乔") ∷
   rw 24 q14 ∷
   rw 23 q19 ∷
   rw 22 q16 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q17 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q17 ∷
   re 20 3 (ℓ "乔") ∷
   rw 21 q18 ∷
   rw 18 q18 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q13 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q13 ∷
   re 24 3 (ℓ "乔") ∷
   rw 23 q14 ∷
   rw 22 q19 ∷
   rw 21 q16 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q17 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q17 ∷
   re 19 3 (ℓ "乔") ∷
   rw 20 q18 ∷
   rw 17 q18 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q13 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "乔") ∷
   rw 22 q14 ∷
   rw 21 q19 ∷
   rw 20 q16 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q17 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q17 ∷
   re 18 3 (ℓ "乔") ∷
   rw 19 q18 ∷
   rw 16 q18 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q13 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q13 ∷
   re 22 3 (ℓ "乔") ∷
   rw 21 q14 ∷
   rw 20 q19 ∷
   rw 19 q16 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q17 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q17 ∷
   re 17 3 (ℓ "乔") ∷
   rw 18 q18 ∷
   rw 15 q21 ∷
   rw 16 q22 ∷
   rw 17 q21 ∷
   rw 14 q12 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q13 ∷
   re 16 3 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q13 ∷
   re 20 3 (ℓ "乔") ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q17 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q17 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q12 ∷
   rw 13 q18 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q13 ∷
   re 15 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q13 ∷
   re 19 3 (ℓ "乔") ∷
   rw 18 q14 ∷
   rw 17 q19 ∷
   rw 16 q16 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q17 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q17 ∷
   re 14 3 (ℓ "乔") ∷
   rw 15 q18 ∷
   rw 12 q18 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q13 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q13 ∷
   re 18 3 (ℓ "乔") ∷
   rw 17 q14 ∷
   rw 16 q19 ∷
   rw 15 q16 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q17 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q17 ∷
   re 13 3 (ℓ "乔") ∷
   rw 14 q18 ∷
   rw 11 q18 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q13 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q13 ∷
   re 17 3 (ℓ "乔") ∷
   rw 16 q14 ∷
   rw 15 q19 ∷
   rw 14 q16 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q17 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q17 ∷
   re 12 3 (ℓ "乔") ∷
   rw 13 q18 ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   rw 9 q12 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q13 ∷
   re 11 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q13 ∷
   re 15 3 (ℓ "乔") ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q17 ∷
   re 12 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q17 ∷
   re 10 3 (ℓ "乔") ∷
   rw 11 q12 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   rw 7 q12 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q13 ∷
   re 9 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q13 ∷
   re 13 3 (ℓ "乔") ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q17 ∷
   re 10 5 (ℓ "乑") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q17 ∷
   re 8 3 (ℓ "乔") ∷
   rw 9 q12 ∷
   rw 6 q20 ∷
   rw 9 q13 ∷
   rw 8 q23 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 9 q17 ∷
   rw 6 q23 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q17 ∷
   rw 6 q24 ∷
   rw 5 q25 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "乔") ∷
   rw 7 q25 ∷
   rw 10 q13 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q17 ∷
   rw 8 q13 ∷
   rw 7 q23 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 8 q17 ∷
   rw 5 q23 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q17 ∷
   rw 5 q24 ∷
   rw 4 q25 ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "乔") ∷
   rw 6 q25 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q17 ∷
   rw 7 q13 ∷
   rw 6 q23 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 7 q17 ∷
   rw 4 q23 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q17 ∷
   rw 4 q26 ∷
   rw 3 q25 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "乔") ∷
   rw 5 q25 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q17 ∷
   rw 6 q13 ∷
   rw 5 q23 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 6 q17 ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q17 ∷
   rw 3 q24 ∷
   rw 2 q25 ∷
   rw 5 q13 ∷
   re 3 3 (ℓ "乔") ∷
   rw 4 q25 ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q17 ∷
   rw 5 q13 ∷
   rw 4 q23 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 5 q17 ∷
   rw 2 q23 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q17 ∷
   rw 2 q26 ∷
   rw 1 q25 ∷
   rw 4 q13 ∷
   re 2 3 (ℓ "乔") ∷
   rw 3 q25 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q17 ∷
   rw 4 q13 ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 4 q17 ∷
   rw 1 q23 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q17 ∷
   rw 1 q26 ∷
   rw 0 q25 ∷
   rw 3 q13 ∷
   re 1 3 (ℓ "乔") ∷
   rw 2 q25 ∷
   rw 5 q13 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q17 ∷ []) Eq.refl
