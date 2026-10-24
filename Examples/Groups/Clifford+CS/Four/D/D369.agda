{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D369 (W : Ws) where

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
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 992 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 X3]: 123 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中丞") (ℓ "丞中丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 29 q2 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw⁻ 22 q6 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q7 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw⁻ 10 q7 ∷
   rw 9 q5 ∷
   rw⁻ 8 q7 ∷
   rw 7 q5 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q5 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q4 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q5 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q3 ∷
   rw 8 q10 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   rw 9 q10 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   rw 12 q10 ∷
   rw 13 q7 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q10 ∷
   rw 18 q7 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q6 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 76 W
  q13 : Eqn
  q13 = wE 993 W
  q14 : Eqn
  q14 = wE 29 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CSd03 X3]: 123 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd03-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丮丞") (ℓ "丞丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丨乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q12 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "举") ∷
   rw⁻ 29 q2 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw⁻ 22 q6 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q7 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw⁻ 10 q7 ∷
   rw 9 q5 ∷
   rw⁻ 8 q7 ∷
   rw 7 q5 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q5 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q4 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q5 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q13 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q3 ∷
   rw 2 q14 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q3 ∷
   rw 8 q10 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   rw 9 q10 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   rw 12 q10 ∷
   rw 13 q7 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q10 ∷
   rw 18 q7 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q6 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q9 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q11 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 994 W
  q16 : Eqn
  q16 = eqn (ℓ "丹丞") (ℓ "丞丹") (low₃-comm ((CX₀₁ ↑)) (X))
  q17 : Eqn
  q17 = wE 1 W
  q18 : Eqn
  q18 = wE 36 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q20 : Eqn
  q20 = wE 37 W
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q23 : Eqn
  q23 = wE 995 W
  q24 : Eqn
  q24 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q25 : Eqn
  q25 = wE 996 W
  q26 : Eqn
  q26 = wE 173 W
  q27 : Eqn
  q27 = wE 997 W
  q28 : Eqn
  q28 = wE 175 W
  q29 : Eqn
  q29 = wE 998 W

-- pass [CCZ123] [X3 CS03 X3]: 77 steps
lem-pass-CCZ123-vs-X3-CS03-X3 : ⟪ (ℓ "乜丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS03-X3 = derive (ℓ "乜丞中丞") (ℓ "丞中丞乜")
  (rw 0 q15 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q18 ∷
   rw⁻ 7 q19 ∷
   rw 8 q20 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q21 ∷
   re 5 5 (ℓ "中") ∷
   rw 6 q16 ∷
   rw 7 q1 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 4 q2 ∷
   rw⁻ 3 q22 ∷
   rw 4 q23 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q2 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 3 q17 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   rw⁻ 5 q19 ∷
   rw 6 q20 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q21 ∷
   re 3 5 (ℓ "中") ∷
   rw 4 q16 ∷
   rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q4 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q24 ∷
   rw 2 q25 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 3 q9 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q2 ∷
   rw 4 q24 ∷
   rw 5 q11 ∷
   rw 4 q17 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q21 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷
   rw 3 q17 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q28 ∷
   rw 5 q17 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q21 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q31 : Eqn
  q31 = wE 999 W
  q32 : Eqn
  q32 = wE 771 W
  q33 : Eqn
  q33 = wE 1000 W

-- pass [CCZ123] [X3 CK30 X3]: 77 steps
lem-pass-CCZ123-vs-X3-CK30-X3 : ⟪ (ℓ "乜丞乑丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CK30-X3 = derive (ℓ "乜丞乑丞") (ℓ "丞乑丞乜")
  (rw 0 q15 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏丼临丼乏") ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q18 ∷
   rw⁻ 7 q30 ∷
   rw 8 q20 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q21 ∷
   re 5 5 (ℓ "乑") ∷
   rw 6 q16 ∷
   rw 7 q1 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乔") ∷
   rw⁻ 4 q2 ∷
   rw⁻ 3 q22 ∷
   rw 4 q31 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q3 ∷
   rw 5 q10 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乑") ∷
   rw 5 q2 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏丼临丼乏") ∷
   rw 3 q17 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   rw⁻ 5 q30 ∷
   rw 6 q20 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q21 ∷
   re 3 5 (ℓ "乑") ∷
   rw 4 q16 ∷
   rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乔") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q24 ∷
   rw 2 q32 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q3 ∷
   rw 3 q10 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q2 ∷
   rw 4 q24 ∷
   rw 5 q11 ∷
   rw 4 q17 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q21 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw 1 q33 ∷
   rw 0 q28 ∷
   rw 3 q17 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q28 ∷
   rw 5 q17 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q21 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 96 W
  q35 : Eqn
  q35 = eqn (ℓ "両之") (ℓ "之両") (low-comm ((CS • CS • CS)) (CZ))
  q36 : Eqn
  q36 = wE 97 W

-- pass [CZ12] [CSd03]: 9 steps
lem-pass-CZ12-vs-CSd03 : ⟪ (ℓ "丸丮") ⟫ʷ ≈ ⟪ (ℓ "丮丸") ⟫ʷ
lem-pass-CZ12-vs-CSd03 = derive (ℓ "丸丮") (ℓ "丮丸")
  (re 1 1 (ℓ "乏丼両丼乏") ∷
   rw 0 q17 ∷
   re 1 3 (ℓ "丿") ∷
   rw 1 q34 ∷
   rw⁻ 2 q35 ∷
   rw 3 q36 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 6 q21 ∷
   re 0 5 (ℓ "丮") ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q38 : Eqn
  q38 = wE 137 W
  q39 : Eqn
  q39 = wE 1001 W
  q40 : Eqn
  q40 = wE 139 W
  q41 : Eqn
  q41 = wE 791 W
  q42 : Eqn
  q42 = wE 1002 W

-- pass [CCZ123] [X3 CKd30 X3]: 77 steps
lem-pass-CCZ123-vs-X3-CKd30-X3 : ⟪ (ℓ "乜丞乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乒丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd30-X3 = derive (ℓ "乜丞乒丞") (ℓ "丞乒丞乜")
  (rw 0 q15 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏丼丵丼乏") ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q18 ∷
   rw⁻ 7 q37 ∷
   rw 8 q20 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q21 ∷
   re 5 5 (ℓ "乒") ∷
   rw 6 q16 ∷
   rw 7 q1 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (ℓ "乏久乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q38 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乕") ∷
   rw⁻ 4 q2 ∷
   rw⁻ 3 q22 ∷
   rw 4 q39 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q3 ∷
   rw 5 q40 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q2 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏丼丵丼乏") ∷
   rw 3 q17 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   rw⁻ 5 q37 ∷
   rw 6 q20 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q21 ∷
   re 3 5 (ℓ "乒") ∷
   rw 4 q16 ∷
   rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q38 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乕") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q24 ∷
   rw 2 q41 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q3 ∷
   rw 3 q40 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q2 ∷
   rw 4 q24 ∷
   rw 5 q11 ∷
   rw 4 q17 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw 4 q21 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw 1 q42 ∷
   rw 0 q28 ∷
   rw 3 q17 ∷
   re 1 3 (ℓ "乒") ∷
   rw 2 q28 ∷
   rw 5 q17 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q21 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q44 : Eqn
  q44 = wE 1003 W
  q45 : Eqn
  q45 = wE 1004 W
  q46 : Eqn
  q46 = wE 1005 W

-- pass [CCZ123] [X3 CSd03 X3]: 77 steps
lem-pass-CCZ123-vs-X3-CSd03-X3 : ⟪ (ℓ "乜丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CSd03-X3 = derive (ℓ "乜丞丮丞") (ℓ "丞丮丞乜")
  (rw 0 q15 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏丼両丼乏") ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q18 ∷
   rw⁻ 7 q43 ∷
   rw 8 q20 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q21 ∷
   re 5 5 (ℓ "丮") ∷
   rw 6 q16 ∷
   rw 7 q1 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q12 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 4 q2 ∷
   rw⁻ 3 q22 ∷
   rw 4 q44 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q3 ∷
   rw 5 q14 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "丮") ∷
   rw 5 q2 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏丼両丼乏") ∷
   rw 3 q17 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q18 ∷
   rw⁻ 5 q43 ∷
   rw 6 q20 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q21 ∷
   re 3 5 (ℓ "丮") ∷
   rw 4 q16 ∷
   rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q12 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q24 ∷
   rw 2 q45 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q3 ∷
   rw 3 q14 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q2 ∷
   rw 4 q24 ∷
   rw 5 q11 ∷
   rw 4 q17 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q21 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw 1 q46 ∷
   rw 0 q28 ∷
   rw 3 q17 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q28 ∷
   rw 5 q17 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q21 ∷
   rw 3 q29 ∷ []) Eq.refl
