{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D063 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 113 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 114 W
  q7 : Eqn
  q7 = wE 486 W
  q8 : Eqn
  q8 = wE 173 W
  q9 : Eqn
  q9 = wE 557 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = wE 568 W
  q12 : Eqn
  q12 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q13 : Eqn
  q13 = wE 569 W
  q14 : Eqn
  q14 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))

-- Bar(SSSKSS;3,2->0) passes groups of WBar(SSKSKK;~3,1->0) part2: 147 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 : ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠中中中乑中中乖丧丧丧丞乏乏乓丼丠丼乏乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 = derive (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠中中中乑中中乖丧丧丧丞乏乏乓丼丠丼乏乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丠丠临丠临临") (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q1 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q2 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q1 ∷
   re 38 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q1 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q2 ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q3 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q1 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q1 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q2 ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q3 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q1 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q2 ∷
   rw 32 q7 ∷
   rw 35 q3 ∷
   rw 34 q8 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   rw 32 q8 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q1 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q1 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q10 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "乑") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q1 ∷
   rw 54 q11 ∷
   rw⁻ 53 q5 ∷
   rw⁻ 54 q5 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 56 q5 ∷
   rw⁻ 57 q12 ∷
   rw⁻ 58 q12 ∷
   rw 36 q13 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 36 q5 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q5 ∷
   rw⁻ 39 q12 ∷
   rw⁻ 40 q12 ∷
   rw 41 q3 ∷
   rw 40 q14 ∷
   rw 39 q14 ∷
   rw 38 q15 ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q1 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q1 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   rw 30 q11 ∷
   rw⁻ 29 q15 ∷
   rw⁻ 30 q15 ∷
   rw⁻ 31 q14 ∷
   rw⁻ 32 q15 ∷
   rw⁻ 33 q14 ∷
   rw⁻ 34 q14 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "乑") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q1 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q19 : Eqn
  q19 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q20 : Eqn
  q20 = wE 30 W
  q21 : Eqn
  q21 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q22 : Eqn
  q22 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 122 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 127 W
  q27 : Eqn
  q27 = wE 7 W
  q28 : Eqn
  q28 = wE 74 W
  q29 : Eqn
  q29 = wE 334 W
  q30 : Eqn
  q30 = wE 140 W
  q31 : Eqn
  q31 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q32 : Eqn
  q32 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q33 : Eqn
  q33 = wE 553 W
  q34 : Eqn
  q34 = wE 24 W
  q35 : Eqn
  q35 = wE 25 W
  q36 : Eqn
  q36 = wE 124 W
  q37 : Eqn
  q37 = wE 142 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 TOFF203 X3]: 175 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF203-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF203-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乤丞") (ℓ "丞乤丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q16 ∷
   rw⁻ 33 q17 ∷
   re 32 1 (ℓ "並乥並") ∷
   re 33 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 32 q18 ∷
   rw 33 q19 ∷
   rw 34 q20 ∷
   rw 35 q21 ∷
   rw 36 q20 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q22 ∷
   rw 38 q23 ∷
   rw 39 q22 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q18 ∷
   rw 39 q24 ∷
   rw 40 q25 ∷
   rw 39 q26 ∷
   rw⁻ 38 q18 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q22 ∷
   rw 38 q27 ∷
   rw⁻ 37 q22 ∷
   re 38 3 (ℓ "丽") ∷
   rw 36 q28 ∷
   rw⁻ 35 q21 ∷
   rw 34 q28 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 32 q18 ∷
   rw 33 q29 ∷
   re 33 8 (ℓ "乥") ∷
   rw⁻ 31 q17 ∷
   rw 30 q27 ∷
   rw 29 q27 ∷
   rw 28 q30 ∷
   rw 27 q27 ∷
   rw 26 q27 ∷
   rw 25 q27 ∷
   rw⁻ 24 q31 ∷
   rw 23 q27 ∷
   rw 22 q27 ∷
   rw 21 q27 ∷
   rw 20 q27 ∷
   rw 19 q27 ∷
   rw 18 q27 ∷
   rw 17 q27 ∷
   rw 16 q27 ∷
   rw 15 q27 ∷
   rw⁻ 14 q32 ∷
   rw 13 q30 ∷
   rw 12 q27 ∷
   rw 11 q27 ∷
   rw 10 q27 ∷
   rw 9 q27 ∷
   rw 8 q27 ∷
   rw 7 q27 ∷
   rw⁻ 6 q31 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q22 ∷
   rw 6 q27 ∷
   rw⁻ 5 q22 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q22 ∷
   rw 5 q27 ∷
   rw⁻ 4 q22 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q22 ∷
   rw 4 q30 ∷
   rw⁻ 3 q22 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q22 ∷
   rw 3 q27 ∷
   rw⁻ 2 q22 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q22 ∷
   rw 2 q27 ∷
   rw⁻ 1 q22 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q22 ∷
   rw 1 q27 ∷
   rw⁻ 0 q22 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q33 ∷
   rw 0 q17 ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q18 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q20 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   rw 8 q22 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q18 ∷
   rw 8 q24 ∷
   rw 1 q16 ∷
   rw 2 q18 ∷
   rw 3 q19 ∷
   rw 4 q34 ∷
   rw 5 q21 ∷
   rw 6 q34 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   rw 8 q35 ∷
   rw 9 q22 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw 9 q36 ∷
   rw 2 q29 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q17 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q22 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q22 ∷
   rw 5 q23 ∷
   rw 6 q22 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q22 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q22 ∷
   rw 7 q37 ∷
   rw 8 q22 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q22 ∷
   rw 8 q23 ∷
   rw 9 q22 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q22 ∷
   rw 9 q23 ∷
   rw 10 q22 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q31 ∷
   rw 10 q23 ∷
   rw 11 q23 ∷
   rw 12 q23 ∷
   rw 13 q23 ∷
   rw 14 q23 ∷
   rw 15 q23 ∷
   rw 16 q37 ∷
   rw 17 q32 ∷
   rw 18 q23 ∷
   rw 19 q23 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q23 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q23 ∷
   rw 26 q23 ∷
   rw 27 q31 ∷
   rw 28 q23 ∷
   rw 29 q23 ∷
   rw 30 q23 ∷
   rw 31 q37 ∷
   rw 32 q23 ∷
   rw 33 q23 ∷
   rw 34 q25 ∷ []) Eq.refl
