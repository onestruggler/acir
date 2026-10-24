{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D040 (W : Ws) where

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
  q1 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q2 : Eqn
  q2 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 3 W

-- Bar(SSKSKK;3,2->0) passes groups of WBar(SSKSKK;~3,1->0) part2: 19 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 : ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞乏丠丠临丠临临丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 = derive (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞乏丠丠临丠临临丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw⁻ 29 q1 ∷
   rw⁻ 30 q1 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 32 q1 ∷
   rw⁻ 33 q2 ∷
   rw⁻ 34 q2 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "乑") ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "乑") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q8 : Eqn
  q8 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q9 : Eqn
  q9 = wE 30 W
  q10 : Eqn
  q10 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 122 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 127 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 74 W
  q18 : Eqn
  q18 = wE 334 W
  q19 : Eqn
  q19 = wE 140 W
  q20 : Eqn
  q20 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q21 : Eqn
  q21 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q22 : Eqn
  q22 = wE 509 W
  q23 : Eqn
  q23 = wE 24 W
  q24 : Eqn
  q24 = wE 25 W
  q25 : Eqn
  q25 = wE 124 W
  q26 : Eqn
  q26 = wE 142 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF203 X3]: 171 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF203-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF203-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乤丞") (ℓ "丞乤丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q5 ∷
   rw⁻ 31 q6 ∷
   re 30 1 (ℓ "並乥並") ∷
   re 31 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 30 q7 ∷
   rw 31 q8 ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q9 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q11 ∷
   rw 36 q12 ∷
   rw 37 q11 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q7 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 37 q15 ∷
   rw⁻ 36 q7 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q11 ∷
   rw 36 q16 ∷
   rw⁻ 35 q11 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q17 ∷
   rw⁻ 33 q10 ∷
   rw 32 q17 ∷
   rw⁻ 31 q8 ∷
   rw⁻ 30 q7 ∷
   rw 31 q18 ∷
   re 31 8 (ℓ "乥") ∷
   rw⁻ 29 q6 ∷
   rw 28 q19 ∷
   rw 27 q19 ∷
   rw 26 q16 ∷
   rw 25 q19 ∷
   rw 24 q16 ∷
   rw 23 q16 ∷
   rw⁻ 22 q20 ∷
   rw 21 q16 ∷
   rw 20 q16 ∷
   rw 19 q16 ∷
   rw 18 q16 ∷
   rw 17 q16 ∷
   rw 16 q16 ∷
   rw⁻ 15 q21 ∷
   rw 14 q19 ∷
   rw 13 q16 ∷
   rw 12 q16 ∷
   rw 11 q16 ∷
   rw⁻ 10 q21 ∷
   rw 9 q19 ∷
   rw⁻ 8 q21 ∷
   rw 7 q19 ∷
   rw⁻ 6 q20 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q11 ∷
   rw 6 q19 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q11 ∷
   rw 5 q19 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q11 ∷
   rw 4 q16 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q11 ∷
   rw 3 q19 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q11 ∷
   rw 2 q16 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q11 ∷
   rw 1 q16 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q22 ∷
   rw 0 q6 ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q7 ∷
   rw 8 q13 ∷
   rw 1 q5 ∷
   rw 2 q7 ∷
   rw 3 q8 ∷
   rw 4 q23 ∷
   rw 5 q10 ∷
   rw 6 q23 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q11 ∷
   rw 8 q24 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q7 ∷
   rw 9 q25 ∷
   rw 2 q18 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q6 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw 5 q12 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q11 ∷
   rw 6 q26 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q11 ∷
   rw 8 q26 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q11 ∷
   rw 9 q26 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q20 ∷
   rw 10 q26 ∷
   rw 11 q21 ∷
   rw 12 q26 ∷
   rw 13 q21 ∷
   rw 14 q12 ∷
   rw 15 q12 ∷
   rw 16 q12 ∷
   rw 17 q26 ∷
   rw 18 q21 ∷
   rw 19 q12 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q20 ∷
   rw 26 q12 ∷
   rw 27 q12 ∷
   rw 28 q26 ∷
   rw 29 q12 ∷
   rw 30 q26 ∷
   rw 31 q26 ∷
   rw 32 q14 ∷ []) Eq.refl
