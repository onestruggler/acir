{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D284 (W : Ws) where

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
  q1 = wE 13 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q3 : Eqn
  q3 = wE 78 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q7 : Eqn
  q7 = wE 140 W
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 799 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W

-- Bar(SSSKSS;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part2: 113 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part2 : ⟪ (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞中中中乑中中乄且乄且丧丧丧乄且丧丧乓丧丧丧丧丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ ≈ ⟪ (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part2 = derive (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞中中中乑中中乄且乄且丧丧丧乄且丧丧乓丧丧丧丧丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (re 83 1 (ℓ "丼丠丼") ∷
   rw 82 q1 ∷
   rw⁻ 83 q2 ∷
   rw 84 q3 ∷
   re 82 3 (ℓ "丧") ∷
   re 84 1 (ℓ "丼丠丼") ∷
   rw 83 q1 ∷
   rw⁻ 84 q2 ∷
   rw 85 q3 ∷
   re 83 3 (ℓ "丧") ∷
   re 85 1 (ℓ "丼丠丼") ∷
   rw 84 q1 ∷
   rw⁻ 85 q2 ∷
   rw 86 q3 ∷
   re 84 3 (ℓ "丧") ∷
   re 86 1 (ℓ "丼丠丼") ∷
   rw 85 q1 ∷
   rw⁻ 86 q2 ∷
   rw 87 q3 ∷
   re 85 3 (ℓ "丧") ∷
   rw 86 q4 ∷
   rw 85 q5 ∷
   rw 84 q5 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   rw 80 q5 ∷
   rw⁻ 79 q6 ∷
   rw 78 q7 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw⁻ 74 q6 ∷
   rw 73 q7 ∷
   rw⁻ 72 q6 ∷
   rw 71 q7 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q8 ∷
   rw 71 q5 ∷
   rw⁻ 70 q8 ∷
   re 71 3 (ℓ "丽") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q8 ∷
   rw 70 q5 ∷
   rw⁻ 69 q8 ∷
   re 70 3 (ℓ "丽") ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw⁻ 70 q8 ∷
   rw 69 q7 ∷
   rw⁻ 68 q8 ∷
   re 69 3 (ℓ "乔") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q8 ∷
   rw 68 q5 ∷
   rw⁻ 67 q8 ∷
   re 68 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q8 ∷
   rw 67 q5 ∷
   rw⁻ 66 q8 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q8 ∷
   rw 66 q5 ∷
   rw⁻ 65 q8 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   rw 66 q6 ∷
   rw 67 q10 ∷
   rw 68 q6 ∷
   rw 69 q11 ∷
   rw 70 q11 ∷
   rw 71 q11 ∷
   rw 72 q10 ∷
   rw 73 q6 ∷
   rw 74 q11 ∷
   rw 75 q11 ∷
   rw 76 q11 ∷
   rw 77 q11 ∷
   rw 78 q11 ∷
   rw 79 q11 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q8 ∷
   rw 81 q11 ∷
   rw 82 q8 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q8 ∷
   rw 83 q11 ∷
   rw 84 q8 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏乇乏") ∷
   rw 83 q8 ∷
   rw 84 q10 ∷
   rw 85 q8 ∷
   re 83 3 (ℓ "乑") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q8 ∷
   rw 85 q11 ∷
   rw 86 q8 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q8 ∷
   rw 86 q11 ∷
   rw 87 q8 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 173 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q19 : Eqn
  q19 = wE 668 W
  q20 : Eqn
  q20 = wE 175 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CX31 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX31-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乓丞") ⟫ʷ ≈ ⟪ (ℓ "丞乓丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX31-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乓丞") (ℓ "丞乓丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q13 ∷
   rw 33 q14 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q15 ∷
   rw 31 q14 ∷
   rw 30 q16 ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   rw 27 q16 ∷
   rw 26 q16 ∷
   rw 25 q16 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q15 ∷
   rw 23 q16 ∷
   rw 22 q16 ∷
   rw 21 q16 ∷
   rw 20 q16 ∷
   rw 19 q16 ∷
   rw 18 q16 ∷
   rw 17 q16 ∷
   rw 16 q16 ∷
   rw 15 q16 ∷
   rw 14 q18 ∷
   rw 13 q17 ∷
   rw 12 q16 ∷
   rw 11 q16 ∷
   rw 10 q16 ∷
   rw 9 q16 ∷
   rw 8 q16 ∷
   rw 7 q16 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q15 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q15 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q15 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q15 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q15 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q15 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q15 ∷
   rw 1 q19 ∷
   rw 0 q20 ∷
   rw 3 q13 ∷
   re 1 3 (ℓ "乓") ∷
   rw 2 q20 ∷
   rw 5 q13 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q13 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q13 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q16 ∷
   rw⁻ 13 q16 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q16 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q16 ∷
   rw⁻ 21 q16 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 23 q16 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 26 q16 ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q16 ∷
   rw⁻ 29 q16 ∷
   rw⁻ 30 q16 ∷
   rw⁻ 31 q17 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 33 q16 ∷
   rw 34 q15 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q23 : Eqn
  q23 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q24 : Eqn
  q24 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q25 : Eqn
  q25 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q26 : Eqn
  q26 = wE 869 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CSd23 CKd32 CS23 CS23 X3]: 121 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-CKd32-CS23-CS23-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊乘义义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊乘义义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-CKd32-CS23-CS23-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乊乘义义丞") (ℓ "丞乊乘义义丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 35 q4 ∷
   rw⁻ 34 q21 ∷
   rw⁻ 33 q22 ∷
   rw⁻ 32 q22 ∷
   rw⁻ 31 q23 ∷
   rw⁻ 30 q24 ∷
   rw⁻ 29 q21 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q5 ∷
   rw 25 q7 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw⁻ 22 q25 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw⁻ 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw⁻ 10 q6 ∷
   rw 9 q7 ∷
   rw⁻ 8 q6 ∷
   rw 7 q7 ∷
   rw⁻ 6 q25 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q8 ∷
   rw 6 q7 ∷
   rw⁻ 5 q8 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q8 ∷
   rw 5 q7 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q8 ∷
   rw 4 q5 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q8 ∷
   rw 3 q7 ∷
   rw⁻ 2 q8 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q8 ∷
   rw 2 q5 ∷
   rw⁻ 1 q8 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q8 ∷
   rw 1 q5 ∷
   rw⁻ 0 q8 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q26 ∷
   rw 0 q21 ∷
   rw 1 q24 ∷
   rw 2 q23 ∷
   rw 3 q22 ∷
   rw 4 q22 ∷
   rw 5 q21 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q8 ∷
   rw 7 q11 ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q8 ∷
   rw 8 q11 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q8 ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q8 ∷
   rw 10 q11 ∷
   rw 11 q8 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q8 ∷
   rw 11 q10 ∷
   rw 12 q8 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q8 ∷
   rw 12 q10 ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "乑") ∷
   rw 12 q25 ∷
   rw 13 q10 ∷
   rw 14 q6 ∷
   rw 15 q10 ∷
   rw 16 q6 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q10 ∷
   rw 21 q6 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q25 ∷
   rw 29 q11 ∷
   rw 30 q11 ∷
   rw 31 q10 ∷
   rw 32 q11 ∷
   rw 33 q10 ∷
   rw 34 q10 ∷
   rw 35 q12 ∷ []) Eq.refl
