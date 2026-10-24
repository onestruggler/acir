{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D034 (W : Ws) where

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
  q1 = wE 114 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q4 : Eqn
  q4 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 113 W
  q7 : Eqn
  q7 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q8 : Eqn
  q8 = wE 486 W
  q9 : Eqn
  q9 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q10 : Eqn
  q10 = wE 487 W
  q11 : Eqn
  q11 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 488 W
  q14 : Eqn
  q14 = wE 175 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 76 W
  q19 : Eqn
  q19 = wE 137 W
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 7 W
  q22 : Eqn
  q22 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q24 : Eqn
  q24 = wE 491 W
  q25 : Eqn
  q25 = wE 29 W
  q26 : Eqn
  q26 = wE 139 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 142 W
  q29 : Eqn
  q29 = wE 31 W

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧丞乏乏丼乖临丼乏乏丞丧乄乄丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中乑並乏丶乏乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞举举举丞並") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧丞乏乏丼乖临丼乏乏丞丧乄乄丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中乑並乏丶乏乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞举举举丞並")
  (rw 81 q1 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q2 ∷
   re 81 5 (ℓ "乑") ∷
   re 81 1 (ℓ "乏乄乏") ∷
   rw 83 q2 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q3 ∷
   rw 77 q4 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q5 ∷
   re 79 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q5 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q6 ∷
   rw 81 q7 ∷
   rw 80 q1 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q2 ∷
   re 80 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q2 ∷
   re 78 3 (ℓ "乓") ∷
   rw 79 q4 ∷
   rw 76 q4 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q5 ∷
   re 78 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q5 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q6 ∷
   rw 80 q7 ∷
   rw 79 q1 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q2 ∷
   re 79 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q2 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q4 ∷
   rw 75 q8 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q5 ∷
   re 76 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q5 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q6 ∷
   rw 78 q7 ∷
   rw 77 q1 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q2 ∷
   re 77 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q2 ∷
   re 75 3 (ℓ "乓") ∷
   rw 76 q4 ∷
   rw 73 q4 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q5 ∷
   re 75 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q5 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q6 ∷
   rw 77 q7 ∷
   rw 76 q1 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q2 ∷
   re 76 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q2 ∷
   re 74 3 (ℓ "乓") ∷
   rw 75 q4 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q5 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q5 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q6 ∷
   rw 76 q7 ∷
   rw 75 q1 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q2 ∷
   re 75 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q2 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q4 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q5 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q5 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q6 ∷
   rw 75 q7 ∷
   rw 74 q1 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q2 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q2 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q4 ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q5 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q5 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q6 ∷
   rw 74 q7 ∷
   rw 73 q1 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q2 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q2 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q4 ∷
   rw 69 q4 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q5 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q6 ∷
   rw 73 q7 ∷
   rw 72 q1 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q2 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q2 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q4 ∷
   rw 68 q9 ∷
   rw 69 q10 ∷
   rw 70 q9 ∷
   rw 67 q3 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q5 ∷
   re 69 3 (ℓ "乑") ∷
   re 69 1 (ℓ "乏丼临丼乏") ∷
   rw 75 q5 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q6 ∷
   rw 71 q11 ∷
   rw 70 q1 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q2 ∷
   re 70 5 (ℓ "乑") ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q2 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q3 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q5 ∷
   re 68 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q1 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q2 ∷
   re 69 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q2 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q4 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q5 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q5 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   rw 68 q1 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q2 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q2 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q4 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q5 ∷
   re 66 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q6 ∷
   rw 68 q7 ∷
   rw 67 q1 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q2 ∷
   re 67 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q2 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q4 ∷
   rw 63 q9 ∷
   rw 64 q10 ∷
   rw 65 q9 ∷
   rw 62 q3 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q5 ∷
   re 64 3 (ℓ "乑") ∷
   re 64 1 (ℓ "乏丼临丼乏") ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q6 ∷
   rw 66 q11 ∷
   rw 65 q1 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q2 ∷
   re 65 5 (ℓ "乑") ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw 67 q2 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q3 ∷
   rw 61 q9 ∷
   rw 62 q10 ∷
   rw 63 q9 ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q5 ∷
   re 62 3 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 68 q5 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q6 ∷
   rw 64 q11 ∷
   rw 63 q1 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q2 ∷
   re 63 5 (ℓ "乑") ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw 65 q2 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q3 ∷
   rw 59 q8 ∷
   rw 62 q5 ∷
   rw 61 q12 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q2 ∷
   rw 59 q12 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q2 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q2 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q2 ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw 57 q2 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q2 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q2 ∷
   rw 54 q13 ∷
   rw 53 q14 ∷
   rw 56 q5 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q14 ∷
   rw 58 q5 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q5 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q5 ∷
   re 58 3 (ℓ "乑") ∷
   rw 61 q5 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q5 ∷
   re 60 3 (ℓ "乑") ∷
   rw 63 q5 ∷
   re 61 3 (ℓ "乑") ∷
   rw 62 q2 ∷
   rw 91 q15 ∷
   rw⁻ 90 q16 ∷
   re 89 1 (ℓ "乏丨乏") ∷
   rw⁻ 91 q17 ∷
   rw 90 q18 ∷
   rw⁻ 89 q17 ∷
   re 90 3 (ℓ "举") ∷
   re 88 1 (ℓ "乏丨乏") ∷
   rw⁻ 90 q17 ∷
   rw 89 q18 ∷
   rw⁻ 88 q17 ∷
   re 89 3 (ℓ "举") ∷
   re 87 1 (ℓ "乏久乏") ∷
   rw⁻ 89 q17 ∷
   rw 88 q19 ∷
   rw⁻ 87 q17 ∷
   re 88 3 (ℓ "乕") ∷
   re 86 1 (ℓ "乏丨乏") ∷
   rw⁻ 88 q17 ∷
   rw 87 q18 ∷
   rw⁻ 86 q17 ∷
   re 87 3 (ℓ "举") ∷
   rw⁻ 85 q16 ∷
   rw 84 q20 ∷
   rw 83 q20 ∷
   rw 82 q21 ∷
   rw 81 q20 ∷
   rw 80 q21 ∷
   rw 79 q21 ∷
   rw⁻ 78 q22 ∷
   rw 77 q21 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw 72 q21 ∷
   rw⁻ 71 q23 ∷
   rw 70 q20 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw⁻ 66 q23 ∷
   rw 65 q20 ∷
   rw⁻ 64 q23 ∷
   rw 63 q20 ∷
   rw⁻ 62 q22 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw⁻ 63 q17 ∷
   rw 62 q20 ∷
   rw⁻ 61 q17 ∷
   re 62 3 (ℓ "乔") ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw⁻ 62 q17 ∷
   rw 61 q20 ∷
   rw⁻ 60 q17 ∷
   re 61 3 (ℓ "乔") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q17 ∷
   rw 60 q21 ∷
   rw⁻ 59 q17 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw⁻ 60 q17 ∷
   rw 59 q20 ∷
   rw⁻ 58 q17 ∷
   re 59 3 (ℓ "乔") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q17 ∷
   rw 58 q21 ∷
   rw⁻ 57 q17 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q17 ∷
   rw 57 q21 ∷
   rw⁻ 56 q17 ∷
   re 57 3 (ℓ "丽") ∷
   rw 57 q24 ∷
   rw 56 q16 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q17 ∷
   rw 58 q25 ∷
   rw 59 q17 ∷
   re 57 3 (ℓ "丮") ∷
   re 59 1 (ℓ "乏么乏") ∷
   rw 58 q17 ∷
   rw 59 q26 ∷
   rw 60 q17 ∷
   re 58 3 (ℓ "乒") ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q17 ∷
   rw 60 q25 ∷
   rw 61 q17 ∷
   re 59 3 (ℓ "丮") ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q17 ∷
   rw 61 q25 ∷
   rw 62 q17 ∷
   re 60 3 (ℓ "丮") ∷
   rw 61 q16 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q17 ∷
   rw 63 q27 ∷
   rw 64 q17 ∷
   re 62 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q17 ∷
   rw 64 q27 ∷
   rw 65 q17 ∷
   re 63 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏乇乏") ∷
   rw 64 q17 ∷
   rw 65 q28 ∷
   rw 66 q17 ∷
   re 64 3 (ℓ "乑") ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q17 ∷
   rw 66 q27 ∷
   rw 67 q17 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏乇乏") ∷
   rw 66 q17 ∷
   rw 67 q28 ∷
   rw 68 q17 ∷
   re 66 3 (ℓ "乑") ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q17 ∷
   rw 68 q28 ∷
   rw 69 q17 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q22 ∷
   rw 69 q28 ∷
   rw 70 q23 ∷
   rw 71 q28 ∷
   rw 72 q23 ∷
   rw 73 q27 ∷
   rw 74 q27 ∷
   rw 75 q27 ∷
   rw 76 q28 ∷
   rw 77 q23 ∷
   rw 78 q27 ∷
   rw 79 q27 ∷
   rw 80 q27 ∷
   rw 81 q27 ∷
   rw 82 q27 ∷
   rw 83 q27 ∷
   rw 84 q22 ∷
   rw 85 q27 ∷
   rw 86 q27 ∷
   rw 87 q28 ∷
   rw 88 q27 ∷
   rw 89 q28 ∷
   rw 90 q28 ∷
   rw 91 q29 ∷
   rw 96 q15 ∷
   rw⁻ 95 q16 ∷
   re 94 1 (ℓ "乏丨乏") ∷
   rw⁻ 96 q17 ∷
   rw 95 q18 ∷
   rw⁻ 94 q17 ∷
   re 95 3 (ℓ "举") ∷
   re 93 1 (ℓ "乏丨乏") ∷
   rw⁻ 95 q17 ∷
   rw 94 q18 ∷
   rw⁻ 93 q17 ∷
   re 94 3 (ℓ "举") ∷
   re 92 1 (ℓ "乏丨乏") ∷
   rw⁻ 94 q17 ∷
   rw 93 q18 ∷
   rw⁻ 92 q17 ∷
   re 93 3 (ℓ "举") ∷
   rw⁻ 91 q16 ∷
   rw 90 q20 ∷
   rw 89 q20 ∷
   rw 88 q21 ∷
   rw 87 q20 ∷
   rw 86 q21 ∷
   rw 85 q21 ∷
   rw⁻ 84 q22 ∷
   rw 83 q21 ∷
   rw 82 q21 ∷
   rw 81 q21 ∷
   rw 80 q21 ∷
   rw 79 q21 ∷
   rw 78 q21 ∷
   rw⁻ 77 q23 ∷
   rw 76 q20 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw⁻ 72 q23 ∷
   rw 71 q20 ∷
   rw⁻ 70 q23 ∷
   rw 69 q20 ∷
   rw⁻ 68 q22 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw⁻ 69 q17 ∷
   rw 68 q20 ∷
   rw⁻ 67 q17 ∷
   re 68 3 (ℓ "乔") ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q17 ∷
   rw 67 q20 ∷
   rw⁻ 66 q17 ∷
   re 67 3 (ℓ "乔") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q17 ∷
   rw 66 q21 ∷
   rw⁻ 65 q17 ∷ []) Eq.refl
