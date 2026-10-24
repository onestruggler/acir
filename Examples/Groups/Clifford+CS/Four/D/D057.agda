{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D057 (W : Ws) where

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
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 76 W
  q15 : Eqn
  q15 = wE 137 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q19 : Eqn
  q19 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q20 : Eqn
  q20 = wE 560 W
  q21 : Eqn
  q21 = wE 29 W
  q22 : Eqn
  q22 = wE 139 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 142 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 562 W

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part5: 414 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丞乏乏乏乆乏丼丠丼乏乏丞丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丞乏乏乏乆乏丼丠丼乏乏丞丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 66 q1 ∷
   re 67 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q1 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q2 ∷
   rw 63 q2 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q3 ∷
   re 65 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   rw 66 q6 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q1 ∷
   re 66 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q1 ∷
   re 64 3 (ℓ "乓") ∷
   rw 65 q2 ∷
   rw 62 q2 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q3 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q4 ∷
   rw 66 q5 ∷
   rw 65 q6 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q1 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q1 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q2 ∷
   rw 61 q2 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q3 ∷
   re 63 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q4 ∷
   rw 65 q5 ∷
   rw 64 q6 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q1 ∷
   re 64 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q1 ∷
   re 62 3 (ℓ "乓") ∷
   rw 63 q2 ∷
   rw 60 q2 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q3 ∷
   re 62 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q3 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q4 ∷
   rw 64 q5 ∷
   rw 63 q6 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   re 63 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q2 ∷
   rw 59 q7 ∷
   rw 62 q3 ∷
   rw 61 q8 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   rw 59 q8 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q1 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q1 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q1 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   rw 54 q9 ∷
   rw 53 q10 ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q10 ∷
   rw 58 q3 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q3 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q3 ∷
   re 59 3 (ℓ "乑") ∷
   rw 62 q3 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q3 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q1 ∷
   rw 93 q11 ∷
   rw⁻ 92 q12 ∷
   re 91 1 (ℓ "乏丨乏") ∷
   rw⁻ 93 q13 ∷
   rw 92 q14 ∷
   rw⁻ 91 q13 ∷
   re 92 3 (ℓ "举") ∷
   re 90 1 (ℓ "乏丨乏") ∷
   rw⁻ 92 q13 ∷
   rw 91 q14 ∷
   rw⁻ 90 q13 ∷
   re 91 3 (ℓ "举") ∷
   re 89 1 (ℓ "乏久乏") ∷
   rw⁻ 91 q13 ∷
   rw 90 q15 ∷
   rw⁻ 89 q13 ∷
   re 90 3 (ℓ "乕") ∷
   re 88 1 (ℓ "乏丨乏") ∷
   rw⁻ 90 q13 ∷
   rw 89 q14 ∷
   rw⁻ 88 q13 ∷
   re 89 3 (ℓ "举") ∷
   rw⁻ 87 q12 ∷
   rw 86 q16 ∷
   rw 85 q16 ∷
   rw 84 q17 ∷
   rw 83 q16 ∷
   rw 82 q16 ∷
   rw 81 q16 ∷
   rw⁻ 80 q18 ∷
   rw 79 q16 ∷
   rw 78 q16 ∷
   rw 77 q16 ∷
   rw 76 q16 ∷
   rw 75 q16 ∷
   rw 74 q16 ∷
   rw 73 q16 ∷
   rw 72 q16 ∷
   rw 71 q16 ∷
   rw⁻ 70 q19 ∷
   rw 69 q17 ∷
   rw 68 q16 ∷
   rw 67 q16 ∷
   rw 66 q16 ∷
   rw 65 q16 ∷
   rw 64 q16 ∷
   rw 63 q16 ∷
   rw⁻ 62 q18 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q13 ∷
   rw 62 q16 ∷
   rw⁻ 61 q13 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q13 ∷
   rw 61 q16 ∷
   rw⁻ 60 q13 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw⁻ 61 q13 ∷
   rw 60 q17 ∷
   rw⁻ 59 q13 ∷
   re 60 3 (ℓ "乔") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q13 ∷
   rw 59 q16 ∷
   rw⁻ 58 q13 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q13 ∷
   rw 58 q16 ∷
   rw⁻ 57 q13 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q13 ∷
   rw 57 q16 ∷
   rw⁻ 56 q13 ∷
   re 57 3 (ℓ "丽") ∷
   rw 57 q20 ∷
   rw 56 q12 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q13 ∷
   rw 58 q21 ∷
   rw 59 q13 ∷
   re 57 3 (ℓ "丮") ∷
   re 59 1 (ℓ "乏么乏") ∷
   rw 58 q13 ∷
   rw 59 q22 ∷
   rw 60 q13 ∷
   re 58 3 (ℓ "乒") ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q13 ∷
   rw 60 q21 ∷
   rw 61 q13 ∷
   re 59 3 (ℓ "丮") ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q13 ∷
   rw 61 q21 ∷
   rw 62 q13 ∷
   re 60 3 (ℓ "丮") ∷
   rw 61 q12 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q13 ∷
   rw 63 q23 ∷
   rw 64 q13 ∷
   re 62 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q13 ∷
   rw 64 q23 ∷
   rw 65 q13 ∷
   re 63 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q13 ∷
   rw 65 q23 ∷
   rw 66 q13 ∷
   re 64 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏乇乏") ∷
   rw 65 q13 ∷
   rw 66 q24 ∷
   rw 67 q13 ∷
   re 65 3 (ℓ "乑") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q13 ∷
   rw 67 q23 ∷
   rw 68 q13 ∷
   re 66 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q13 ∷
   rw 68 q23 ∷
   rw 69 q13 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q18 ∷
   rw 69 q23 ∷
   rw 70 q23 ∷
   rw 71 q23 ∷
   rw 72 q23 ∷
   rw 73 q23 ∷
   rw 74 q23 ∷
   rw 75 q24 ∷
   rw 76 q19 ∷
   rw 77 q23 ∷
   rw 78 q23 ∷
   rw 79 q23 ∷
   rw 80 q23 ∷
   rw 81 q23 ∷
   rw 82 q23 ∷
   rw 83 q23 ∷
   rw 84 q23 ∷
   rw 85 q23 ∷
   rw 86 q18 ∷
   rw 87 q23 ∷
   rw 88 q23 ∷
   rw 89 q23 ∷
   rw 90 q24 ∷
   rw 91 q23 ∷
   rw 92 q23 ∷
   rw 93 q25 ∷
   rw 98 q11 ∷
   rw⁻ 97 q12 ∷
   re 96 1 (ℓ "乏丨乏") ∷
   rw⁻ 98 q13 ∷
   rw 97 q14 ∷
   rw⁻ 96 q13 ∷
   re 97 3 (ℓ "举") ∷
   re 95 1 (ℓ "乏丨乏") ∷
   rw⁻ 97 q13 ∷
   rw 96 q14 ∷
   rw⁻ 95 q13 ∷
   re 96 3 (ℓ "举") ∷
   re 94 1 (ℓ "乏丨乏") ∷
   rw⁻ 96 q13 ∷
   rw 95 q14 ∷
   rw⁻ 94 q13 ∷
   re 95 3 (ℓ "举") ∷
   rw⁻ 93 q12 ∷
   rw 92 q16 ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   rw 89 q16 ∷
   rw 88 q16 ∷
   rw 87 q16 ∷
   rw⁻ 86 q18 ∷
   rw 85 q16 ∷
   rw 84 q16 ∷
   rw 83 q16 ∷
   rw 82 q16 ∷
   rw 81 q16 ∷
   rw 80 q16 ∷
   rw 79 q16 ∷
   rw 78 q16 ∷
   rw 77 q16 ∷
   rw⁻ 76 q19 ∷
   rw 75 q17 ∷
   rw 74 q16 ∷
   rw 73 q16 ∷
   rw 72 q16 ∷
   rw 71 q16 ∷
   rw 70 q16 ∷
   rw 69 q16 ∷
   rw⁻ 68 q18 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q13 ∷
   rw 68 q16 ∷
   rw⁻ 67 q13 ∷
   re 68 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q13 ∷
   rw 67 q16 ∷
   rw⁻ 66 q13 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw⁻ 67 q13 ∷
   rw 66 q17 ∷
   rw⁻ 65 q13 ∷
   re 66 3 (ℓ "乔") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q13 ∷
   rw 65 q16 ∷
   rw⁻ 64 q13 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q13 ∷
   rw 64 q16 ∷
   rw⁻ 63 q13 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q13 ∷
   rw 63 q16 ∷
   rw⁻ 62 q13 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q26 ∷
   rw 62 q12 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q13 ∷
   rw 64 q21 ∷
   rw 65 q13 ∷
   re 63 3 (ℓ "丮") ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q13 ∷
   rw 65 q21 ∷
   rw 66 q13 ∷
   re 64 3 (ℓ "丮") ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q13 ∷
   rw 66 q21 ∷
   rw 67 q13 ∷
   re 65 3 (ℓ "丮") ∷
   rw 66 q12 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q13 ∷
   rw 68 q23 ∷
   rw 69 q13 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q13 ∷
   rw 69 q23 ∷
   rw 70 q13 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q13 ∷
   rw 70 q23 ∷
   rw 71 q13 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q13 ∷
   rw 71 q24 ∷
   rw 72 q13 ∷
   re 70 3 (ℓ "乑") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q13 ∷
   rw 72 q23 ∷
   rw 73 q13 ∷
   re 71 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q13 ∷
   rw 73 q23 ∷
   rw 74 q13 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q18 ∷
   rw 74 q23 ∷
   rw 75 q23 ∷
   rw 76 q23 ∷
   rw 77 q23 ∷
   rw 78 q23 ∷
   rw 79 q23 ∷
   rw 80 q24 ∷
   rw 81 q19 ∷
   rw 82 q23 ∷
   rw 83 q23 ∷
   rw 84 q23 ∷
   rw 85 q23 ∷
   rw 86 q23 ∷
   rw 87 q23 ∷
   rw 88 q23 ∷
   rw 89 q23 ∷
   rw 90 q23 ∷
   rw 91 q18 ∷
   rw 92 q23 ∷
   rw 93 q23 ∷
   rw 94 q23 ∷
   rw 95 q24 ∷
   rw 96 q23 ∷
   rw 97 q23 ∷
   rw 98 q25 ∷ []) Eq.refl
