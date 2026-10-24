{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D055 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q3 : Eqn
  q3 = wE 142 W
  q4 : Eqn
  q4 = wE 31 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 140 W
  q10 : Eqn
  q10 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q11 : Eqn
  q11 = wE 561 W
  q12 : Eqn
  q12 = wE 555 W
  q13 : Eqn
  q13 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q14 : Eqn
  q14 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q15 : Eqn
  q15 = wE 556 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q21 : Eqn
  q21 = wE 113 W
  q22 : Eqn
  q22 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q23 : Eqn
  q23 = wE 114 W
  q24 : Eqn
  q24 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q25 : Eqn
  q25 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q26 : Eqn
  q26 = wE 486 W
  q27 : Eqn
  q27 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q28 : Eqn
  q28 = wE 487 W

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且並丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶並丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両中中中乑中中乖丧丧丧丧丧丞乏乆乏丧丞乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且並丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶並丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両中中中乑中中乖丧丧丧丧丧丞乏乆乏丧丞乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q1 ∷
   rw 49 q1 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   rw 53 q1 ∷
   rw 54 q2 ∷
   rw 55 q1 ∷
   rw 56 q1 ∷
   rw 57 q1 ∷
   rw 58 q3 ∷
   rw 59 q1 ∷
   rw 60 q1 ∷
   rw 61 q4 ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q7 ∷
   rw 64 q8 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q7 ∷
   rw 63 q8 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (ℓ "丽") ∷
   rw⁻ 61 q6 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q9 ∷
   rw 57 q8 ∷
   rw 56 q8 ∷
   rw 55 q8 ∷
   rw⁻ 54 q2 ∷
   rw 53 q8 ∷
   rw 52 q8 ∷
   rw 51 q8 ∷
   rw 50 q8 ∷
   rw 49 q8 ∷
   rw 48 q8 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw⁻ 44 q10 ∷
   rw 43 q9 ∷
   rw 42 q8 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q8 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q7 ∷
   rw 35 q8 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q9 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q8 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q7 ∷
   rw 32 q8 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q7 ∷
   rw 31 q8 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q11 ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q7 ∷
   rw 32 q1 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q7 ∷
   rw 33 q1 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q7 ∷
   rw 34 q1 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q1 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q7 ∷
   rw 37 q1 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q7 ∷
   rw 38 q1 ∷
   rw 39 q7 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q7 ∷
   rw 39 q3 ∷
   rw 40 q7 ∷
   re 38 3 (ℓ "乑") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q7 ∷
   rw 40 q1 ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q7 ∷
   rw 41 q1 ∷
   rw 42 q7 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 43 q1 ∷
   rw 44 q1 ∷
   rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q3 ∷
   rw 49 q10 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   rw 53 q1 ∷
   rw 54 q1 ∷
   rw 55 q1 ∷
   rw 56 q1 ∷
   rw 57 q1 ∷
   rw 58 q1 ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   rw 61 q1 ∷
   rw 62 q1 ∷
   rw 63 q3 ∷
   rw 64 q1 ∷
   rw 65 q1 ∷
   rw 66 q4 ∷
   rw 60 q12 ∷
   rw⁻ 59 q13 ∷
   rw⁻ 60 q14 ∷
   rw⁻ 61 q13 ∷
   rw⁻ 62 q13 ∷
   rw 42 q15 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 42 q14 ∷
   rw⁻ 43 q13 ∷
   rw⁻ 44 q13 ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   rw 43 q17 ∷
   rw 42 q18 ∷
   rw 41 q17 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q19 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q19 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q19 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q19 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q19 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q19 ∷
   rw 36 q12 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q17 ∷
   rw 41 q16 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q16 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q16 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q16 ∷
   re 42 3 (ℓ "乑") ∷
   rw 45 q16 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q16 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q19 ∷
   rw 69 q20 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q16 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q16 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q21 ∷
   rw 73 q22 ∷
   rw 72 q23 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q19 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q19 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q20 ∷
   rw 68 q20 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q16 ∷
   re 70 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q16 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q21 ∷
   rw 72 q22 ∷
   rw 71 q23 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q19 ∷
   re 71 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q19 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q20 ∷
   rw 67 q24 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q16 ∷
   re 69 3 (ℓ "乑") ∷
   re 69 1 (ℓ "乏丼临丼乏") ∷
   rw 75 q16 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q21 ∷
   rw 71 q25 ∷
   rw 70 q23 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q19 ∷
   re 70 5 (ℓ "乑") ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q19 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q24 ∷
   rw 66 q20 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q16 ∷
   re 68 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q16 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q21 ∷
   rw 70 q22 ∷
   rw 69 q23 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q19 ∷
   re 69 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q19 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q20 ∷
   rw 65 q20 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q16 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q16 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q21 ∷
   rw 69 q22 ∷
   rw 68 q23 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q19 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q19 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q20 ∷
   rw 64 q20 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q16 ∷
   re 66 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q16 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q21 ∷
   rw 68 q22 ∷
   rw 67 q23 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q19 ∷
   re 67 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q19 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q20 ∷
   rw 63 q26 ∷
   rw 62 q20 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q16 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q16 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q21 ∷
   rw 66 q22 ∷
   rw 65 q23 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q19 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q19 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q20 ∷
   rw 61 q20 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q16 ∷
   re 63 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q16 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q21 ∷
   rw 65 q22 ∷
   rw 64 q23 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q19 ∷
   re 64 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q19 ∷
   re 62 3 (ℓ "乓") ∷
   rw 63 q20 ∷
   rw 60 q20 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q16 ∷
   re 62 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q16 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q21 ∷
   rw 64 q22 ∷
   rw 63 q23 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q19 ∷
   re 63 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q19 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q20 ∷
   rw 59 q20 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q16 ∷
   re 61 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q16 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q21 ∷
   rw 63 q22 ∷
   rw 62 q23 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q19 ∷
   re 62 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q19 ∷
   re 60 3 (ℓ "乓") ∷
   rw 61 q20 ∷
   rw 58 q20 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q16 ∷
   re 60 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q16 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q21 ∷
   rw 62 q22 ∷
   rw 61 q23 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q19 ∷
   re 61 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q19 ∷
   re 59 3 (ℓ "乓") ∷
   rw 60 q20 ∷
   rw 57 q20 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q16 ∷
   re 59 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q16 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q21 ∷
   rw 61 q22 ∷
   rw 60 q23 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q19 ∷
   re 60 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q19 ∷
   re 58 3 (ℓ "乓") ∷
   rw 59 q20 ∷
   rw 56 q20 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q16 ∷
   re 58 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q16 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q21 ∷
   rw 60 q22 ∷
   rw 59 q23 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q19 ∷
   re 59 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q19 ∷
   re 57 3 (ℓ "乓") ∷
   rw 58 q20 ∷
   rw 55 q20 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q16 ∷
   re 57 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q16 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q21 ∷
   rw 59 q22 ∷
   rw 58 q23 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q19 ∷
   re 58 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q19 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q20 ∷
   rw 54 q20 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q16 ∷
   re 56 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q16 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q21 ∷
   rw 58 q22 ∷
   rw 57 q23 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q19 ∷
   re 57 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q19 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q20 ∷
   rw 53 q27 ∷
   rw 54 q28 ∷
   rw 55 q27 ∷
   rw 52 q24 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q16 ∷
   re 54 3 (ℓ "乑") ∷
   re 54 1 (ℓ "乏丼临丼乏") ∷
   rw 60 q16 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q21 ∷
   rw 56 q25 ∷
   rw 55 q23 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q19 ∷
   re 55 5 (ℓ "乑") ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw 57 q19 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q24 ∷
   rw 51 q20 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q16 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q16 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q21 ∷
   rw 55 q22 ∷
   rw 54 q23 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q19 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q19 ∷ []) Eq.refl
