{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D033 (W : Ws) where

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
  q1 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q5 : Eqn
  q5 = wE 113 W
  q6 : Eqn
  q6 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q7 : Eqn
  q7 = wE 114 W
  q8 : Eqn
  q8 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = wE 486 W
  q11 : Eqn
  q11 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q12 : Eqn
  q12 = wE 487 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = wE 488 W
  q15 : Eqn
  q15 = wE 175 W
  q16 : Eqn
  q16 = wE 489 W
  q17 : Eqn
  q17 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q18 : Eqn
  q18 = eqn (ℓ "丏乖") (ℓ "乖丏") (low-comm (((S • S • S) ↑)) (CX₁₀))
  q19 : Eqn
  q19 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q20 : Eqn
  q20 = wE 490 W
  q21 : Eqn
  q21 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵乏両両丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧丞乏乏丼乖临丼乏乏丞丧乄乄丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵乏両両丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧丞乏乏丼乖临丼乏乏丞丧乄乄丞丮乒丮丮丞丞丮丮丮丞")
  (rw⁻ 37 q1 ∷
   rw⁻ 38 q1 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "乑") ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "乑") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q3 ∷
   rw 67 q4 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q2 ∷
   re 69 3 (ℓ "乑") ∷
   re 69 1 (ℓ "乏丼临丼乏") ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q3 ∷
   re 70 5 (ℓ "乑") ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q3 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q4 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q2 ∷
   re 68 3 (ℓ "乑") ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q5 ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q3 ∷
   re 69 5 (ℓ "乑") ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 71 q3 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q4 ∷
   rw 65 q8 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q2 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q5 ∷
   rw 69 q9 ∷
   rw 68 q7 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q3 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q3 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q8 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q2 ∷
   re 66 3 (ℓ "乑") ∷
   re 66 1 (ℓ "乏丼临丼乏") ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q5 ∷
   rw 68 q6 ∷
   rw 67 q7 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q3 ∷
   re 67 5 (ℓ "乑") ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw 69 q3 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q4 ∷
   rw 63 q8 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q2 ∷
   re 65 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q5 ∷
   rw 67 q9 ∷
   rw 66 q7 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q3 ∷
   re 66 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q3 ∷
   re 64 3 (ℓ "乓") ∷
   rw 65 q8 ∷
   rw 62 q8 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q2 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q5 ∷
   rw 66 q9 ∷
   rw 65 q7 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q3 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q3 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q8 ∷
   rw 61 q10 ∷
   rw 60 q8 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q2 ∷
   re 62 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q5 ∷
   rw 64 q9 ∷
   rw 63 q7 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q3 ∷
   re 63 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q3 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q8 ∷
   rw 59 q8 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q2 ∷
   re 61 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q5 ∷
   rw 63 q9 ∷
   rw 62 q7 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q3 ∷
   re 62 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q3 ∷
   re 60 3 (ℓ "乓") ∷
   rw 61 q8 ∷
   rw 58 q8 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q2 ∷
   re 60 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q5 ∷
   rw 62 q9 ∷
   rw 61 q7 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q3 ∷
   re 61 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q3 ∷
   re 59 3 (ℓ "乓") ∷
   rw 60 q8 ∷
   rw 57 q8 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q2 ∷
   re 59 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q5 ∷
   rw 61 q9 ∷
   rw 60 q7 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q3 ∷
   re 60 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q3 ∷
   re 58 3 (ℓ "乓") ∷
   rw 59 q8 ∷
   rw 56 q8 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q2 ∷
   re 58 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q5 ∷
   rw 60 q9 ∷
   rw 59 q7 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q3 ∷
   re 59 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q3 ∷
   re 57 3 (ℓ "乓") ∷
   rw 58 q8 ∷
   rw 55 q8 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q2 ∷
   re 57 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q5 ∷
   rw 59 q9 ∷
   rw 58 q7 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q3 ∷
   re 58 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q3 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q8 ∷
   rw 54 q11 ∷
   rw 55 q12 ∷
   rw 56 q11 ∷
   rw 53 q4 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q2 ∷
   re 55 3 (ℓ "乑") ∷
   re 55 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q5 ∷
   rw 57 q6 ∷
   rw 56 q7 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q3 ∷
   re 56 5 (ℓ "乑") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q3 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q4 ∷
   rw 52 q8 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q2 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q5 ∷
   rw 56 q9 ∷
   rw 55 q7 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q3 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q3 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q8 ∷
   rw 51 q8 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q2 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q5 ∷
   rw 55 q9 ∷
   rw 54 q7 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q3 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q3 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q8 ∷
   rw 50 q8 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q2 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q5 ∷
   rw 54 q9 ∷
   rw 53 q7 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q3 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q3 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q8 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q11 ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q2 ∷
   re 50 3 (ℓ "乑") ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   rw 51 q7 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q3 ∷
   re 51 5 (ℓ "乑") ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q3 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q4 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q11 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q2 ∷
   re 48 3 (ℓ "乑") ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   rw 49 q7 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q3 ∷
   re 49 5 (ℓ "乑") ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw 51 q3 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q4 ∷
   rw 45 q10 ∷
   rw 48 q2 ∷
   rw 47 q13 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q3 ∷
   rw 45 q13 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏乄乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   rw 40 q14 ∷
   rw 39 q15 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q15 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乑") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "乑") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乑") ∷
   rw 48 q3 ∷
   rw 65 q16 ∷
   rw⁻ 64 q17 ∷
   rw⁻ 65 q17 ∷
   rw⁻ 66 q17 ∷
   rw⁻ 67 q17 ∷
   rw⁻ 68 q17 ∷
   rw⁻ 69 q17 ∷
   rw⁻ 70 q18 ∷
   rw⁻ 71 q19 ∷
   rw⁻ 72 q17 ∷
   rw⁻ 73 q17 ∷
   rw⁻ 74 q17 ∷
   rw 49 q20 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q17 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 58 q17 ∷
   rw 59 q2 ∷
   rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q1 ∷
   rw 55 q21 ∷
   rw 54 q22 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q1 ∷
   rw 48 q1 ∷
   re 47 1 (ℓ "乏乄乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   rw 43 q16 ∷
   rw⁻ 42 q1 ∷
   rw⁻ 43 q1 ∷
   rw⁻ 44 q1 ∷
   rw⁻ 45 q1 ∷
   rw⁻ 46 q1 ∷
   rw⁻ 47 q1 ∷
   rw⁻ 48 q22 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q1 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乑") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "乑") ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "乑") ∷
   rw 59 q3 ∷
   rw 81 q4 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q2 ∷
   re 83 3 (ℓ "乑") ∷
   re 83 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q5 ∷
   rw 85 q6 ∷
   rw 84 q7 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q3 ∷
   re 84 5 (ℓ "乑") ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q3 ∷
   re 82 3 (ℓ "乓") ∷
   rw 83 q4 ∷
   rw 80 q4 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "乑") ∷
   re 82 1 (ℓ "乏丼临丼乏") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   rw 83 q7 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q3 ∷
   re 83 5 (ℓ "乑") ∷
   re 83 1 (ℓ "乏乄乏") ∷
   rw 85 q3 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q4 ∷
   rw 79 q8 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q2 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q5 ∷
   rw 83 q9 ∷
   rw 82 q7 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q3 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q3 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q8 ∷
   rw 78 q4 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q2 ∷
   re 80 3 (ℓ "乑") ∷
   re 80 1 (ℓ "乏丼临丼乏") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q5 ∷
   rw 82 q6 ∷ []) Eq.refl
