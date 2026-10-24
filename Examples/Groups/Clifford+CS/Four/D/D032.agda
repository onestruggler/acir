{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D032 (W : Ws) where

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
  q1 = wE 113 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q3 : Eqn
  q3 = wE 114 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q8 : Eqn
  q8 = wE 487 W
  q9 : Eqn
  q9 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q11 : Eqn
  q11 = wE 486 W
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
  q30 : Eqn
  q30 = wE 492 W
  q31 : Eqn
  q31 = wE 484 W
  q32 : Eqn
  q32 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q33 : Eqn
  q33 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q34 : Eqn
  q34 = wE 485 W
  q35 : Eqn
  q35 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q36 : Eqn
  q36 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丞乏乏丼丠丼乓乏乏丞丧丧丧丧乖丧丧乄丧乄乄丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵乏両両丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丞乏乏丼丠丼乓乏乏丞丧丧丧丧乖丧丧乄丧乄乄丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵乏両両丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 43 q1 ∷
   rw 42 q2 ∷
   rw 41 q3 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q4 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q4 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q5 ∷
   rw 37 q5 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q6 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   rw 40 q3 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q4 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q4 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q5 ∷
   rw 36 q7 ∷
   rw 37 q8 ∷
   rw 38 q7 ∷
   rw 35 q9 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q6 ∷
   re 37 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q6 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q1 ∷
   rw 39 q10 ∷
   rw 38 q3 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q4 ∷
   re 38 5 (ℓ "乑") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q4 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q9 ∷
   rw 34 q5 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q6 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q4 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q4 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q5 ∷
   rw 33 q5 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q6 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q4 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q4 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q5 ∷
   rw 32 q5 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q6 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q4 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q5 ∷
   rw 31 q7 ∷
   rw 32 q8 ∷
   rw 33 q7 ∷
   rw 30 q9 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q6 ∷
   re 32 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q6 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q1 ∷
   rw 34 q10 ∷
   rw 33 q3 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q4 ∷
   re 33 5 (ℓ "乑") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q4 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q9 ∷
   rw 29 q7 ∷
   rw 30 q8 ∷
   rw 31 q7 ∷
   rw 28 q9 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q6 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q6 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q1 ∷
   rw 32 q10 ∷
   rw 31 q3 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q4 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q9 ∷
   rw 27 q11 ∷
   rw 30 q6 ∷
   rw 29 q12 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 30 q4 ∷
   rw 27 q12 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏乄乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 24 q6 ∷
   re 22 3 (ℓ "乓") ∷
   rw 23 q14 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "乑") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q4 ∷
   rw 59 q15 ∷
   rw⁻ 58 q16 ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw⁻ 59 q17 ∷
   rw 58 q18 ∷
   rw⁻ 57 q17 ∷
   re 58 3 (ℓ "举") ∷
   re 56 1 (ℓ "乏丨乏") ∷
   rw⁻ 58 q17 ∷
   rw 57 q18 ∷
   rw⁻ 56 q17 ∷
   re 57 3 (ℓ "举") ∷
   re 55 1 (ℓ "乏久乏") ∷
   rw⁻ 57 q17 ∷
   rw 56 q19 ∷
   rw⁻ 55 q17 ∷
   re 56 3 (ℓ "乕") ∷
   re 54 1 (ℓ "乏丨乏") ∷
   rw⁻ 56 q17 ∷
   rw 55 q18 ∷
   rw⁻ 54 q17 ∷
   re 55 3 (ℓ "举") ∷
   rw⁻ 53 q16 ∷
   rw 52 q20 ∷
   rw 51 q20 ∷
   rw 50 q21 ∷
   rw 49 q20 ∷
   rw 48 q21 ∷
   rw 47 q21 ∷
   rw⁻ 46 q22 ∷
   rw 45 q21 ∷
   rw 44 q21 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   rw 40 q21 ∷
   rw⁻ 39 q23 ∷
   rw 38 q20 ∷
   rw 37 q21 ∷
   rw 36 q21 ∷
   rw 35 q21 ∷
   rw⁻ 34 q23 ∷
   rw 33 q20 ∷
   rw⁻ 32 q23 ∷
   rw 31 q20 ∷
   rw⁻ 30 q22 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q17 ∷
   rw 30 q20 ∷
   rw⁻ 29 q17 ∷
   re 30 3 (ℓ "乔") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q17 ∷
   rw 29 q20 ∷
   rw⁻ 28 q17 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q17 ∷
   rw 28 q21 ∷
   rw⁻ 27 q17 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q17 ∷
   rw 27 q20 ∷
   rw⁻ 26 q17 ∷
   re 27 3 (ℓ "乔") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q17 ∷
   rw 26 q21 ∷
   rw⁻ 25 q17 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q17 ∷
   rw 25 q21 ∷
   rw⁻ 24 q17 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q24 ∷
   rw 24 q16 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q17 ∷
   rw 26 q25 ∷
   rw 27 q17 ∷
   re 25 3 (ℓ "丮") ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q17 ∷
   rw 27 q26 ∷
   rw 28 q17 ∷
   re 26 3 (ℓ "乒") ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q17 ∷
   rw 28 q25 ∷
   rw 29 q17 ∷
   re 27 3 (ℓ "丮") ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q17 ∷
   rw 29 q25 ∷
   rw 30 q17 ∷
   re 28 3 (ℓ "丮") ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q17 ∷
   rw 31 q27 ∷
   rw 32 q17 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q17 ∷
   rw 32 q27 ∷
   rw 33 q17 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 32 q17 ∷
   rw 33 q28 ∷
   rw 34 q17 ∷
   re 32 3 (ℓ "乑") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q17 ∷
   rw 34 q27 ∷
   rw 35 q17 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q17 ∷
   rw 35 q28 ∷
   rw 36 q17 ∷
   re 34 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q17 ∷
   rw 36 q28 ∷
   rw 37 q17 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q22 ∷
   rw 37 q28 ∷
   rw 38 q23 ∷
   rw 39 q28 ∷
   rw 40 q23 ∷
   rw 41 q27 ∷
   rw 42 q27 ∷
   rw 43 q27 ∷
   rw 44 q28 ∷
   rw 45 q23 ∷
   rw 46 q27 ∷
   rw 47 q27 ∷
   rw 48 q27 ∷
   rw 49 q27 ∷
   rw 50 q27 ∷
   rw 51 q27 ∷
   rw 52 q22 ∷
   rw 53 q27 ∷
   rw 54 q27 ∷
   rw 55 q28 ∷
   rw 56 q27 ∷
   rw 57 q28 ∷
   rw 58 q28 ∷
   rw 59 q29 ∷
   rw 64 q15 ∷
   rw⁻ 63 q16 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q17 ∷
   rw 63 q21 ∷
   rw⁻ 62 q17 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q17 ∷
   rw 62 q21 ∷
   rw⁻ 61 q17 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q17 ∷
   rw 61 q21 ∷
   rw⁻ 60 q17 ∷
   re 61 3 (ℓ "丽") ∷
   rw⁻ 59 q16 ∷
   rw 58 q20 ∷
   rw 57 q20 ∷
   rw 56 q21 ∷
   rw 55 q20 ∷
   rw 54 q21 ∷
   rw 53 q21 ∷
   rw⁻ 52 q22 ∷
   rw 51 q21 ∷
   rw 50 q21 ∷
   rw 49 q21 ∷
   rw 48 q21 ∷
   rw 47 q21 ∷
   rw 46 q21 ∷
   rw⁻ 45 q23 ∷
   rw 44 q20 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   rw⁻ 40 q23 ∷
   rw 39 q20 ∷
   rw⁻ 38 q23 ∷
   rw 37 q20 ∷
   rw⁻ 36 q22 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q17 ∷
   rw 36 q20 ∷
   rw⁻ 35 q17 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q17 ∷
   rw 35 q20 ∷
   rw⁻ 34 q17 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q17 ∷
   rw 34 q21 ∷
   rw⁻ 33 q17 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q17 ∷
   rw 33 q20 ∷
   rw⁻ 32 q17 ∷
   re 33 3 (ℓ "乔") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q17 ∷
   rw 32 q21 ∷
   rw⁻ 31 q17 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q17 ∷
   rw 31 q21 ∷
   rw⁻ 30 q17 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q30 ∷
   rw 30 q16 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q17 ∷
   rw 32 q27 ∷
   rw 33 q17 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q17 ∷
   rw 33 q27 ∷
   rw 34 q17 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q17 ∷
   rw 34 q27 ∷
   rw 35 q17 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q16 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q17 ∷
   rw 36 q27 ∷
   rw 37 q17 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q17 ∷
   rw 37 q27 ∷
   rw 38 q17 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q17 ∷
   rw 38 q28 ∷
   rw 39 q17 ∷
   re 37 3 (ℓ "乑") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q17 ∷
   rw 39 q27 ∷
   rw 40 q17 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏乇乏") ∷
   rw 39 q17 ∷
   rw 40 q28 ∷
   rw 41 q17 ∷
   re 39 3 (ℓ "乑") ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q17 ∷
   rw 41 q28 ∷
   rw 42 q17 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q22 ∷
   rw 42 q28 ∷
   rw 43 q23 ∷
   rw 44 q28 ∷
   rw 45 q23 ∷
   rw 46 q27 ∷
   rw 47 q27 ∷
   rw 48 q27 ∷
   rw 49 q28 ∷
   rw 50 q23 ∷
   rw 51 q27 ∷
   rw 52 q27 ∷
   rw 53 q27 ∷
   rw 54 q27 ∷
   rw 55 q27 ∷
   rw 56 q27 ∷
   rw 57 q22 ∷
   rw 58 q27 ∷
   rw 59 q27 ∷
   rw 60 q28 ∷
   rw 61 q27 ∷
   rw 62 q28 ∷
   rw 63 q28 ∷
   rw 64 q29 ∷
   rw 58 q31 ∷
   rw⁻ 57 q32 ∷
   rw⁻ 58 q33 ∷
   rw⁻ 59 q32 ∷
   rw⁻ 60 q32 ∷
   rw 42 q34 ∷
   rw⁻ 41 q32 ∷
   rw⁻ 42 q33 ∷
   rw⁻ 43 q32 ∷
   rw⁻ 44 q32 ∷
   rw 45 q6 ∷
   rw 44 q35 ∷
   rw 43 q35 ∷
   rw 42 q36 ∷
   rw 41 q35 ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw 42 q4 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw 41 q4 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q4 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q4 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q4 ∷
   rw 36 q31 ∷
   rw⁻ 35 q35 ∷
   rw⁻ 36 q36 ∷ []) Eq.refl
