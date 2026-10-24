{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D056 (W : Ws) where

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
  q1 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 113 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q5 : Eqn
  q5 = wE 114 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 486 W
  q8 : Eqn
  q8 = wE 173 W
  q9 : Eqn
  q9 = wE 557 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = wE 558 W
  q12 : Eqn
  q12 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "丏乖") (ℓ "乖丏") (low-comm (((S • S • S) ↑)) (CX₁₀))
  q14 : Eqn
  q14 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q15 : Eqn
  q15 = wE 559 W
  q16 : Eqn
  q16 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q19 : Eqn
  q19 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q20 : Eqn
  q20 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q21 : Eqn
  q21 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q22 : Eqn
  q22 = wE 487 W

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両中中中乑中中乖丧丧丧丧丧丞乏乆乏丧丞乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丞乏乏乏乆乏丼丠丼乏乏丞丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両中中中乑中中乖丧丧丧丧丧丞乏乆乏丧丞乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丞乏乏乏乆乏丼丠丼乏乏丞丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮乒丮丮丞丞丮丮丮丞")
  (re 52 3 (ℓ "乓") ∷
   rw 53 q1 ∷
   rw 50 q1 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q2 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q6 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q6 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q1 ∷
   rw 49 q1 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q2 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q6 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q6 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q1 ∷
   rw 48 q1 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q2 ∷
   re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q6 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q6 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q1 ∷
   rw 47 q1 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q6 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q6 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q1 ∷
   rw 46 q1 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q6 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q6 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q1 ∷
   rw 45 q7 ∷
   rw 48 q2 ∷
   rw 47 q8 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q6 ∷
   rw 45 q8 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q6 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q6 ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw 44 q6 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q6 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q6 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q6 ∷
   rw 40 q9 ∷
   rw 39 q10 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q10 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "乑") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   rw 67 q11 ∷
   rw⁻ 66 q12 ∷
   rw⁻ 67 q12 ∷
   rw⁻ 68 q12 ∷
   rw⁻ 69 q12 ∷
   rw⁻ 70 q12 ∷
   rw⁻ 71 q12 ∷
   rw⁻ 72 q13 ∷
   rw⁻ 73 q14 ∷
   rw⁻ 74 q12 ∷
   rw⁻ 75 q12 ∷
   rw⁻ 76 q12 ∷
   rw 49 q15 ∷
   rw⁻ 48 q12 ∷
   rw⁻ 49 q12 ∷
   rw⁻ 50 q12 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 52 q12 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 54 q13 ∷
   rw⁻ 55 q14 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 57 q12 ∷
   rw⁻ 58 q12 ∷
   rw 59 q2 ∷
   rw 58 q16 ∷
   rw 57 q16 ∷
   rw 56 q16 ∷
   rw 55 q17 ∷
   rw 54 q18 ∷
   rw 53 q16 ∷
   rw 52 q16 ∷
   rw 51 q16 ∷
   rw 50 q16 ∷
   rw 49 q16 ∷
   rw 48 q16 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q6 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q6 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q6 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q6 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q6 ∷
   rw 43 q11 ∷
   rw⁻ 42 q16 ∷
   rw⁻ 43 q16 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 45 q16 ∷
   rw⁻ 46 q16 ∷
   rw⁻ 47 q16 ∷
   rw⁻ 48 q18 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q16 ∷
   rw⁻ 51 q16 ∷
   rw⁻ 52 q16 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乑") ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q6 ∷
   rw 83 q1 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q2 ∷
   re 85 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乓") ∷
   rw 88 q3 ∷
   rw 87 q4 ∷
   rw 86 q5 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 85 q6 ∷
   re 86 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q6 ∷
   re 84 3 (ℓ "乓") ∷
   rw 85 q1 ∷
   rw 82 q1 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q2 ∷
   re 84 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q2 ∷
   re 88 3 (ℓ "乓") ∷
   rw 87 q3 ∷
   rw 86 q4 ∷
   rw 85 q5 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q6 ∷
   re 85 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q6 ∷
   re 83 3 (ℓ "乓") ∷
   rw 84 q1 ∷
   rw 81 q19 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q2 ∷
   re 83 3 (ℓ "乑") ∷
   re 83 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q3 ∷
   rw 85 q20 ∷
   rw 84 q5 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q6 ∷
   re 84 5 (ℓ "乑") ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q6 ∷
   re 82 3 (ℓ "乓") ∷
   rw 83 q19 ∷
   rw 80 q1 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q3 ∷
   rw 84 q4 ∷
   rw 83 q5 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q6 ∷
   re 83 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q6 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q1 ∷
   rw 79 q1 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q2 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q3 ∷
   rw 83 q4 ∷
   rw 82 q5 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q6 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q6 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q1 ∷
   rw 78 q1 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q2 ∷
   re 80 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q3 ∷
   rw 82 q4 ∷
   rw 81 q5 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q6 ∷
   re 81 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q6 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q1 ∷
   rw 77 q7 ∷
   rw 76 q1 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q2 ∷
   re 78 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   rw 79 q5 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q6 ∷
   re 79 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q6 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q1 ∷
   rw 75 q1 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q2 ∷
   re 77 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "乓") ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   rw 78 q5 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q6 ∷
   re 78 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q6 ∷
   re 76 3 (ℓ "乓") ∷
   rw 77 q1 ∷
   rw 74 q1 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q2 ∷
   re 76 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q6 ∷
   re 77 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q6 ∷
   re 75 3 (ℓ "乓") ∷
   rw 76 q1 ∷
   rw 73 q1 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q2 ∷
   re 75 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 76 q5 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q6 ∷
   re 76 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q6 ∷
   re 74 3 (ℓ "乓") ∷
   rw 75 q1 ∷
   rw 72 q1 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q2 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q6 ∷
   re 75 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q6 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q1 ∷
   rw 71 q1 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q2 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   rw 74 q5 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q6 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q6 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q1 ∷
   rw 70 q1 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q2 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   rw 73 q5 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q6 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q6 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q1 ∷
   rw 69 q1 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q2 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   rw 72 q5 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q6 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q6 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q1 ∷
   rw 68 q1 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q2 ∷
   re 70 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   rw 71 q5 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q6 ∷
   re 71 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q6 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q1 ∷
   rw 67 q21 ∷
   rw 68 q22 ∷
   rw 69 q21 ∷
   rw 66 q19 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q2 ∷
   re 68 3 (ℓ "乑") ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q3 ∷
   rw 70 q20 ∷
   rw 69 q5 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q6 ∷
   re 69 5 (ℓ "乑") ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 71 q6 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q19 ∷
   rw 65 q1 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q2 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   rw 68 q5 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q6 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q6 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q1 ∷
   rw 64 q1 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q2 ∷
   re 66 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   re 67 1 (ℓ "乏乆乏") ∷ []) Eq.refl
