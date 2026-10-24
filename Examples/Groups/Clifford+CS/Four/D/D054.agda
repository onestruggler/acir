{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D054 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 113 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 114 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q7 : Eqn
  q7 = wE 486 W
  q8 : Eqn
  q8 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q9 : Eqn
  q9 = wE 487 W
  q10 : Eqn
  q10 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q11 : Eqn
  q11 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 557 W
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
  q20 = wE 7 W
  q21 : Eqn
  q21 = wE 140 W
  q22 : Eqn
  q22 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q24 : Eqn
  q24 = wE 560 W
  q25 : Eqn
  q25 = wE 29 W
  q26 : Eqn
  q26 = wE 139 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 142 W

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丞乏乏丧乏乆乏丞乄丧丧丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且並丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶並丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丞乏乏丧乏乆乏丞乄丧丧丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞中中中乑中中乖丧丧丧丧丧丧乄且並丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶並丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q5 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q6 ∷
   rw 47 q6 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q2 ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q5 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q6 ∷
   rw 46 q6 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q2 ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q6 ∷
   rw 45 q7 ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q2 ∷
   rw 48 q3 ∷
   rw 47 q4 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q5 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q6 ∷
   rw 43 q6 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q1 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q2 ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q5 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 44 3 (ℓ "乓") ∷
   rw 45 q6 ∷
   rw 42 q6 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q1 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q2 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q5 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q6 ∷
   rw 41 q6 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q2 ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q5 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q5 ∷
   re 42 3 (ℓ "乓") ∷
   rw 43 q6 ∷
   rw 40 q6 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q5 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q5 ∷
   re 41 3 (ℓ "乓") ∷
   rw 42 q6 ∷
   rw 39 q6 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q2 ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q5 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q6 ∷
   rw 38 q6 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q5 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q5 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q6 ∷
   rw 37 q6 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q2 ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q6 ∷
   rw 36 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q2 ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q5 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q6 ∷
   rw 35 q8 ∷
   rw 36 q9 ∷
   rw 37 q8 ∷
   rw 34 q10 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q2 ∷
   rw 38 q11 ∷
   rw 37 q4 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q5 ∷
   re 37 5 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q5 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q10 ∷
   rw 33 q6 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q5 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q5 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q6 ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q5 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q6 ∷
   rw 31 q6 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q1 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q5 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   re 32 3 (ℓ "乓") ∷
   rw 33 q6 ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q5 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q6 ∷
   rw 29 q6 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q5 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q6 ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q5 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q6 ∷
   rw 27 q7 ∷
   rw 30 q1 ∷
   rw 29 q12 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 30 q5 ∷
   rw 27 q12 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乓") ∷
   rw 23 q14 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   rw 61 q15 ∷
   rw⁻ 60 q16 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw⁻ 61 q17 ∷
   rw 60 q18 ∷
   rw⁻ 59 q17 ∷
   re 60 3 (ℓ "举") ∷
   re 58 1 (ℓ "乏丨乏") ∷
   rw⁻ 60 q17 ∷
   rw 59 q18 ∷
   rw⁻ 58 q17 ∷
   re 59 3 (ℓ "举") ∷
   re 57 1 (ℓ "乏久乏") ∷
   rw⁻ 59 q17 ∷
   rw 58 q19 ∷
   rw⁻ 57 q17 ∷
   re 58 3 (ℓ "乕") ∷
   re 56 1 (ℓ "乏丨乏") ∷
   rw⁻ 58 q17 ∷
   rw 57 q18 ∷
   rw⁻ 56 q17 ∷
   re 57 3 (ℓ "举") ∷
   rw⁻ 55 q16 ∷
   rw 54 q20 ∷
   rw 53 q20 ∷
   rw 52 q21 ∷
   rw 51 q20 ∷
   rw 50 q20 ∷
   rw 49 q20 ∷
   rw⁻ 48 q22 ∷
   rw 47 q20 ∷
   rw 46 q20 ∷
   rw 45 q20 ∷
   rw 44 q20 ∷
   rw 43 q20 ∷
   rw 42 q20 ∷
   rw 41 q20 ∷
   rw 40 q20 ∷
   rw 39 q20 ∷
   rw⁻ 38 q23 ∷
   rw 37 q21 ∷
   rw 36 q20 ∷
   rw 35 q20 ∷
   rw 34 q20 ∷
   rw 33 q20 ∷
   rw 32 q20 ∷
   rw 31 q20 ∷
   rw⁻ 30 q22 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q17 ∷
   rw 30 q20 ∷
   rw⁻ 29 q17 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q17 ∷
   rw 29 q20 ∷
   rw⁻ 28 q17 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q17 ∷
   rw 28 q21 ∷
   rw⁻ 27 q17 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q17 ∷
   rw 27 q20 ∷
   rw⁻ 26 q17 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q17 ∷
   rw 26 q20 ∷
   rw⁻ 25 q17 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q17 ∷
   rw 25 q20 ∷
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
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q17 ∷
   rw 33 q27 ∷
   rw 34 q17 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q17 ∷
   rw 34 q28 ∷
   rw 35 q17 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q17 ∷
   rw 35 q27 ∷
   rw 36 q17 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q17 ∷
   rw 36 q27 ∷
   rw 37 q17 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q22 ∷
   rw 37 q27 ∷
   rw 38 q27 ∷
   rw 39 q27 ∷
   rw 40 q27 ∷
   rw 41 q27 ∷
   rw 42 q27 ∷
   rw 43 q28 ∷
   rw 44 q23 ∷ []) Eq.refl
