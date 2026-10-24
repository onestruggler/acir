{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D148 (W : Ws) where

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
  q2 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 728 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 13 W
  q8 : Eqn
  q8 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q9 : Eqn
  q9 = wE 78 W
  q10 : Eqn
  q10 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 76 W
  q14 : Eqn
  q14 = wE 137 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 729 W
  q18 : Eqn
  q18 = wE 29 W
  q19 : Eqn
  q19 = wE 139 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q24 : Eqn
  q24 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q26 : Eqn
  q26 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q27 : Eqn
  q27 = wE 612 W
  q28 : Eqn
  q28 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q29 : Eqn
  q29 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q30 : Eqn
  q30 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q31 : Eqn
  q31 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q32 : Eqn
  q32 = wE 661 W
  q33 : Eqn
  q33 = wE 689 W
  q34 : Eqn
  q34 = wE 730 W
  q35 : Eqn
  q35 = wE 153 W
  q36 : Eqn
  q36 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q37 : Eqn
  q37 = wE 731 W

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乏丨久丨丨乏乆丠丠丠临丠丠丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧丧乄丧丧丮丮丮丮丮乆乏丼両丼乏丛乒丮丮丮丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乏丨久丨丨乏乆丠丠丠临丠丠丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧丧乄丧丧丮丮丮丮丮乆乏丼両丼乏丛乒丮丮丮丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q1 ∷
   rw 55 q1 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   rw 48 q3 ∷
   rw 47 q1 ∷
   rw 46 q1 ∷
   rw 45 q1 ∷
   rw 44 q1 ∷
   rw 43 q1 ∷
   rw 42 q1 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   re 42 3 (ℓ "丮") ∷
   rw 45 q5 ∷
   re 43 3 (ℓ "乒") ∷
   rw 46 q5 ∷
   re 44 3 (ℓ "丮") ∷
   rw 47 q5 ∷
   re 45 3 (ℓ "丮") ∷
   rw⁻ 46 q1 ∷
   rw⁻ 47 q1 ∷
   rw⁻ 48 q1 ∷
   rw⁻ 49 q1 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q2 ∷
   rw⁻ 54 q1 ∷
   rw⁻ 55 q1 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q1 ∷
   rw⁻ 58 q1 ∷
   rw⁻ 59 q1 ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q1 ∷
   rw⁻ 62 q1 ∷
   rw 63 q6 ∷
   re 42 1 (ℓ "乏丼両丼乏") ∷
   rw 41 q5 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q7 ∷
   rw⁻ 43 q8 ∷
   rw 44 q9 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q6 ∷
   re 41 5 (ℓ "丮") ∷
   re 43 1 (ℓ "乏丼丵丼乏") ∷
   rw 42 q5 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q7 ∷
   rw⁻ 44 q10 ∷
   rw 45 q9 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q6 ∷
   re 42 5 (ℓ "乒") ∷
   re 44 1 (ℓ "乏丼両丼乏") ∷
   rw 43 q5 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q7 ∷
   rw⁻ 45 q8 ∷
   rw 46 q9 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q6 ∷
   re 43 5 (ℓ "丮") ∷
   re 45 1 (ℓ "乏丼両丼乏") ∷
   rw 44 q5 ∷
   re 45 3 (ℓ "乓") ∷
   rw 45 q7 ∷
   rw⁻ 46 q8 ∷
   rw 47 q9 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 50 q6 ∷
   re 44 5 (ℓ "丮") ∷
   rw 45 q11 ∷
   re 44 1 (ℓ "乏丨乏") ∷
   rw⁻ 46 q12 ∷
   rw 45 q13 ∷
   rw⁻ 44 q12 ∷
   re 45 3 (ℓ "举") ∷
   re 43 1 (ℓ "乏丨乏") ∷
   rw⁻ 45 q12 ∷
   rw 44 q13 ∷
   rw⁻ 43 q12 ∷
   re 44 3 (ℓ "举") ∷
   re 42 1 (ℓ "乏久乏") ∷
   rw⁻ 44 q12 ∷
   rw 43 q14 ∷
   rw⁻ 42 q12 ∷
   re 43 3 (ℓ "乕") ∷
   re 41 1 (ℓ "乏丨乏") ∷
   rw⁻ 43 q12 ∷
   rw 42 q13 ∷
   rw⁻ 41 q12 ∷
   re 42 3 (ℓ "举") ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q16 ∷
   rw 37 q15 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 36 q17 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q12 ∷
   rw 36 q18 ∷
   rw 37 q12 ∷
   re 35 3 (ℓ "丮") ∷
   re 37 1 (ℓ "乏么乏") ∷
   rw 36 q12 ∷
   rw 37 q19 ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "乒") ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q12 ∷
   rw 38 q18 ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "丮") ∷
   re 39 1 (ℓ "乏丷乏") ∷
   rw 38 q12 ∷
   rw 39 q18 ∷
   rw 40 q12 ∷
   re 38 3 (ℓ "丮") ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q21 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q22 ∷
   rw 69 q23 ∷
   rw 70 q24 ∷
   rw 71 q23 ∷
   rw 68 q23 ∷
   rw 69 q24 ∷
   rw 70 q23 ∷
   rw 67 q25 ∷
   rw 68 q26 ∷
   rw 69 q25 ∷
   rw 66 q23 ∷
   rw 67 q24 ∷
   rw 68 q23 ∷
   rw 65 q23 ∷
   rw 66 q24 ∷
   rw 67 q23 ∷
   rw 64 q23 ∷
   rw 65 q24 ∷
   rw 66 q23 ∷
   rw 63 q27 ∷
   rw 62 q23 ∷
   rw 63 q24 ∷
   rw 64 q23 ∷
   rw 61 q23 ∷
   rw 62 q24 ∷
   rw 63 q23 ∷
   rw 60 q23 ∷
   rw 61 q24 ∷
   rw 62 q23 ∷
   rw 59 q23 ∷
   rw 60 q24 ∷
   rw 61 q23 ∷
   rw 58 q23 ∷
   rw 59 q24 ∷
   rw 60 q23 ∷
   rw 57 q23 ∷
   rw 58 q24 ∷
   rw 59 q23 ∷
   rw 56 q23 ∷
   rw 57 q24 ∷
   rw 58 q23 ∷
   rw 55 q23 ∷
   rw 56 q24 ∷
   rw 57 q23 ∷
   rw 54 q23 ∷
   rw 55 q24 ∷
   rw 56 q23 ∷
   rw 53 q28 ∷
   rw 54 q29 ∷
   rw 55 q28 ∷
   rw 52 q25 ∷
   rw 53 q26 ∷
   rw 54 q25 ∷
   rw 51 q23 ∷
   rw 52 q24 ∷
   rw 53 q23 ∷
   rw 50 q23 ∷
   rw 51 q24 ∷
   rw 52 q23 ∷
   rw 49 q23 ∷
   rw 50 q24 ∷
   rw 51 q23 ∷
   rw 48 q23 ∷
   rw 49 q24 ∷
   rw 50 q23 ∷
   rw 47 q23 ∷
   rw 48 q24 ∷
   rw 49 q23 ∷
   rw 46 q23 ∷
   rw 47 q24 ∷
   rw 48 q23 ∷
   rw 45 q27 ∷
   rw 48 q11 ∷
   rw⁻ 47 q30 ∷
   rw⁻ 46 q31 ∷
   rw⁻ 45 q30 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q16 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 40 q32 ∷
   rw 39 q30 ∷
   rw 40 q31 ∷
   rw 41 q30 ∷
   rw 42 q20 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q21 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q22 ∷
   rw 84 q5 ∷
   re 83 1 (ℓ "乏丨乏") ∷
   rw 85 q6 ∷
   re 82 1 (ℓ "乏丨乏") ∷
   rw 84 q6 ∷
   re 81 1 (ℓ "乏丨乏") ∷
   rw 83 q6 ∷
   re 80 1 (ℓ "乏久乏") ∷
   rw 82 q6 ∷
   rw 79 q33 ∷
   re 78 1 (ℓ "乏丨乏") ∷
   rw 80 q6 ∷
   re 77 1 (ℓ "乏丨乏") ∷
   rw 79 q6 ∷
   re 76 1 (ℓ "乏丨乏") ∷
   rw 78 q6 ∷
   re 75 1 (ℓ "乏丨乏") ∷
   rw 77 q6 ∷
   re 74 1 (ℓ "乏丨乏") ∷
   rw 76 q6 ∷
   re 73 1 (ℓ "乏丨乏") ∷
   rw 75 q6 ∷
   rw 72 q1 ∷
   rw 71 q1 ∷
   rw 70 q3 ∷
   rw 69 q1 ∷
   rw 68 q1 ∷
   rw 67 q1 ∷
   rw 68 q34 ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "丮") ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "丮") ∷
   rw 71 q5 ∷
   re 69 3 (ℓ "丮") ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "丮") ∷
   rw 73 q5 ∷
   re 71 3 (ℓ "丮") ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "丮") ∷
   rw 73 q35 ∷
   rw 76 q5 ∷
   re 74 3 (ℓ "乒") ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "丮") ∷
   rw 78 q5 ∷
   re 76 3 (ℓ "丮") ∷
   rw 79 q5 ∷
   re 77 3 (ℓ "丮") ∷
   rw⁻ 78 q1 ∷
   rw⁻ 79 q1 ∷
   rw⁻ 80 q1 ∷
   rw⁻ 81 q3 ∷
   rw⁻ 82 q1 ∷
   rw⁻ 83 q1 ∷
   rw 84 q6 ∷
   re 67 1 (ℓ "乏丼両丼乏") ∷
   rw 66 q5 ∷
   re 67 3 (ℓ "乓") ∷
   rw 67 q7 ∷
   rw⁻ 68 q8 ∷
   rw 69 q9 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q6 ∷
   re 66 5 (ℓ "丮") ∷
   re 68 1 (ℓ "乏丼両丼乏") ∷
   rw 67 q5 ∷
   re 68 3 (ℓ "乓") ∷
   rw 68 q7 ∷
   rw⁻ 69 q8 ∷
   rw 70 q9 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 73 q6 ∷
   re 67 5 (ℓ "丮") ∷
   re 69 1 (ℓ "乏丼両丼乏") ∷
   rw 68 q5 ∷
   re 69 3 (ℓ "乓") ∷
   rw 69 q7 ∷
   rw⁻ 70 q8 ∷
   rw 71 q9 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 74 q6 ∷
   re 68 5 (ℓ "丮") ∷
   re 70 1 (ℓ "乏丼両丼乏") ∷
   rw 69 q5 ∷
   re 70 3 (ℓ "乓") ∷
   rw 70 q7 ∷
   rw⁻ 71 q8 ∷
   rw 72 q9 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 75 q6 ∷
   re 69 5 (ℓ "丮") ∷
   re 71 1 (ℓ "乏丼両丼乏") ∷
   rw 70 q5 ∷
   re 71 3 (ℓ "乓") ∷
   rw 71 q7 ∷
   rw⁻ 72 q8 ∷
   rw 73 q9 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 76 q6 ∷
   re 70 5 (ℓ "丮") ∷
   re 72 1 (ℓ "乏丼両丼乏") ∷
   rw 71 q5 ∷
   re 72 3 (ℓ "乓") ∷
   rw 72 q7 ∷
   rw⁻ 73 q8 ∷
   rw 74 q9 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 77 q6 ∷
   re 71 5 (ℓ "丮") ∷
   rw 72 q36 ∷
   re 74 1 (ℓ "乏丼丵丼乏") ∷
   rw 73 q5 ∷
   re 74 3 (ℓ "乓") ∷
   rw 74 q7 ∷
   rw⁻ 75 q10 ∷
   rw 76 q9 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 79 q6 ∷
   re 73 5 (ℓ "乒") ∷
   re 75 1 (ℓ "乏丼両丼乏") ∷
   rw 74 q5 ∷
   re 75 3 (ℓ "乓") ∷
   rw 75 q7 ∷
   rw⁻ 76 q8 ∷
   rw 77 q9 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 80 q6 ∷
   re 74 5 (ℓ "丮") ∷
   re 76 1 (ℓ "乏丼両丼乏") ∷
   rw 75 q5 ∷
   re 76 3 (ℓ "乓") ∷
   rw 76 q7 ∷
   rw⁻ 77 q8 ∷
   rw 78 q9 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 81 q6 ∷
   re 75 5 (ℓ "丮") ∷
   re 77 1 (ℓ "乏丼両丼乏") ∷
   rw 76 q5 ∷
   re 77 3 (ℓ "乓") ∷
   rw 77 q7 ∷
   rw⁻ 78 q8 ∷
   rw 79 q9 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 82 q6 ∷
   re 76 5 (ℓ "丮") ∷
   rw 77 q5 ∷
   re 76 1 (ℓ "乏丨乏") ∷
   rw 78 q6 ∷
   re 75 1 (ℓ "乏丨乏") ∷
   rw 77 q6 ∷
   re 74 1 (ℓ "乏丨乏") ∷
   rw 76 q6 ∷
   re 73 1 (ℓ "乏久乏") ∷
   rw 75 q6 ∷
   rw 72 q33 ∷
   re 71 1 (ℓ "乏丨乏") ∷
   rw 73 q6 ∷
   re 70 1 (ℓ "乏丨乏") ∷
   rw 72 q6 ∷
   re 69 1 (ℓ "乏丨乏") ∷
   rw 71 q6 ∷
   re 68 1 (ℓ "乏丨乏") ∷
   rw 70 q6 ∷
   re 67 1 (ℓ "乏丨乏") ∷
   rw 69 q6 ∷
   re 66 1 (ℓ "乏丨乏") ∷
   rw 68 q6 ∷
   rw 65 q1 ∷
   rw 64 q1 ∷
   rw 63 q1 ∷
   rw 62 q1 ∷
   rw 61 q1 ∷
   rw 60 q1 ∷
   rw 59 q1 ∷
   rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q1 ∷
   rw 49 q1 ∷
   rw 50 q37 ∷
   rw 51 q5 ∷
   re 49 3 (ℓ "丮") ∷
   rw 52 q5 ∷
   re 50 3 (ℓ "丮") ∷
   rw 53 q5 ∷
   re 51 3 (ℓ "丮") ∷
   rw 54 q5 ∷
   re 52 3 (ℓ "丮") ∷
   rw 55 q5 ∷
   re 53 3 (ℓ "丮") ∷
   rw 56 q5 ∷
   re 54 3 (ℓ "丮") ∷
   rw 55 q35 ∷
   rw 58 q5 ∷
   re 56 3 (ℓ "乒") ∷
   rw 59 q5 ∷
   re 57 3 (ℓ "丮") ∷
   rw 60 q5 ∷
   re 58 3 (ℓ "丮") ∷
   rw 61 q5 ∷
   re 59 3 (ℓ "丮") ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q1 ∷
   rw⁻ 62 q1 ∷
   rw⁻ 63 q1 ∷
   rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q2 ∷
   rw⁻ 68 q1 ∷
   rw⁻ 69 q1 ∷
   rw⁻ 70 q1 ∷
   rw⁻ 71 q1 ∷
   rw⁻ 72 q1 ∷
   rw⁻ 73 q1 ∷
   rw⁻ 74 q1 ∷
   rw⁻ 75 q1 ∷
   rw⁻ 76 q1 ∷
   rw 77 q6 ∷
   re 49 1 (ℓ "乏丼両丼乏") ∷
   rw 48 q5 ∷
   re 49 3 (ℓ "乓") ∷
   rw 49 q7 ∷
   rw⁻ 50 q8 ∷
   rw 51 q9 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 54 q6 ∷
   re 48 5 (ℓ "丮") ∷
   re 50 1 (ℓ "乏丼両丼乏") ∷
   rw 49 q5 ∷
   re 50 3 (ℓ "乓") ∷
   rw 50 q7 ∷
   rw⁻ 51 q8 ∷
   rw 52 q9 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q6 ∷
   re 49 5 (ℓ "丮") ∷
   re 51 1 (ℓ "乏丼両丼乏") ∷
   rw 50 q5 ∷
   re 51 3 (ℓ "乓") ∷
   rw 51 q7 ∷
   rw⁻ 52 q8 ∷
   rw 53 q9 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q6 ∷
   re 50 5 (ℓ "丮") ∷
   re 52 1 (ℓ "乏丼両丼乏") ∷
   rw 51 q5 ∷
   re 52 3 (ℓ "乓") ∷
   rw 52 q7 ∷
   rw⁻ 53 q8 ∷
   rw 54 q9 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 57 q6 ∷
   re 51 5 (ℓ "丮") ∷
   re 53 1 (ℓ "乏丼両丼乏") ∷
   rw 52 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 53 q7 ∷
   rw⁻ 54 q8 ∷
   rw 55 q9 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q6 ∷
   re 52 5 (ℓ "丮") ∷
   re 54 1 (ℓ "乏丼両丼乏") ∷ []) Eq.refl
