{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D135 (W : Ws) where

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
  q1 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q2 : Eqn
  q2 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 13 W
  q7 : Eqn
  q7 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q8 : Eqn
  q8 = wE 78 W
  q9 : Eqn
  q9 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 76 W
  q13 : Eqn
  q13 = wE 137 W
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 688 W
  q17 : Eqn
  q17 = wE 29 W
  q18 : Eqn
  q18 = wE 139 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q23 : Eqn
  q23 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q24 : Eqn
  q24 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q25 : Eqn
  q25 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q26 : Eqn
  q26 = wE 612 W
  q27 : Eqn
  q27 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q28 : Eqn
  q28 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q29 : Eqn
  q29 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q30 : Eqn
  q30 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q31 : Eqn
  q31 = wE 613 W
  q32 : Eqn
  q32 = wE 689 W
  q33 : Eqn
  q33 = wE 576 W
  q34 : Eqn
  q34 = wE 153 W
  q35 : Eqn
  q35 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q36 : Eqn
  q36 = wE 577 W

-- Bar(SSKSKK;2,1->0) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧乄丧乄乄乆丮乒丮丮临与乏临与丠丠丠临与丠丠丠丠丠丠乏乆丠丠临丠临临丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧乄丧乄乄丮丮丮丮丮丮丛乒丮丮乏丼乖両丼乏临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧乄丧乄乄乆丮乒丮丮临与乏临与丠丠丠临与丠丠丠丠丠丠乏乆丠丠临丠临临丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧乄丧乄乄丮丮丮丮丮丮丛乒丮丮乏丼乖両丼乏临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘丘丨久丨丨丘丘丨丨丨丘")
  (rw⁻ 48 q1 ∷
   rw⁻ 49 q2 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q3 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw⁻ 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q3 ∷
   rw⁻ 59 q3 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 42 1 (ℓ "乏丼両丼乏") ∷
   rw 41 q5 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q6 ∷
   rw⁻ 43 q7 ∷
   rw 44 q8 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q4 ∷
   re 41 5 (ℓ "丮") ∷
   re 43 1 (ℓ "乏丼丵丼乏") ∷
   rw 42 q5 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q6 ∷
   rw⁻ 44 q9 ∷
   rw 45 q8 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q4 ∷
   re 42 5 (ℓ "乒") ∷
   re 44 1 (ℓ "乏丼両丼乏") ∷
   rw 43 q5 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q6 ∷
   rw⁻ 45 q7 ∷
   rw 46 q8 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q4 ∷
   re 43 5 (ℓ "丮") ∷
   re 45 1 (ℓ "乏丼両丼乏") ∷
   rw 44 q5 ∷
   re 45 3 (ℓ "乓") ∷
   rw 45 q6 ∷
   rw⁻ 46 q7 ∷
   rw 47 q8 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 50 q4 ∷
   re 44 5 (ℓ "丮") ∷
   rw 45 q10 ∷
   re 44 1 (ℓ "乏丨乏") ∷
   rw⁻ 46 q11 ∷
   rw 45 q12 ∷
   rw⁻ 44 q11 ∷
   re 45 3 (ℓ "举") ∷
   re 43 1 (ℓ "乏丨乏") ∷
   rw⁻ 45 q11 ∷
   rw 44 q12 ∷
   rw⁻ 43 q11 ∷
   re 44 3 (ℓ "举") ∷
   re 42 1 (ℓ "乏久乏") ∷
   rw⁻ 44 q11 ∷
   rw 43 q13 ∷
   rw⁻ 42 q11 ∷
   re 43 3 (ℓ "乕") ∷
   re 41 1 (ℓ "乏丨乏") ∷
   rw⁻ 43 q11 ∷
   rw 42 q12 ∷
   rw⁻ 41 q11 ∷
   re 42 3 (ℓ "举") ∷
   rw 40 q14 ∷
   rw 39 q14 ∷
   rw 38 q15 ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 36 q16 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q11 ∷
   rw 36 q17 ∷
   rw 37 q11 ∷
   re 35 3 (ℓ "丮") ∷
   re 37 1 (ℓ "乏么乏") ∷
   rw 36 q11 ∷
   rw 37 q18 ∷
   rw 38 q11 ∷
   re 36 3 (ℓ "乒") ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q11 ∷
   rw 38 q17 ∷
   rw 39 q11 ∷
   re 37 3 (ℓ "丮") ∷
   re 39 1 (ℓ "乏丷乏") ∷
   rw 38 q11 ∷
   rw 39 q17 ∷
   rw 40 q11 ∷
   re 38 3 (ℓ "丮") ∷
   rw 39 q19 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q21 ∷
   rw 67 q22 ∷
   rw 68 q23 ∷
   rw 69 q22 ∷
   rw 66 q22 ∷
   rw 67 q23 ∷
   rw 68 q22 ∷
   rw 65 q24 ∷
   rw 66 q25 ∷
   rw 67 q24 ∷
   rw 64 q22 ∷
   rw 65 q23 ∷
   rw 66 q22 ∷
   rw 63 q24 ∷
   rw 64 q25 ∷
   rw 65 q24 ∷
   rw 62 q24 ∷
   rw 63 q25 ∷
   rw 64 q24 ∷
   rw 61 q26 ∷
   rw 60 q24 ∷
   rw 61 q25 ∷
   rw 62 q24 ∷
   rw 59 q24 ∷
   rw 60 q25 ∷
   rw 61 q24 ∷
   rw 58 q24 ∷
   rw 59 q25 ∷
   rw 60 q24 ∷
   rw 57 q24 ∷
   rw 58 q25 ∷
   rw 59 q24 ∷
   rw 56 q24 ∷
   rw 57 q25 ∷
   rw 58 q24 ∷
   rw 55 q24 ∷
   rw 56 q25 ∷
   rw 57 q24 ∷
   rw 54 q27 ∷
   rw 55 q28 ∷
   rw 56 q27 ∷
   rw 53 q22 ∷
   rw 54 q23 ∷
   rw 55 q22 ∷
   rw 52 q24 ∷
   rw 53 q25 ∷
   rw 54 q24 ∷
   rw 51 q24 ∷
   rw 52 q25 ∷
   rw 53 q24 ∷
   rw 50 q24 ∷
   rw 51 q25 ∷
   rw 52 q24 ∷
   rw 49 q27 ∷
   rw 50 q28 ∷
   rw 51 q27 ∷
   rw 48 q22 ∷
   rw 49 q23 ∷
   rw 50 q22 ∷
   rw 47 q27 ∷
   rw 48 q28 ∷
   rw 49 q27 ∷
   rw 46 q22 ∷
   rw 47 q23 ∷
   rw 48 q22 ∷
   rw 45 q26 ∷
   rw 48 q10 ∷
   rw⁻ 47 q29 ∷
   rw⁻ 46 q30 ∷
   rw⁻ 45 q29 ∷
   rw 44 q14 ∷
   rw 43 q14 ∷
   rw 42 q15 ∷
   rw 41 q14 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 40 q31 ∷
   rw 39 q29 ∷
   rw 40 q30 ∷
   rw 41 q29 ∷
   rw 42 q19 ∷
   rw 43 q19 ∷
   rw 44 q20 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q21 ∷
   rw 82 q5 ∷
   re 81 1 (ℓ "乏丨乏") ∷
   rw 83 q4 ∷
   re 80 1 (ℓ "乏丨乏") ∷
   rw 82 q4 ∷
   re 79 1 (ℓ "乏丨乏") ∷
   rw 81 q4 ∷
   re 78 1 (ℓ "乏久乏") ∷
   rw 80 q4 ∷
   rw 77 q32 ∷
   re 76 1 (ℓ "乏丨乏") ∷
   rw 78 q4 ∷
   re 75 1 (ℓ "乏丨乏") ∷
   rw 77 q4 ∷
   re 74 1 (ℓ "乏丨乏") ∷
   rw 76 q4 ∷
   re 73 1 (ℓ "乏丨乏") ∷
   rw 75 q4 ∷
   re 72 1 (ℓ "乏丨乏") ∷
   rw 74 q4 ∷
   re 71 1 (ℓ "乏丨乏") ∷
   rw 73 q4 ∷
   rw 70 q1 ∷
   rw 69 q1 ∷
   rw 68 q3 ∷
   rw 67 q1 ∷
   rw 66 q3 ∷
   rw 65 q3 ∷
   rw 66 q33 ∷
   rw 67 q5 ∷
   re 65 3 (ℓ "丮") ∷
   rw 68 q5 ∷
   re 66 3 (ℓ "丮") ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "丮") ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "丮") ∷
   rw 71 q5 ∷
   re 69 3 (ℓ "丮") ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "丮") ∷
   rw 71 q34 ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "乒") ∷
   rw 75 q5 ∷
   re 73 3 (ℓ "丮") ∷
   rw 76 q5 ∷
   re 74 3 (ℓ "丮") ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "丮") ∷
   rw⁻ 76 q3 ∷
   rw⁻ 77 q3 ∷
   rw⁻ 78 q1 ∷
   rw⁻ 79 q3 ∷
   rw⁻ 80 q1 ∷
   rw⁻ 81 q1 ∷
   rw 82 q4 ∷
   re 65 1 (ℓ "乏丼両丼乏") ∷
   rw 64 q5 ∷
   re 65 3 (ℓ "乓") ∷
   rw 65 q6 ∷
   rw⁻ 66 q7 ∷
   rw 67 q8 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 70 q4 ∷
   re 64 5 (ℓ "丮") ∷
   re 66 1 (ℓ "乏丼両丼乏") ∷
   rw 65 q5 ∷
   re 66 3 (ℓ "乓") ∷
   rw 66 q6 ∷
   rw⁻ 67 q7 ∷
   rw 68 q8 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 71 q4 ∷
   re 65 5 (ℓ "丮") ∷
   re 67 1 (ℓ "乏丼両丼乏") ∷
   rw 66 q5 ∷
   re 67 3 (ℓ "乓") ∷
   rw 67 q6 ∷
   rw⁻ 68 q7 ∷
   rw 69 q8 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q4 ∷
   re 66 5 (ℓ "丮") ∷
   re 68 1 (ℓ "乏丼両丼乏") ∷
   rw 67 q5 ∷
   re 68 3 (ℓ "乓") ∷
   rw 68 q6 ∷
   rw⁻ 69 q7 ∷
   rw 70 q8 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 73 q4 ∷
   re 67 5 (ℓ "丮") ∷
   re 69 1 (ℓ "乏丼両丼乏") ∷
   rw 68 q5 ∷
   re 69 3 (ℓ "乓") ∷
   rw 69 q6 ∷
   rw⁻ 70 q7 ∷
   rw 71 q8 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 74 q4 ∷
   re 68 5 (ℓ "丮") ∷
   re 70 1 (ℓ "乏丼両丼乏") ∷
   rw 69 q5 ∷
   re 70 3 (ℓ "乓") ∷
   rw 70 q6 ∷
   rw⁻ 71 q7 ∷
   rw 72 q8 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 75 q4 ∷
   re 69 5 (ℓ "丮") ∷
   rw 70 q35 ∷
   re 72 1 (ℓ "乏丼丵丼乏") ∷
   rw 71 q5 ∷
   re 72 3 (ℓ "乓") ∷
   rw 72 q6 ∷
   rw⁻ 73 q9 ∷
   rw 74 q8 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 77 q4 ∷
   re 71 5 (ℓ "乒") ∷
   re 73 1 (ℓ "乏丼両丼乏") ∷
   rw 72 q5 ∷
   re 73 3 (ℓ "乓") ∷
   rw 73 q6 ∷
   rw⁻ 74 q7 ∷
   rw 75 q8 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 78 q4 ∷
   re 72 5 (ℓ "丮") ∷
   re 74 1 (ℓ "乏丼両丼乏") ∷
   rw 73 q5 ∷
   re 74 3 (ℓ "乓") ∷
   rw 74 q6 ∷
   rw⁻ 75 q7 ∷
   rw 76 q8 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 79 q4 ∷
   re 73 5 (ℓ "丮") ∷
   re 75 1 (ℓ "乏丼両丼乏") ∷
   rw 74 q5 ∷
   re 75 3 (ℓ "乓") ∷
   rw 75 q6 ∷
   rw⁻ 76 q7 ∷
   rw 77 q8 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 80 q4 ∷
   re 74 5 (ℓ "丮") ∷
   rw 75 q5 ∷
   re 74 1 (ℓ "乏丨乏") ∷
   rw 76 q4 ∷
   re 73 1 (ℓ "乏丨乏") ∷
   rw 75 q4 ∷
   re 72 1 (ℓ "乏丨乏") ∷
   rw 74 q4 ∷
   re 71 1 (ℓ "乏久乏") ∷
   rw 73 q4 ∷
   rw 70 q32 ∷
   re 69 1 (ℓ "乏丨乏") ∷
   rw 71 q4 ∷
   re 68 1 (ℓ "乏丨乏") ∷
   rw 70 q4 ∷
   re 67 1 (ℓ "乏丨乏") ∷
   rw 69 q4 ∷
   re 66 1 (ℓ "乏丨乏") ∷
   rw 68 q4 ∷
   re 65 1 (ℓ "乏丨乏") ∷
   rw 67 q4 ∷
   re 64 1 (ℓ "乏丨乏") ∷
   rw 66 q4 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q2 ∷
   rw 56 q1 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q2 ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   rw 49 q1 ∷
   rw 50 q36 ∷
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
   rw 55 q34 ∷
   rw 58 q5 ∷
   re 56 3 (ℓ "乒") ∷
   rw 59 q5 ∷
   re 57 3 (ℓ "丮") ∷
   rw 60 q5 ∷
   re 58 3 (ℓ "丮") ∷
   rw 61 q5 ∷
   re 59 3 (ℓ "丮") ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 62 q1 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 64 q3 ∷
   rw⁻ 65 q3 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q1 ∷
   rw⁻ 68 q2 ∷
   rw⁻ 69 q3 ∷
   rw⁻ 70 q3 ∷
   rw⁻ 71 q3 ∷
   rw⁻ 72 q3 ∷
   rw⁻ 73 q3 ∷
   rw⁻ 74 q3 ∷
   rw 75 q4 ∷
   re 49 1 (ℓ "乏丼両丼乏") ∷
   rw 48 q5 ∷
   re 49 3 (ℓ "乓") ∷
   rw 49 q6 ∷
   rw⁻ 50 q7 ∷
   rw 51 q8 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 54 q4 ∷
   re 48 5 (ℓ "丮") ∷
   re 50 1 (ℓ "乏丼両丼乏") ∷
   rw 49 q5 ∷
   re 50 3 (ℓ "乓") ∷
   rw 50 q6 ∷
   rw⁻ 51 q7 ∷
   rw 52 q8 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q4 ∷
   re 49 5 (ℓ "丮") ∷
   re 51 1 (ℓ "乏丼両丼乏") ∷
   rw 50 q5 ∷
   re 51 3 (ℓ "乓") ∷
   rw 51 q6 ∷
   rw⁻ 52 q7 ∷
   rw 53 q8 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q4 ∷
   re 50 5 (ℓ "丮") ∷
   re 52 1 (ℓ "乏丼両丼乏") ∷
   rw 51 q5 ∷
   re 52 3 (ℓ "乓") ∷
   rw 52 q6 ∷
   rw⁻ 53 q7 ∷
   rw 54 q8 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 57 q4 ∷
   re 51 5 (ℓ "丮") ∷
   re 53 1 (ℓ "乏丼両丼乏") ∷
   rw 52 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 53 q6 ∷
   rw⁻ 54 q7 ∷
   rw 55 q8 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q4 ∷
   re 52 5 (ℓ "丮") ∷
   re 54 1 (ℓ "乏丼両丼乏") ∷
   rw 53 q5 ∷
   re 54 3 (ℓ "乓") ∷
   rw 54 q6 ∷
   rw⁻ 55 q7 ∷
   rw 56 q8 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 59 q4 ∷
   re 53 5 (ℓ "丮") ∷
   rw 54 q35 ∷
   re 56 1 (ℓ "乏丼丵丼乏") ∷
   rw 55 q5 ∷
   re 56 3 (ℓ "乓") ∷
   rw 56 q6 ∷
   rw⁻ 57 q9 ∷
   rw 58 q8 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q4 ∷
   re 55 5 (ℓ "乒") ∷
   re 57 1 (ℓ "乏丼両丼乏") ∷
   rw 56 q5 ∷
   re 57 3 (ℓ "乓") ∷
   rw 57 q6 ∷
   rw⁻ 58 q7 ∷
   rw 59 q8 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q4 ∷
   re 56 5 (ℓ "丮") ∷
   re 58 1 (ℓ "乏丼両丼乏") ∷
   rw 57 q5 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q6 ∷
   rw⁻ 59 q7 ∷
   rw 60 q8 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q4 ∷
   re 57 5 (ℓ "丮") ∷
   re 59 1 (ℓ "乏丼両丼乏") ∷
   rw 58 q5 ∷
   re 59 3 (ℓ "乓") ∷
   rw 59 q6 ∷ []) Eq.refl
