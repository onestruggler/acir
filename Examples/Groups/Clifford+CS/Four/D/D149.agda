{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D149 (W : Ws) where

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
  q2 = wE 13 W
  q3 : Eqn
  q3 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q4 : Eqn
  q4 = wE 78 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q7 : Eqn
  q7 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 76 W
  q11 : Eqn
  q11 = wE 137 W
  q12 : Eqn
  q12 = eqn (ℓ "並丛") (ℓ "丛並") (low-comm (Swap) (((S • S • S) ↑)))
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 732 W
  q16 : Eqn
  q16 = wE 29 W
  q17 : Eqn
  q17 = wE 139 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 142 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q22 : Eqn
  q22 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q23 : Eqn
  q23 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q24 : Eqn
  q24 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q25 : Eqn
  q25 = wE 612 W
  q26 : Eqn
  q26 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q27 : Eqn
  q27 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q28 : Eqn
  q28 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q29 : Eqn
  q29 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q30 : Eqn
  q30 = wE 661 W
  q31 : Eqn
  q31 = wE 733 W
  q32 : Eqn
  q32 = wE 735 W

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part3: 256 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧丧乄丧丧丮丮丮丮丮乆乏丼両丼乏丛乒丮丮丮丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧丧乄丧丧丮丮丮丮丮乆乏丼両丼乏丛乒丮丮丮丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 53 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw 56 q4 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 59 q5 ∷
   re 53 5 (ℓ "丮") ∷
   rw 54 q6 ∷
   re 56 1 (ℓ "乏丼丵丼乏") ∷
   rw 55 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 56 q2 ∷
   rw⁻ 57 q7 ∷
   rw 58 q4 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q5 ∷
   re 55 5 (ℓ "乒") ∷
   re 57 1 (ℓ "乏丼両丼乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "乓") ∷
   rw 57 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q5 ∷
   re 56 5 (ℓ "丮") ∷
   re 58 1 (ℓ "乏丼両丼乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q4 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q5 ∷
   re 57 5 (ℓ "丮") ∷
   re 59 1 (ℓ "乏丼両丼乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "乓") ∷
   rw 59 q2 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 64 q5 ∷
   re 58 5 (ℓ "丮") ∷
   rw 59 q8 ∷
   re 58 1 (ℓ "乏丨乏") ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw⁻ 58 q9 ∷
   re 59 3 (ℓ "举") ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw⁻ 59 q9 ∷
   rw 58 q10 ∷
   rw⁻ 57 q9 ∷
   re 58 3 (ℓ "举") ∷
   re 56 1 (ℓ "乏丨乏") ∷
   rw⁻ 58 q9 ∷
   rw 57 q10 ∷
   rw⁻ 56 q9 ∷
   re 57 3 (ℓ "举") ∷
   re 55 1 (ℓ "乏久乏") ∷
   rw⁻ 57 q9 ∷
   rw 56 q11 ∷
   rw⁻ 55 q9 ∷
   re 56 3 (ℓ "乕") ∷
   rw⁻ 54 q12 ∷
   re 53 1 (ℓ "乏丨乏") ∷
   rw⁻ 55 q9 ∷
   rw 54 q10 ∷
   rw⁻ 53 q9 ∷
   re 54 3 (ℓ "举") ∷
   re 52 1 (ℓ "乏丨乏") ∷
   rw⁻ 54 q9 ∷
   rw 53 q10 ∷
   rw⁻ 52 q9 ∷
   re 53 3 (ℓ "举") ∷
   re 51 1 (ℓ "乏丨乏") ∷
   rw⁻ 53 q9 ∷
   rw 52 q10 ∷
   rw⁻ 51 q9 ∷
   re 52 3 (ℓ "举") ∷
   re 50 1 (ℓ "乏丨乏") ∷
   rw⁻ 52 q9 ∷
   rw 51 q10 ∷
   rw⁻ 50 q9 ∷
   re 51 3 (ℓ "举") ∷
   re 49 1 (ℓ "乏丨乏") ∷
   rw⁻ 51 q9 ∷
   rw 50 q10 ∷
   rw⁻ 49 q9 ∷
   re 50 3 (ℓ "举") ∷
   re 48 1 (ℓ "乏丨乏") ∷
   rw⁻ 50 q9 ∷
   rw 49 q10 ∷
   rw⁻ 48 q9 ∷
   re 49 3 (ℓ "举") ∷
   rw 47 q13 ∷
   rw 46 q13 ∷
   rw 45 q14 ∷
   rw 44 q13 ∷
   rw 43 q13 ∷
   rw 42 q13 ∷
   rw 43 q15 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q9 ∷
   rw 43 q16 ∷
   rw 44 q9 ∷
   re 42 3 (ℓ "丮") ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q9 ∷
   rw 44 q16 ∷
   rw 45 q9 ∷
   re 43 3 (ℓ "丮") ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q9 ∷
   rw 45 q16 ∷
   rw 46 q9 ∷
   re 44 3 (ℓ "丮") ∷
   re 46 1 (ℓ "乏丷乏") ∷
   rw 45 q9 ∷
   rw 46 q16 ∷
   rw 47 q9 ∷
   re 45 3 (ℓ "丮") ∷
   re 47 1 (ℓ "乏丷乏") ∷
   rw 46 q9 ∷
   rw 47 q16 ∷
   rw 48 q9 ∷
   re 46 3 (ℓ "丮") ∷
   re 48 1 (ℓ "乏丷乏") ∷
   rw 47 q9 ∷
   rw 48 q16 ∷
   rw 49 q9 ∷
   re 47 3 (ℓ "丮") ∷
   rw 48 q12 ∷
   re 50 1 (ℓ "乏么乏") ∷
   rw 49 q9 ∷
   rw 50 q17 ∷
   rw 51 q9 ∷
   re 49 3 (ℓ "乒") ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q9 ∷
   rw 51 q16 ∷
   rw 52 q9 ∷
   re 50 3 (ℓ "丮") ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q9 ∷
   rw 52 q16 ∷
   rw 53 q9 ∷
   re 51 3 (ℓ "丮") ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q9 ∷
   rw 53 q16 ∷
   rw 54 q9 ∷
   re 52 3 (ℓ "丮") ∷
   rw 53 q18 ∷
   rw 54 q18 ∷
   rw 55 q18 ∷
   rw 56 q19 ∷
   rw 57 q18 ∷
   rw 58 q18 ∷
   rw 59 q20 ∷
   rw 83 q21 ∷
   rw 84 q22 ∷
   rw 85 q21 ∷
   rw 82 q21 ∷
   rw 83 q22 ∷
   rw 84 q21 ∷
   rw 81 q23 ∷
   rw 82 q24 ∷
   rw 83 q23 ∷
   rw 80 q21 ∷
   rw 81 q22 ∷
   rw 82 q21 ∷
   rw 79 q21 ∷
   rw 80 q22 ∷
   rw 81 q21 ∷
   rw 78 q21 ∷
   rw 79 q22 ∷
   rw 80 q21 ∷
   rw 77 q25 ∷
   rw 76 q21 ∷
   rw 77 q22 ∷
   rw 78 q21 ∷
   rw 75 q21 ∷
   rw 76 q22 ∷
   rw 77 q21 ∷
   rw 74 q21 ∷
   rw 75 q22 ∷
   rw 76 q21 ∷
   rw 73 q21 ∷
   rw 74 q22 ∷
   rw 75 q21 ∷
   rw 72 q21 ∷
   rw 73 q22 ∷
   rw 74 q21 ∷
   rw 71 q21 ∷
   rw 72 q22 ∷
   rw 73 q21 ∷
   rw 70 q21 ∷
   rw 71 q22 ∷
   rw 72 q21 ∷
   rw 69 q21 ∷
   rw 70 q22 ∷
   rw 71 q21 ∷
   rw 68 q21 ∷
   rw 69 q22 ∷
   rw 70 q21 ∷
   rw 67 q26 ∷
   rw 68 q27 ∷
   rw 69 q26 ∷
   rw 66 q23 ∷
   rw 67 q24 ∷
   rw 68 q23 ∷
   rw 65 q21 ∷
   rw 66 q22 ∷
   rw 67 q21 ∷
   rw 64 q21 ∷
   rw 65 q22 ∷
   rw 66 q21 ∷
   rw 63 q21 ∷
   rw 64 q22 ∷
   rw 65 q21 ∷
   rw 62 q21 ∷
   rw 63 q22 ∷
   rw 64 q21 ∷
   rw 61 q21 ∷
   rw 62 q22 ∷
   rw 63 q21 ∷
   rw 60 q21 ∷
   rw 61 q22 ∷
   rw 62 q21 ∷
   rw 59 q25 ∷
   rw 62 q8 ∷
   rw⁻ 61 q28 ∷
   rw⁻ 60 q29 ∷
   rw⁻ 59 q28 ∷
   rw 58 q13 ∷
   rw 57 q13 ∷
   rw 56 q14 ∷
   rw 55 q13 ∷
   rw 54 q13 ∷
   rw 53 q13 ∷
   rw 54 q30 ∷
   rw 53 q28 ∷
   rw 54 q29 ∷
   rw 55 q28 ∷
   rw 56 q18 ∷
   rw 57 q18 ∷
   rw 58 q18 ∷
   rw 59 q19 ∷
   rw 60 q18 ∷
   rw 61 q18 ∷
   rw 62 q20 ∷
   rw 56 q31 ∷
   rw 62 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 736 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CKd20 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘久丘") ⟫ʷ ≈ ⟪ (ℓ "丘久丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd20-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘久丘") (ℓ "丘久丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q33 ∷ []) Eq.refl
