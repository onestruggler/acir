{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D136 (W : Ws) where

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
  q1 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q2 : Eqn
  q2 = wE 78 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 76 W
  q7 : Eqn
  q7 = wE 137 W
  q8 : Eqn
  q8 = eqn (ℓ "並丛") (ℓ "丛並") (low-comm (Swap) (((S • S • S) ↑)))
  q9 : Eqn
  q9 = wE 140 W
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = wE 690 W
  q12 : Eqn
  q12 = wE 29 W
  q13 : Eqn
  q13 = wE 139 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q18 : Eqn
  q18 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q19 : Eqn
  q19 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q20 : Eqn
  q20 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q21 : Eqn
  q21 = wE 612 W
  q22 : Eqn
  q22 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q23 : Eqn
  q23 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q24 : Eqn
  q24 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q25 : Eqn
  q25 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q26 : Eqn
  q26 = wE 613 W
  q27 : Eqn
  q27 = wE 578 W
  q28 : Eqn
  q28 = wE 580 W

-- Bar(SSKSKK;2,1->0) passes white iX via V2 conjugates 3 part3: 210 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧乄丧乄乄丮丮丮丮丮丮丛乒丮丮乏丼乖両丼乏临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part3 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丧丧乄丧乄乄丮丮丮丮丮丮丛乒丮丮乏丼乖両丼乏临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw⁻ 60 q1 ∷
   rw 61 q2 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 64 q3 ∷
   re 58 5 (ℓ "丮") ∷
   rw 59 q4 ∷
   re 58 1 (ℓ "乏丨乏") ∷
   rw⁻ 60 q5 ∷
   rw 59 q6 ∷
   rw⁻ 58 q5 ∷
   re 59 3 (ℓ "举") ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw⁻ 59 q5 ∷
   rw 58 q6 ∷
   rw⁻ 57 q5 ∷
   re 58 3 (ℓ "举") ∷
   re 56 1 (ℓ "乏丨乏") ∷
   rw⁻ 58 q5 ∷
   rw 57 q6 ∷
   rw⁻ 56 q5 ∷
   re 57 3 (ℓ "举") ∷
   re 55 1 (ℓ "乏久乏") ∷
   rw⁻ 57 q5 ∷
   rw 56 q7 ∷
   rw⁻ 55 q5 ∷
   re 56 3 (ℓ "乕") ∷
   rw⁻ 54 q8 ∷
   re 53 1 (ℓ "乏丨乏") ∷
   rw⁻ 55 q5 ∷
   rw 54 q6 ∷
   rw⁻ 53 q5 ∷
   re 54 3 (ℓ "举") ∷
   re 52 1 (ℓ "乏丨乏") ∷
   rw⁻ 54 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (ℓ "举") ∷
   re 51 1 (ℓ "乏丨乏") ∷
   rw⁻ 53 q5 ∷
   rw 52 q6 ∷
   rw⁻ 51 q5 ∷
   re 52 3 (ℓ "举") ∷
   re 50 1 (ℓ "乏丨乏") ∷
   rw⁻ 52 q5 ∷
   rw 51 q6 ∷
   rw⁻ 50 q5 ∷
   re 51 3 (ℓ "举") ∷
   re 49 1 (ℓ "乏丨乏") ∷
   rw⁻ 51 q5 ∷
   rw 50 q6 ∷
   rw⁻ 49 q5 ∷
   re 50 3 (ℓ "举") ∷
   re 48 1 (ℓ "乏丨乏") ∷
   rw⁻ 50 q5 ∷
   rw 49 q6 ∷
   rw⁻ 48 q5 ∷
   re 49 3 (ℓ "举") ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q10 ∷
   rw 44 q9 ∷
   rw 43 q10 ∷
   rw 42 q10 ∷
   rw 43 q11 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q5 ∷
   rw 43 q12 ∷
   rw 44 q5 ∷
   re 42 3 (ℓ "丮") ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q5 ∷
   rw 44 q12 ∷
   rw 45 q5 ∷
   re 43 3 (ℓ "丮") ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q5 ∷
   rw 45 q12 ∷
   rw 46 q5 ∷
   re 44 3 (ℓ "丮") ∷
   re 46 1 (ℓ "乏丷乏") ∷
   rw 45 q5 ∷
   rw 46 q12 ∷
   rw 47 q5 ∷
   re 45 3 (ℓ "丮") ∷
   re 47 1 (ℓ "乏丷乏") ∷
   rw 46 q5 ∷
   rw 47 q12 ∷
   rw 48 q5 ∷
   re 46 3 (ℓ "丮") ∷
   re 48 1 (ℓ "乏丷乏") ∷
   rw 47 q5 ∷
   rw 48 q12 ∷
   rw 49 q5 ∷
   re 47 3 (ℓ "丮") ∷
   rw 48 q8 ∷
   re 50 1 (ℓ "乏么乏") ∷
   rw 49 q5 ∷
   rw 50 q13 ∷
   rw 51 q5 ∷
   re 49 3 (ℓ "乒") ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q5 ∷
   rw 51 q12 ∷
   rw 52 q5 ∷
   re 50 3 (ℓ "丮") ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q5 ∷
   rw 52 q12 ∷
   rw 53 q5 ∷
   re 51 3 (ℓ "丮") ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q5 ∷
   rw 53 q12 ∷
   rw 54 q5 ∷
   re 52 3 (ℓ "丮") ∷
   rw 53 q14 ∷
   rw 54 q14 ∷
   rw 55 q15 ∷
   rw 56 q14 ∷
   rw 57 q15 ∷
   rw 58 q15 ∷
   rw 59 q16 ∷
   rw 81 q17 ∷
   rw 82 q18 ∷
   rw 83 q17 ∷
   rw 80 q17 ∷
   rw 81 q18 ∷
   rw 82 q17 ∷
   rw 79 q19 ∷
   rw 80 q20 ∷
   rw 81 q19 ∷
   rw 78 q17 ∷
   rw 79 q18 ∷
   rw 80 q17 ∷
   rw 77 q19 ∷
   rw 78 q20 ∷
   rw 79 q19 ∷
   rw 76 q19 ∷
   rw 77 q20 ∷
   rw 78 q19 ∷
   rw 75 q21 ∷
   rw 74 q19 ∷
   rw 75 q20 ∷
   rw 76 q19 ∷
   rw 73 q19 ∷
   rw 74 q20 ∷
   rw 75 q19 ∷
   rw 72 q19 ∷
   rw 73 q20 ∷
   rw 74 q19 ∷
   rw 71 q19 ∷
   rw 72 q20 ∷
   rw 73 q19 ∷
   rw 70 q19 ∷
   rw 71 q20 ∷
   rw 72 q19 ∷
   rw 69 q19 ∷
   rw 70 q20 ∷
   rw 71 q19 ∷
   rw 68 q22 ∷
   rw 69 q23 ∷
   rw 70 q22 ∷
   rw 67 q17 ∷
   rw 68 q18 ∷
   rw 69 q17 ∷
   rw 66 q19 ∷
   rw 67 q20 ∷
   rw 68 q19 ∷
   rw 65 q19 ∷
   rw 66 q20 ∷
   rw 67 q19 ∷
   rw 64 q19 ∷
   rw 65 q20 ∷
   rw 66 q19 ∷
   rw 63 q22 ∷
   rw 64 q23 ∷
   rw 65 q22 ∷
   rw 62 q17 ∷
   rw 63 q18 ∷
   rw 64 q17 ∷
   rw 61 q22 ∷
   rw 62 q23 ∷
   rw 63 q22 ∷
   rw 60 q17 ∷
   rw 61 q18 ∷
   rw 62 q17 ∷
   rw 59 q21 ∷
   rw 62 q4 ∷
   rw⁻ 61 q24 ∷
   rw⁻ 60 q25 ∷
   rw⁻ 59 q24 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q10 ∷
   rw 55 q9 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 54 q26 ∷
   rw 53 q24 ∷
   rw 54 q25 ∷
   rw 55 q24 ∷
   rw 56 q14 ∷
   rw 57 q14 ∷
   rw 58 q15 ∷
   rw 59 q14 ∷
   rw 60 q15 ∷
   rw 61 q15 ∷
   rw 62 q16 ∷
   rw 56 q27 ∷
   rw 62 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 581 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CKd20 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘久丘") ⟫ʷ ≈ ⟪ (ℓ "丘久丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘久丘") (ℓ "丘久丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "临乎") (ℓ "乎临") (low-comm (CK₁₀) ((S • CK₀₁)))
  q31 : Eqn
  q31 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))
  q32 : Eqn
  q32 = wE 691 W
  q33 : Eqn
  q33 = eqn (ℓ "与乎") (ℓ "乎与") (low-comm ((S ↑)) ((S • CK₀₁)))
  q34 : Eqn
  q34 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))
  q35 : Eqn
  q35 = wE 692 W
  q36 : Eqn
  q36 = wE 693 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CKd23 X2]: 131 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd23-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乎丘") ⟫ʷ ≈ ⟪ (ℓ "丘乎丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd23-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乎丘") (ℓ "丘乎丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 28 q17 ∷
   rw 29 q30 ∷
   rw 30 q17 ∷
   rw 27 q17 ∷
   rw 28 q30 ∷
   rw 29 q17 ∷
   rw 26 q19 ∷
   rw 27 q31 ∷
   rw 28 q19 ∷
   rw 25 q17 ∷
   rw 26 q30 ∷
   rw 27 q17 ∷
   rw 24 q19 ∷
   rw 25 q31 ∷
   rw 26 q19 ∷
   rw 23 q19 ∷
   rw 24 q31 ∷
   rw 25 q19 ∷
   rw 22 q32 ∷
   rw 21 q19 ∷
   rw 22 q31 ∷
   rw 23 q19 ∷
   rw 20 q19 ∷
   rw 21 q31 ∷
   rw 22 q19 ∷
   rw 19 q19 ∷
   rw 20 q31 ∷
   rw 21 q19 ∷
   rw 18 q19 ∷
   rw 19 q31 ∷
   rw 20 q19 ∷
   rw 17 q19 ∷
   rw 18 q31 ∷
   rw 19 q19 ∷
   rw 16 q19 ∷
   rw 17 q31 ∷
   rw 18 q19 ∷
   rw 15 q22 ∷
   rw 16 q33 ∷
   rw 17 q22 ∷
   rw 14 q17 ∷
   rw 15 q30 ∷
   rw 16 q17 ∷
   rw 13 q19 ∷
   rw 14 q31 ∷
   rw 15 q19 ∷
   rw 12 q19 ∷
   rw 13 q31 ∷
   rw 14 q19 ∷
   rw 11 q19 ∷
   rw 12 q31 ∷
   rw 13 q19 ∷
   rw 10 q22 ∷
   rw 11 q33 ∷
   rw 12 q22 ∷
   rw 9 q17 ∷
   rw 10 q30 ∷
   rw 11 q17 ∷
   rw 8 q22 ∷
   rw 9 q33 ∷
   rw 10 q22 ∷
   rw 7 q17 ∷
   rw 8 q30 ∷
   rw 9 q17 ∷
   rw 6 q32 ∷
   rw 9 q4 ∷
   rw⁻ 8 q24 ∷
   rw⁻ 7 q34 ∷
   rw⁻ 6 q24 ∷
   rw 5 q9 ∷
   rw 6 q35 ∷
   rw 5 q24 ∷
   rw 6 q34 ∷
   rw 7 q24 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 8 q4 ∷
   rw⁻ 7 q24 ∷
   rw⁻ 6 q34 ∷
   rw⁻ 5 q24 ∷
   rw 4 q9 ∷
   rw 5 q35 ∷
   rw 4 q24 ∷
   rw 5 q34 ∷
   rw 6 q24 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 7 q4 ∷
   rw⁻ 6 q24 ∷
   rw⁻ 5 q34 ∷
   rw⁻ 4 q24 ∷
   rw 3 q10 ∷
   rw 4 q36 ∷
   rw 3 q24 ∷
   rw 4 q34 ∷
   rw 5 q24 ∷
   rw 6 q14 ∷
   rw 7 q16 ∷
   rw 6 q4 ∷
   rw⁻ 5 q24 ∷
   rw⁻ 4 q34 ∷
   rw⁻ 3 q24 ∷
   rw 2 q9 ∷
   rw 3 q35 ∷
   rw 2 q24 ∷
   rw 3 q34 ∷
   rw 4 q24 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 5 q4 ∷
   rw⁻ 4 q24 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 2 q24 ∷
   rw 1 q10 ∷
   rw 2 q36 ∷
   rw 1 q24 ∷
   rw 2 q34 ∷
   rw 3 q24 ∷
   rw 4 q14 ∷
   rw 5 q16 ∷
   rw 4 q4 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 1 q24 ∷
   rw 0 q10 ∷
   rw 1 q36 ∷
   rw 0 q24 ∷
   rw 1 q34 ∷
   rw 2 q24 ∷
   rw 3 q14 ∷
   rw 4 q16 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 694 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CS12 CS12 CK21 CS12 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-CS12-CK21-CS12-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丶乇丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶乇丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-CS12-CK21-CS12-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丶乇丶丘") (ℓ "丘丶丶乇丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q37 ∷ []) Eq.refl
