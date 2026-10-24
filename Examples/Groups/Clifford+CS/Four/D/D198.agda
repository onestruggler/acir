{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D198 (W : Ws) where

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
  q1 = wE 31 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 733 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 735 W

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part3: 200 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 : ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞中中中乑中乏丧乏並並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 = derive (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞中中中乑中乏丧乏並並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (re 61 3 (ℓ "中") ∷
   rw 62 q1 ∷
   rw 93 q2 ∷
   rw 92 q3 ∷
   re 91 1 (ℓ "乏丨乏") ∷
   rw 93 q4 ∷
   re 90 1 (ℓ "乏丨乏") ∷
   rw 92 q4 ∷
   re 89 1 (ℓ "乏久乏") ∷
   rw 91 q4 ∷
   re 88 1 (ℓ "乏丨乏") ∷
   rw 90 q4 ∷
   rw 87 q3 ∷
   rw 86 q5 ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 82 q4 ∷
   rw 79 q5 ∷
   rw 78 q5 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q5 ∷
   rw 70 q7 ∷
   rw 69 q6 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q5 ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 64 q4 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q4 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q4 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q4 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q4 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q4 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q4 ∷
   rw 57 q8 ∷
   rw 56 q9 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "丮") ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "乒") ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "丮") ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "丮") ∷
   rw 61 q9 ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "乑") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "乓") ∷
   rw⁻ 69 q5 ∷
   rw⁻ 70 q5 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 72 q5 ∷
   rw⁻ 73 q5 ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q7 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q5 ∷
   rw⁻ 80 q5 ∷
   rw⁻ 81 q5 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乓") ∷
   rw⁻ 87 q5 ∷
   rw⁻ 88 q5 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q6 ∷
   rw⁻ 91 q5 ∷
   rw⁻ 92 q5 ∷
   rw 93 q4 ∷
   rw 98 q2 ∷
   rw 97 q3 ∷
   re 96 1 (ℓ "乏丨乏") ∷
   rw 98 q4 ∷
   re 95 1 (ℓ "乏丨乏") ∷
   rw 97 q4 ∷
   re 94 1 (ℓ "乏丨乏") ∷
   rw 96 q4 ∷
   rw 93 q3 ∷
   rw 92 q5 ∷
   rw 91 q5 ∷
   rw 90 q6 ∷
   rw 89 q5 ∷
   rw 88 q5 ∷
   rw 87 q5 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 88 q4 ∷
   rw 85 q5 ∷
   rw 84 q5 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   rw 80 q5 ∷
   rw 79 q5 ∷
   rw 78 q5 ∷
   rw 77 q5 ∷
   rw 76 q7 ∷
   rw 75 q6 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q5 ∷
   rw 70 q5 ∷
   rw 69 q5 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 70 q4 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q4 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q4 ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw 67 q4 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q4 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q4 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q4 ∷
   rw 63 q10 ∷
   rw 62 q9 ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "丮") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "丮") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "丮") ∷
   rw 66 q9 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "乑") ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "乓") ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q5 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q5 ∷
   rw⁻ 80 q6 ∷
   rw⁻ 81 q7 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw⁻ 86 q5 ∷
   rw⁻ 87 q5 ∷
   rw⁻ 88 q5 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q5 ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "乓") ∷
   rw⁻ 92 q5 ∷
   rw⁻ 93 q5 ∷
   rw⁻ 94 q5 ∷
   rw⁻ 95 q6 ∷
   rw⁻ 96 q5 ∷
   rw⁻ 97 q5 ∷
   rw 98 q4 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q15 : Eqn
  q15 = wE 528 W
  q16 : Eqn
  q16 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "与乗") (ℓ "乗与") (low-comm ((S ↑)) (CK₁₀))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 530 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 140 W
  q26 : Eqn
  q26 = wE 529 W
  q27 : Eqn
  q27 = wE 142 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK32 X3]: 185 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞") (ℓ "丞乗丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 30 q11 ∷
   rw 31 q12 ∷
   rw 32 q11 ∷
   rw 29 q11 ∷
   rw 30 q12 ∷
   rw 31 q11 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q15 ∷
   rw 23 q11 ∷
   rw 24 q12 ∷
   rw 25 q11 ∷
   rw 22 q11 ∷
   rw 23 q12 ∷
   rw 24 q11 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 17 q11 ∷
   rw 18 q12 ∷
   rw 19 q11 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q11 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q11 ∷
   rw 14 q16 ∷
   rw 15 q17 ∷
   rw 16 q16 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q13 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q11 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q11 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   rw 6 q15 ∷
   rw 9 q18 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 6 q19 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q21 ∷
   rw 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (ℓ "丽") ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw 9 q24 ∷
   rw 10 q21 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q1 ∷
   rw 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q21 ∷
   rw 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q23 ∷
   rw 4 q19 ∷
   rw 5 q20 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q1 ∷
   rw 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q21 ∷
   rw 4 q25 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (ℓ "乔") ∷
   rw 4 q26 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q21 ∷
   rw 7 q27 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q1 ∷
   rw 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 3 q19 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q21 ∷
   rw 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q23 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q19 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw 6 q24 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q1 ∷
   rw 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q21 ∷
   rw 2 q22 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q23 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q19 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw 5 q24 ∷
   rw 6 q21 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q1 ∷
   rw 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q21 ∷
   rw 1 q22 ∷
   rw⁻ 0 q21 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q23 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw 4 q24 ∷
   rw 5 q21 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q1 ∷ []) Eq.refl
