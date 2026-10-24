{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D196 (W : Ws) where

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
  q1 = wE 76 W
  q2 : Eqn
  q2 = wE 137 W
  q3 : Eqn
  q3 = eqn (ℓ "並丕") (ℓ "丕並") (low-comm (Swap) ((S • S • S)))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 140 W
  q7 : Eqn
  q7 = wE 797 W
  q8 : Eqn
  q8 = wE 29 W
  q9 : Eqn
  q9 = wE 139 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 142 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = wE 537 W
  q18 : Eqn
  q18 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q23 : Eqn
  q23 = wE 796 W
  q24 : Eqn
  q24 = wE 1 W
  q25 : Eqn
  q25 = wE 173 W
  q26 : Eqn
  q26 = wE 3 W
  q27 : Eqn
  q27 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q29 : Eqn
  q29 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q30 : Eqn
  q30 = wE 733 W
  q31 : Eqn
  q31 = wE 175 W
  q32 : Eqn
  q32 = wE 734 W
  q33 : Eqn
  q33 = wE 727 W
  q34 : Eqn
  q34 = wE 13 W
  q35 : Eqn
  q35 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q36 : Eqn
  q36 = wE 78 W
  q37 : Eqn
  q37 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q38 : Eqn
  q38 = wE 728 W
  q39 : Eqn
  q39 = wE 795 W

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part1: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 : ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞中中中乑中中丨丨丨丨丨丨丕久丨並丷丷並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久並丷丷丽丽丽乔丽丽並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part1 = derive (ℓ "丞乊丞丨久丨丨丞乖丞中中中乑中中丨丨丨丨丨丨丕久丨並丷丷並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久並丷丷丽丽丽乔丽丽並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 24 q1 ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   rw 21 q1 ∷
   rw 20 q1 ∷
   rw 19 q1 ∷
   rw 18 q1 ∷
   rw 17 q1 ∷
   rw 16 q1 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q4 ∷
   rw 16 q5 ∷
   rw⁻ 15 q4 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q4 ∷
   rw 15 q5 ∷
   rw⁻ 14 q4 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q4 ∷
   rw 14 q6 ∷
   rw⁻ 13 q4 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw⁻ 12 q4 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q4 ∷
   rw 12 q5 ∷
   rw⁻ 11 q4 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q4 ∷
   rw 11 q5 ∷
   rw⁻ 10 q4 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q7 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   rw 16 q3 ∷
   rw 17 q9 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   rw 22 q10 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q4 ∷
   rw 23 q10 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q4 ∷
   rw 24 q10 ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 24 q4 ∷
   rw 25 q11 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q4 ∷
   rw 26 q10 ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q12 ∷
   rw 51 q13 ∷
   rw 52 q14 ∷
   rw 53 q13 ∷
   rw 50 q13 ∷
   rw 51 q14 ∷
   rw 52 q13 ∷
   rw 49 q15 ∷
   rw 50 q16 ∷
   rw 51 q15 ∷
   rw 48 q13 ∷
   rw 49 q14 ∷
   rw 50 q13 ∷
   rw 47 q13 ∷
   rw 48 q14 ∷
   rw 49 q13 ∷
   rw 46 q13 ∷
   rw 47 q14 ∷
   rw 48 q13 ∷
   rw 45 q17 ∷
   rw 44 q13 ∷
   rw 45 q14 ∷
   rw 46 q13 ∷
   rw 43 q13 ∷
   rw 44 q14 ∷
   rw 45 q13 ∷
   rw 42 q13 ∷
   rw 43 q14 ∷
   rw 44 q13 ∷
   rw 41 q13 ∷
   rw 42 q14 ∷
   rw 43 q13 ∷
   rw 40 q13 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   rw 39 q13 ∷
   rw 40 q14 ∷
   rw 41 q13 ∷
   rw 38 q13 ∷
   rw 39 q14 ∷
   rw 40 q13 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q13 ∷
   rw 35 q18 ∷
   rw 36 q19 ∷
   rw 37 q18 ∷
   rw 34 q15 ∷
   rw 35 q16 ∷
   rw 36 q15 ∷
   rw 33 q13 ∷
   rw 34 q14 ∷
   rw 35 q13 ∷
   rw 32 q13 ∷
   rw 33 q14 ∷
   rw 34 q13 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q13 ∷
   rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 27 q17 ∷
   rw 30 q20 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 28 q22 ∷
   rw⁻ 27 q21 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw⁻ 26 q4 ∷
   rw 25 q6 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (ℓ "乔") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q4 ∷
   rw 23 q5 ∷
   rw⁻ 22 q4 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q23 ∷
   rw 21 q21 ∷
   rw 22 q22 ∷
   rw 23 q21 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q4 ∷
   rw 26 q10 ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q4 ∷
   rw 28 q11 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q4 ∷
   rw 29 q10 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   rw 30 q10 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q12 ∷
   rw 61 q24 ∷
   rw 60 q25 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw 61 q26 ∷
   re 58 1 (ℓ "乏丨乏") ∷
   rw 60 q26 ∷
   re 57 1 (ℓ "乏久乏") ∷
   rw 59 q26 ∷
   re 56 1 (ℓ "乏丨乏") ∷
   rw 58 q26 ∷
   rw 55 q25 ∷
   rw 54 q27 ∷
   rw 53 q27 ∷
   rw 52 q28 ∷
   rw 51 q27 ∷
   rw 50 q27 ∷
   rw 49 q27 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 50 q26 ∷
   rw 47 q27 ∷
   rw 46 q27 ∷
   rw 45 q27 ∷
   rw 44 q27 ∷
   rw 43 q27 ∷
   rw 42 q27 ∷
   rw 41 q27 ∷
   rw 40 q27 ∷
   rw 39 q27 ∷
   rw 38 q29 ∷
   rw 37 q28 ∷
   rw 36 q27 ∷
   rw 35 q27 ∷
   rw 34 q27 ∷
   rw 33 q27 ∷
   rw 32 q27 ∷
   rw 31 q27 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q26 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q26 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q26 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q26 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q26 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q26 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q26 ∷
   rw 25 q30 ∷
   rw 24 q31 ∷
   rw 27 q24 ∷
   re 25 3 (ℓ "丮") ∷
   rw 28 q24 ∷
   re 26 3 (ℓ "乒") ∷
   rw 29 q24 ∷
   re 27 3 (ℓ "丮") ∷
   rw 30 q24 ∷
   re 28 3 (ℓ "丮") ∷
   rw 29 q31 ∷
   rw 32 q24 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q24 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q24 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q24 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q24 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q24 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q24 ∷
   re 36 3 (ℓ "乓") ∷
   rw⁻ 37 q27 ∷
   rw⁻ 38 q27 ∷
   rw⁻ 39 q27 ∷
   rw⁻ 40 q27 ∷
   rw⁻ 41 q27 ∷
   rw⁻ 42 q27 ∷
   rw⁻ 43 q28 ∷
   rw⁻ 44 q29 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q27 ∷
   rw⁻ 47 q27 ∷
   rw⁻ 48 q27 ∷
   rw⁻ 49 q27 ∷
   rw⁻ 50 q27 ∷
   rw⁻ 51 q27 ∷
   rw⁻ 52 q27 ∷
   rw⁻ 53 q27 ∷
   rw 56 q24 ∷
   re 54 3 (ℓ "乓") ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q27 ∷
   rw⁻ 57 q27 ∷
   rw⁻ 58 q28 ∷
   rw⁻ 59 q27 ∷
   rw⁻ 60 q27 ∷
   rw 61 q26 ∷
   rw 66 q24 ∷
   rw 65 q25 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q26 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q26 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q26 ∷
   rw 61 q25 ∷
   rw 60 q27 ∷
   rw 59 q27 ∷
   rw 58 q28 ∷
   rw 57 q27 ∷
   rw 56 q27 ∷
   rw 55 q27 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q26 ∷
   rw 53 q27 ∷
   rw 52 q27 ∷
   rw 51 q27 ∷
   rw 50 q27 ∷
   rw 49 q27 ∷
   rw 48 q27 ∷
   rw 47 q27 ∷
   rw 46 q27 ∷
   rw 45 q27 ∷
   rw 44 q29 ∷
   rw 43 q28 ∷
   rw 42 q27 ∷
   rw 41 q27 ∷
   rw 40 q27 ∷
   rw 39 q27 ∷
   rw 38 q27 ∷
   rw 37 q27 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q26 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q26 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q26 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q26 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q26 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q26 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q26 ∷
   rw 31 q32 ∷
   rw 30 q31 ∷
   rw 33 q24 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q24 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q24 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q31 ∷
   rw 37 q24 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q24 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q24 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q24 ∷
   re 38 3 (ℓ "乑") ∷
   rw 41 q24 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q24 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q24 ∷
   re 41 3 (ℓ "乓") ∷
   rw⁻ 42 q27 ∷
   rw⁻ 43 q27 ∷
   rw⁻ 44 q27 ∷
   rw⁻ 45 q27 ∷
   rw⁻ 46 q27 ∷
   rw⁻ 47 q27 ∷
   rw⁻ 48 q28 ∷
   rw⁻ 49 q29 ∷
   rw⁻ 50 q27 ∷
   rw⁻ 51 q27 ∷
   rw⁻ 52 q27 ∷
   rw⁻ 53 q27 ∷
   rw⁻ 54 q27 ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q27 ∷
   rw⁻ 57 q27 ∷
   rw⁻ 58 q27 ∷
   rw 61 q24 ∷
   re 59 3 (ℓ "乓") ∷
   rw⁻ 60 q27 ∷
   rw⁻ 61 q27 ∷
   rw⁻ 62 q27 ∷
   rw⁻ 63 q28 ∷
   rw⁻ 64 q27 ∷
   rw⁻ 65 q27 ∷
   rw 66 q26 ∷
   rw 60 q33 ∷
   re 60 1 (ℓ "丼両丼") ∷
   rw 59 q34 ∷
   rw⁻ 60 q35 ∷
   rw 61 q36 ∷
   re 59 3 (ℓ "丨") ∷
   re 61 1 (ℓ "丼丵丼") ∷
   rw 60 q34 ∷
   rw⁻ 61 q37 ∷
   rw 62 q36 ∷
   re 60 3 (ℓ "久") ∷
   re 62 1 (ℓ "丼両丼") ∷
   rw 61 q34 ∷
   rw⁻ 62 q35 ∷
   rw 63 q36 ∷
   re 61 3 (ℓ "丨") ∷
   re 63 1 (ℓ "丼両丼") ∷
   rw 62 q34 ∷
   rw⁻ 63 q35 ∷
   rw 64 q36 ∷
   re 62 3 (ℓ "丨") ∷
   rw 42 q38 ∷
   re 42 1 (ℓ "丼両丼") ∷
   rw 41 q34 ∷
   rw⁻ 42 q35 ∷
   rw 43 q36 ∷
   re 41 3 (ℓ "丨") ∷
   re 43 1 (ℓ "丼丵丼") ∷
   rw 42 q34 ∷
   rw⁻ 43 q37 ∷
   rw 44 q36 ∷
   re 42 3 (ℓ "久") ∷
   re 44 1 (ℓ "丼両丼") ∷
   rw 43 q34 ∷
   rw⁻ 44 q35 ∷
   rw 45 q36 ∷
   re 43 3 (ℓ "丨") ∷
   re 45 1 (ℓ "丼両丼") ∷
   rw 44 q34 ∷
   rw⁻ 45 q35 ∷
   rw 46 q36 ∷
   re 44 3 (ℓ "丨") ∷
   rw 45 q20 ∷
   rw 44 q1 ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   rw 41 q1 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q4 ∷
   rw 39 q6 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (ℓ "乔") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q5 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q39 ∷
   rw 35 q8 ∷
   rw 36 q9 ∷ []) Eq.refl
