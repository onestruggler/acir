{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D197 (W : Ws) where

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
  q1 = wE 29 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 27 W
  q4 : Eqn
  q4 = wE 142 W
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q8 : Eqn
  q8 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q10 : Eqn
  q10 = wE 537 W
  q11 : Eqn
  q11 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = wE 796 W
  q19 : Eqn
  q19 = wE 730 W
  q20 : Eqn
  q20 = wE 13 W
  q21 : Eqn
  q21 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q22 : Eqn
  q22 = wE 78 W
  q23 : Eqn
  q23 = wE 540 W
  q24 : Eqn
  q24 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q25 : Eqn
  q25 = wE 731 W
  q26 : Eqn
  q26 = wE 76 W
  q27 : Eqn
  q27 = wE 137 W
  q28 : Eqn
  q28 = eqn (ℓ "並丕") (ℓ "丕並") (low-comm (Swap) ((S • S • S)))
  q29 : Eqn
  q29 = wE 797 W
  q30 : Eqn
  q30 = wE 139 W

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part2: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 : ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久並丷丷丽丽丽乔丽丽並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞中中中乑中乏丧乏並並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part2 = derive (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久並丷丷丽丽丽乔丽丽並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞中中中乑中乏丧乏並並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮乒丮丮丞丞丮丮丮丞")
  (rw 37 q1 ∷
   rw 38 q1 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q2 ∷
   rw 41 q3 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q2 ∷
   rw 42 q3 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 42 q2 ∷
   rw 43 q4 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "乑") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q5 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   rw 68 q6 ∷
   rw 69 q7 ∷
   rw 70 q6 ∷
   rw 67 q8 ∷
   rw 68 q9 ∷
   rw 69 q8 ∷
   rw 66 q6 ∷
   rw 67 q7 ∷
   rw 68 q6 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 63 q10 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q6 ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q6 ∷
   rw 60 q6 ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   rw 59 q6 ∷
   rw 60 q7 ∷
   rw 61 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q6 ∷
   rw 57 q6 ∷
   rw 58 q7 ∷
   rw 59 q6 ∷
   rw 56 q6 ∷
   rw 57 q7 ∷
   rw 58 q6 ∷
   rw 55 q6 ∷
   rw 56 q7 ∷
   rw 57 q6 ∷
   rw 54 q6 ∷
   rw 55 q7 ∷
   rw 56 q6 ∷
   rw 53 q11 ∷
   rw 54 q12 ∷
   rw 55 q11 ∷
   rw 52 q8 ∷
   rw 53 q9 ∷
   rw 54 q8 ∷
   rw 51 q6 ∷
   rw 52 q7 ∷
   rw 53 q6 ∷
   rw 50 q6 ∷
   rw 51 q7 ∷
   rw 52 q6 ∷
   rw 49 q6 ∷
   rw 50 q7 ∷
   rw 51 q6 ∷
   rw 48 q6 ∷
   rw 49 q7 ∷
   rw 50 q6 ∷
   rw 47 q6 ∷
   rw 48 q7 ∷
   rw 49 q6 ∷
   rw 46 q6 ∷
   rw 47 q7 ∷
   rw 48 q6 ∷
   rw 45 q10 ∷
   rw 48 q13 ∷
   rw⁻ 47 q14 ∷
   rw⁻ 46 q15 ∷
   rw⁻ 45 q14 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q16 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q16 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q17 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "乔") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q2 ∷
   rw 42 q16 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q2 ∷
   rw 41 q16 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q2 ∷
   rw 40 q16 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q18 ∷
   rw 39 q14 ∷
   rw 40 q15 ∷
   rw 41 q14 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q2 ∷
   rw 44 q3 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏乇乏") ∷
   rw 45 q2 ∷
   rw 46 q4 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "乑") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q3 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q5 ∷
   rw 67 q19 ∷
   re 67 1 (ℓ "丼両丼") ∷
   rw 66 q20 ∷
   rw⁻ 67 q21 ∷
   rw 68 q22 ∷
   re 66 3 (ℓ "丨") ∷
   re 68 1 (ℓ "丼両丼") ∷
   rw 67 q20 ∷
   rw⁻ 68 q21 ∷
   rw 69 q22 ∷
   re 67 3 (ℓ "丨") ∷
   re 69 1 (ℓ "丼両丼") ∷
   rw 68 q20 ∷
   rw⁻ 69 q21 ∷
   rw 70 q22 ∷
   re 68 3 (ℓ "丨") ∷
   re 70 1 (ℓ "丼両丼") ∷
   rw 69 q20 ∷
   rw⁻ 70 q21 ∷
   rw 71 q22 ∷
   re 69 3 (ℓ "丨") ∷
   re 71 1 (ℓ "丼両丼") ∷
   rw 70 q20 ∷
   rw⁻ 71 q21 ∷
   rw 72 q22 ∷
   re 70 3 (ℓ "丨") ∷
   re 72 1 (ℓ "丼両丼") ∷
   rw 71 q20 ∷
   rw⁻ 72 q21 ∷
   rw 73 q22 ∷
   re 71 3 (ℓ "丨") ∷
   rw 72 q23 ∷
   re 74 1 (ℓ "丼丵丼") ∷
   rw 73 q20 ∷
   rw⁻ 74 q24 ∷
   rw 75 q22 ∷
   re 73 3 (ℓ "久") ∷
   re 75 1 (ℓ "丼両丼") ∷
   rw 74 q20 ∷
   rw⁻ 75 q21 ∷
   rw 76 q22 ∷
   re 74 3 (ℓ "丨") ∷
   re 76 1 (ℓ "丼両丼") ∷
   rw 75 q20 ∷
   rw⁻ 76 q21 ∷
   rw 77 q22 ∷
   re 75 3 (ℓ "丨") ∷
   re 77 1 (ℓ "丼両丼") ∷
   rw 76 q20 ∷
   rw⁻ 77 q21 ∷
   rw 78 q22 ∷
   re 76 3 (ℓ "丨") ∷
   rw 49 q25 ∷
   re 49 1 (ℓ "丼両丼") ∷
   rw 48 q20 ∷
   rw⁻ 49 q21 ∷
   rw 50 q22 ∷
   re 48 3 (ℓ "丨") ∷
   re 50 1 (ℓ "丼両丼") ∷
   rw 49 q20 ∷
   rw⁻ 50 q21 ∷
   rw 51 q22 ∷
   re 49 3 (ℓ "丨") ∷
   re 51 1 (ℓ "丼両丼") ∷
   rw 50 q20 ∷
   rw⁻ 51 q21 ∷
   rw 52 q22 ∷
   re 50 3 (ℓ "丨") ∷
   re 52 1 (ℓ "丼両丼") ∷
   rw 51 q20 ∷
   rw⁻ 52 q21 ∷
   rw 53 q22 ∷
   re 51 3 (ℓ "丨") ∷
   re 53 1 (ℓ "丼両丼") ∷
   rw 52 q20 ∷
   rw⁻ 53 q21 ∷
   rw 54 q22 ∷
   re 52 3 (ℓ "丨") ∷
   re 54 1 (ℓ "丼両丼") ∷
   rw 53 q20 ∷
   rw⁻ 54 q21 ∷
   rw 55 q22 ∷
   re 53 3 (ℓ "丨") ∷
   rw 54 q23 ∷
   re 56 1 (ℓ "丼丵丼") ∷
   rw 55 q20 ∷
   rw⁻ 56 q24 ∷
   rw 57 q22 ∷
   re 55 3 (ℓ "久") ∷
   re 57 1 (ℓ "丼両丼") ∷
   rw 56 q20 ∷
   rw⁻ 57 q21 ∷
   rw 58 q22 ∷
   re 56 3 (ℓ "丨") ∷
   re 58 1 (ℓ "丼両丼") ∷
   rw 57 q20 ∷
   rw⁻ 58 q21 ∷
   rw 59 q22 ∷
   re 57 3 (ℓ "丨") ∷
   re 59 1 (ℓ "丼両丼") ∷
   rw 58 q20 ∷
   rw⁻ 59 q21 ∷
   rw 60 q22 ∷
   re 58 3 (ℓ "丨") ∷
   rw 59 q13 ∷
   rw 58 q26 ∷
   rw 57 q26 ∷
   rw 56 q26 ∷
   rw 55 q27 ∷
   rw⁻ 54 q28 ∷
   rw 53 q26 ∷
   rw 52 q26 ∷
   rw 51 q26 ∷
   rw 50 q26 ∷
   rw 49 q26 ∷
   rw 48 q26 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q2 ∷
   rw 48 q16 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q16 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw⁻ 47 q2 ∷
   rw 46 q17 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (ℓ "乔") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q16 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q16 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q16 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q29 ∷
   rw 42 q1 ∷
   rw 43 q1 ∷
   rw 44 q1 ∷
   rw 45 q1 ∷
   rw 46 q1 ∷
   rw 47 q1 ∷
   rw 48 q28 ∷
   rw 49 q30 ∷
   rw 50 q1 ∷
   rw 51 q1 ∷
   rw 52 q1 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q2 ∷
   rw 54 q3 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q2 ∷
   rw 55 q3 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q2 ∷
   rw 56 q3 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏乇乏") ∷
   rw 56 q2 ∷
   rw 57 q4 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乑") ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q2 ∷
   rw 58 q3 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q2 ∷
   rw 59 q3 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q5 ∷
   rw 83 q6 ∷
   rw 84 q7 ∷
   rw 85 q6 ∷
   rw 82 q6 ∷
   rw 83 q7 ∷
   rw 84 q6 ∷
   rw 81 q8 ∷
   rw 82 q9 ∷
   rw 83 q8 ∷
   rw 80 q6 ∷
   rw 81 q7 ∷
   rw 82 q6 ∷
   rw 79 q6 ∷
   rw 80 q7 ∷
   rw 81 q6 ∷
   rw 78 q6 ∷
   rw 79 q7 ∷
   rw 80 q6 ∷
   rw 77 q10 ∷
   rw 76 q6 ∷
   rw 77 q7 ∷
   rw 78 q6 ∷
   rw 75 q6 ∷
   rw 76 q7 ∷
   rw 77 q6 ∷
   rw 74 q6 ∷
   rw 75 q7 ∷
   rw 76 q6 ∷
   rw 73 q6 ∷
   rw 74 q7 ∷
   rw 75 q6 ∷
   rw 72 q6 ∷
   rw 73 q7 ∷
   rw 74 q6 ∷
   rw 71 q6 ∷
   rw 72 q7 ∷
   rw 73 q6 ∷
   rw 70 q6 ∷
   rw 71 q7 ∷
   rw 72 q6 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   rw 68 q6 ∷
   rw 69 q7 ∷
   rw 70 q6 ∷
   rw 67 q11 ∷
   rw 68 q12 ∷
   rw 69 q11 ∷
   rw 66 q8 ∷
   rw 67 q9 ∷
   rw 68 q8 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 63 q6 ∷
   rw 64 q7 ∷
   rw 65 q6 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q6 ∷
   rw 61 q6 ∷
   rw 62 q7 ∷
   rw 63 q6 ∷
   rw 60 q6 ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   rw 59 q10 ∷
   rw 62 q13 ∷
   rw⁻ 61 q14 ∷
   rw⁻ 60 q15 ∷
   rw⁻ 59 q14 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q2 ∷
   rw 59 q16 ∷
   rw⁻ 58 q2 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q2 ∷
   rw 58 q16 ∷
   rw⁻ 57 q2 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q2 ∷
   rw 57 q17 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (ℓ "乔") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q2 ∷
   rw 56 q16 ∷
   rw⁻ 55 q2 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q2 ∷
   rw 55 q16 ∷
   rw⁻ 54 q2 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q2 ∷
   rw 54 q16 ∷
   rw⁻ 53 q2 ∷
   re 54 3 (ℓ "丽") ∷
   rw 54 q18 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q2 ∷
   rw 57 q3 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q2 ∷
   rw 58 q3 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q2 ∷
   rw 59 q3 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏乇乏") ∷
   rw 59 q2 ∷
   rw 60 q4 ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "乑") ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q2 ∷
   rw 61 q3 ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q2 ∷
   rw 62 q3 ∷
   rw 63 q2 ∷ []) Eq.refl
