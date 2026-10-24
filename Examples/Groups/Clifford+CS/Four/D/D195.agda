{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D195 (W : Ws) where

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
  q1 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q2 : Eqn
  q2 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 532 W
  q6 : Eqn
  q6 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "与乊") (ℓ "乊与") (low-comm ((S ↑)) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 794 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 727 W
  q19 : Eqn
  q19 = wE 13 W
  q20 : Eqn
  q20 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q21 : Eqn
  q21 = wE 78 W
  q22 : Eqn
  q22 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q23 : Eqn
  q23 = wE 728 W
  q24 : Eqn
  q24 = wE 76 W
  q25 : Eqn
  q25 = wE 137 W
  q26 : Eqn
  q26 = wE 795 W
  q27 : Eqn
  q27 = wE 29 W
  q28 : Eqn
  q28 = wE 139 W
  q29 : Eqn
  q29 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q30 : Eqn
  q30 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q31 : Eqn
  q31 = wE 537 W
  q32 : Eqn
  q32 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q33 : Eqn
  q33 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q34 : Eqn
  q34 = wE 796 W
  q35 : Eqn
  q35 = wE 730 W
  q36 : Eqn
  q36 = wE 540 W
  q37 : Eqn
  q37 = wE 731 W

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part0: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丨久丨丨丞乖丞中中中乑中中丨丨丨丨丨丨丕久丨並丷丷並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part0 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乊丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞乊丞丨久丨丨丞乖丞中中中乑中中丨丨丨丨丨丨丕久丨並丷丷並乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞丮乒丮丮丞丞中中中丞丨久丨丨丞乖丞丨丨丨丨丨丨丕久丨丨丨丞乖丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q1 ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q3 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q5 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 15 q1 ∷
   rw 16 q2 ∷
   rw 17 q1 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q6 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q1 ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q1 ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q1 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q1 ∷
   rw 9 q2 ∷
   rw 10 q1 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 6 q5 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q9 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q11 ∷
   rw 4 q13 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q11 ∷
   rw 3 q12 ∷
   rw⁻ 2 q11 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q11 ∷
   rw 2 q12 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q11 ∷
   rw 1 q12 ∷
   rw⁻ 0 q11 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q14 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q11 ∷
   rw 4 q15 ∷
   rw 5 q11 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw 5 q15 ∷
   rw 6 q11 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q11 ∷
   rw 6 q15 ∷
   rw 7 q11 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q11 ∷
   rw 7 q16 ∷
   rw 8 q11 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q11 ∷
   rw 9 q15 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q17 ∷
   rw 28 q18 ∷
   re 28 1 (ℓ "丼両丼") ∷
   rw 27 q19 ∷
   rw⁻ 28 q20 ∷
   rw 29 q21 ∷
   re 27 3 (ℓ "丨") ∷
   re 29 1 (ℓ "丼丵丼") ∷
   rw 28 q19 ∷
   rw⁻ 29 q22 ∷
   rw 30 q21 ∷
   re 28 3 (ℓ "久") ∷
   re 30 1 (ℓ "丼両丼") ∷
   rw 29 q19 ∷
   rw⁻ 30 q20 ∷
   rw 31 q21 ∷
   re 29 3 (ℓ "丨") ∷
   re 31 1 (ℓ "丼両丼") ∷
   rw 30 q19 ∷
   rw⁻ 31 q20 ∷
   rw 32 q21 ∷
   re 30 3 (ℓ "丨") ∷
   rw 10 q23 ∷
   re 10 1 (ℓ "丼両丼") ∷
   rw 9 q19 ∷
   rw⁻ 10 q20 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "丨") ∷
   re 11 1 (ℓ "丼丵丼") ∷
   rw 10 q19 ∷
   rw⁻ 11 q22 ∷
   rw 12 q21 ∷
   re 10 3 (ℓ "久") ∷
   re 12 1 (ℓ "丼両丼") ∷
   rw 11 q19 ∷
   rw⁻ 12 q20 ∷
   rw 13 q21 ∷
   re 11 3 (ℓ "丨") ∷
   re 13 1 (ℓ "丼両丼") ∷
   rw 12 q19 ∷
   rw⁻ 13 q20 ∷
   rw 14 q21 ∷
   re 12 3 (ℓ "丨") ∷
   rw 13 q8 ∷
   rw 12 q24 ∷
   rw 11 q24 ∷
   rw 10 q25 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q11 ∷
   rw 9 q12 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q11 ∷
   rw 7 q13 ∷
   rw⁻ 6 q11 ∷
   re 7 3 (ℓ "乔") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q11 ∷
   rw 5 q12 ∷
   rw⁻ 4 q11 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q11 ∷
   rw 4 q12 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q26 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw 5 q27 ∷
   rw 6 q27 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q11 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q11 ∷
   rw 9 q15 ∷
   rw 10 q11 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q11 ∷
   rw 10 q15 ∷
   rw 11 q11 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q11 ∷
   rw 11 q16 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   rw 12 q15 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   rw 13 q15 ∷
   rw 14 q11 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q17 ∷
   rw 37 q1 ∷
   rw 38 q29 ∷
   rw 39 q1 ∷
   rw 36 q1 ∷
   rw 37 q29 ∷
   rw 38 q1 ∷
   rw 35 q3 ∷
   rw 36 q30 ∷
   rw 37 q3 ∷
   rw 34 q1 ∷
   rw 35 q29 ∷
   rw 36 q1 ∷
   rw 33 q1 ∷
   rw 34 q29 ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   rw 33 q29 ∷
   rw 34 q1 ∷
   rw 31 q31 ∷
   rw 30 q1 ∷
   rw 31 q29 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q29 ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   rw 29 q29 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q29 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q29 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q29 ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   rw 25 q29 ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   rw 24 q29 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q29 ∷
   rw 24 q1 ∷
   rw 21 q6 ∷
   rw 22 q32 ∷
   rw 23 q6 ∷
   rw 20 q3 ∷
   rw 21 q30 ∷
   rw 22 q3 ∷
   rw 19 q1 ∷
   rw 20 q29 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q29 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q29 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q29 ∷
   rw 18 q1 ∷
   rw 15 q1 ∷
   rw 16 q29 ∷
   rw 17 q1 ∷
   rw 14 q1 ∷
   rw 15 q29 ∷
   rw 16 q1 ∷
   rw 13 q31 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q33 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q11 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q11 ∷
   rw 11 q13 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (ℓ "乔") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q11 ∷
   rw 10 q12 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q11 ∷
   rw 9 q12 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q34 ∷
   rw 7 q9 ∷
   rw 8 q33 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   rw 11 q15 ∷
   rw 12 q11 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   rw 12 q15 ∷
   rw 13 q11 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   rw 13 q15 ∷
   rw 14 q11 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q11 ∷
   rw 14 q16 ∷
   rw 15 q11 ∷
   re 13 3 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   rw 15 q15 ∷
   rw 16 q11 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q11 ∷
   rw 16 q15 ∷
   rw 17 q11 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q17 ∷
   rw 35 q35 ∷
   re 35 1 (ℓ "丼両丼") ∷
   rw 34 q19 ∷
   rw⁻ 35 q20 ∷
   rw 36 q21 ∷
   re 34 3 (ℓ "丨") ∷
   re 36 1 (ℓ "丼両丼") ∷
   rw 35 q19 ∷
   rw⁻ 36 q20 ∷
   rw 37 q21 ∷
   re 35 3 (ℓ "丨") ∷
   re 37 1 (ℓ "丼両丼") ∷
   rw 36 q19 ∷
   rw⁻ 37 q20 ∷
   rw 38 q21 ∷
   re 36 3 (ℓ "丨") ∷
   re 38 1 (ℓ "丼両丼") ∷
   rw 37 q19 ∷
   rw⁻ 38 q20 ∷
   rw 39 q21 ∷
   re 37 3 (ℓ "丨") ∷
   re 39 1 (ℓ "丼両丼") ∷
   rw 38 q19 ∷
   rw⁻ 39 q20 ∷
   rw 40 q21 ∷
   re 38 3 (ℓ "丨") ∷
   re 40 1 (ℓ "丼両丼") ∷
   rw 39 q19 ∷
   rw⁻ 40 q20 ∷
   rw 41 q21 ∷
   re 39 3 (ℓ "丨") ∷
   rw 40 q36 ∷
   re 42 1 (ℓ "丼丵丼") ∷
   rw 41 q19 ∷
   rw⁻ 42 q22 ∷
   rw 43 q21 ∷
   re 41 3 (ℓ "久") ∷
   re 43 1 (ℓ "丼両丼") ∷
   rw 42 q19 ∷
   rw⁻ 43 q20 ∷
   rw 44 q21 ∷
   re 42 3 (ℓ "丨") ∷
   re 44 1 (ℓ "丼両丼") ∷
   rw 43 q19 ∷
   rw⁻ 44 q20 ∷
   rw 45 q21 ∷
   re 43 3 (ℓ "丨") ∷
   re 45 1 (ℓ "丼両丼") ∷
   rw 44 q19 ∷
   rw⁻ 45 q20 ∷
   rw 46 q21 ∷
   re 44 3 (ℓ "丨") ∷
   rw 17 q37 ∷
   re 17 1 (ℓ "丼両丼") ∷
   rw 16 q19 ∷
   rw⁻ 17 q20 ∷
   rw 18 q21 ∷
   re 16 3 (ℓ "丨") ∷
   re 18 1 (ℓ "丼両丼") ∷
   rw 17 q19 ∷
   rw⁻ 18 q20 ∷
   rw 19 q21 ∷
   re 17 3 (ℓ "丨") ∷
   re 19 1 (ℓ "丼両丼") ∷
   rw 18 q19 ∷
   rw⁻ 19 q20 ∷
   rw 20 q21 ∷
   re 18 3 (ℓ "丨") ∷
   re 20 1 (ℓ "丼両丼") ∷
   rw 19 q19 ∷
   rw⁻ 20 q20 ∷
   rw 21 q21 ∷
   re 19 3 (ℓ "丨") ∷
   re 21 1 (ℓ "丼両丼") ∷
   rw 20 q19 ∷
   rw⁻ 21 q20 ∷
   rw 22 q21 ∷
   re 20 3 (ℓ "丨") ∷
   re 22 1 (ℓ "丼両丼") ∷
   rw 21 q19 ∷
   rw⁻ 22 q20 ∷
   rw 23 q21 ∷
   re 21 3 (ℓ "丨") ∷
   rw 22 q36 ∷
   re 24 1 (ℓ "丼丵丼") ∷
   rw 23 q19 ∷
   rw⁻ 24 q22 ∷
   rw 25 q21 ∷
   re 23 3 (ℓ "久") ∷
   re 25 1 (ℓ "丼両丼") ∷
   rw 24 q19 ∷
   rw⁻ 25 q20 ∷
   rw 26 q21 ∷
   re 24 3 (ℓ "丨") ∷
   re 26 1 (ℓ "丼両丼") ∷
   rw 25 q19 ∷
   rw⁻ 26 q20 ∷
   rw 27 q21 ∷
   re 25 3 (ℓ "丨") ∷
   re 27 1 (ℓ "丼両丼") ∷
   rw 26 q19 ∷
   rw⁻ 27 q20 ∷
   rw 28 q21 ∷
   re 26 3 (ℓ "丨") ∷
   rw 27 q8 ∷
   rw 26 q24 ∷
   rw 25 q24 ∷ []) Eq.refl
