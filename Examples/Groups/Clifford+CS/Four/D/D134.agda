{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D134 (W : Ws) where

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
  q6 = wE 689 W
  q7 : Eqn
  q7 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = wE 577 W
  q11 : Eqn
  q11 = wE 153 W
  q12 : Eqn
  q12 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q13 : Eqn
  q13 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 76 W
  q17 : Eqn
  q17 = wE 137 W
  q18 : Eqn
  q18 = eqn (ℓ "並丛") (ℓ "丛並") (low-comm (Swap) (((S • S • S) ↑)))
  q19 : Eqn
  q19 = wE 140 W
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = wE 690 W
  q22 : Eqn
  q22 = wE 29 W
  q23 : Eqn
  q23 = wE 139 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q28 : Eqn
  q28 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q29 : Eqn
  q29 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q30 : Eqn
  q30 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q31 : Eqn
  q31 = wE 612 W
  q32 : Eqn
  q32 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q33 : Eqn
  q33 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q34 : Eqn
  q34 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q35 : Eqn
  q35 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q36 : Eqn
  q36 = wE 613 W
  q37 : Eqn
  q37 = wE 578 W
  q38 : Eqn
  q38 = wE 579 W
  q39 : Eqn
  q39 = wE 574 W
  q40 : Eqn
  q40 = wE 575 W

-- Bar(SSKSKK;2,1->0) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠丮丮丮丮丮丮丛乒乆丮丮丮丠丠临丠临临丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧乄丧乄乄乆丮乒丮丮临与乏临与丠丠丠临与丠丠丠丠丠丠乏乆丠丠临丠临临丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠丮丮丮丮丮丮丛乒乆丮丮丮丠丠临丠临临丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧乄丧乄乄乆丮乒丮丮临与乏临与丠丠丠临与丠丠丠丠丠丠乏乆丠丠临丠临临丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘")
  (re 41 1 (ℓ "乏丼両丼乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "乓") ∷
   rw 41 q2 ∷
   rw⁻ 42 q3 ∷
   rw 43 q4 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 46 q5 ∷
   re 40 5 (ℓ "丮") ∷
   re 42 1 (ℓ "乏丼両丼乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q2 ∷
   rw⁻ 43 q3 ∷
   rw 44 q4 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q5 ∷
   re 41 5 (ℓ "丮") ∷
   re 43 1 (ℓ "乏丼両丼乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q2 ∷
   rw⁻ 44 q3 ∷
   rw 45 q4 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q5 ∷
   re 42 5 (ℓ "丮") ∷
   rw 43 q1 ∷
   re 42 1 (ℓ "乏丨乏") ∷
   rw 44 q5 ∷
   re 41 1 (ℓ "乏丨乏") ∷
   rw 43 q5 ∷
   re 40 1 (ℓ "乏丨乏") ∷
   rw 42 q5 ∷
   re 39 1 (ℓ "乏久乏") ∷
   rw 41 q5 ∷
   rw 38 q6 ∷
   re 37 1 (ℓ "乏丨乏") ∷
   rw 39 q5 ∷
   re 36 1 (ℓ "乏丨乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏丨乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏丨乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丨乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏丨乏") ∷
   rw 34 q5 ∷
   rw 31 q7 ∷
   rw 30 q7 ∷
   rw 29 q7 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 18 q10 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丮") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丮") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丮") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丮") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丮") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丮") ∷
   rw 23 q11 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乒") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丮") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丮") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丮") ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q8 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q8 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q9 ∷
   rw⁻ 36 q8 ∷
   rw⁻ 37 q7 ∷
   rw⁻ 38 q7 ∷
   rw⁻ 39 q7 ∷
   rw⁻ 40 q7 ∷
   rw⁻ 41 q7 ∷
   rw⁻ 42 q7 ∷
   rw 43 q5 ∷
   re 17 1 (ℓ "乏丼両丼乏") ∷
   rw 16 q1 ∷
   re 17 3 (ℓ "乓") ∷
   rw 17 q2 ∷
   rw⁻ 18 q3 ∷
   rw 19 q4 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 22 q5 ∷
   re 16 5 (ℓ "丮") ∷
   re 18 1 (ℓ "乏丼両丼乏") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "乓") ∷
   rw 18 q2 ∷
   rw⁻ 19 q3 ∷
   rw 20 q4 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 23 q5 ∷
   re 17 5 (ℓ "丮") ∷
   re 19 1 (ℓ "乏丼両丼乏") ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "乓") ∷
   rw 19 q2 ∷
   rw⁻ 20 q3 ∷
   rw 21 q4 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q5 ∷
   re 18 5 (ℓ "丮") ∷
   re 20 1 (ℓ "乏丼両丼乏") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "乓") ∷
   rw 20 q2 ∷
   rw⁻ 21 q3 ∷
   rw 22 q4 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q5 ∷
   re 19 5 (ℓ "丮") ∷
   re 21 1 (ℓ "乏丼両丼乏") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "乓") ∷
   rw 21 q2 ∷
   rw⁻ 22 q3 ∷
   rw 23 q4 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q5 ∷
   re 20 5 (ℓ "丮") ∷
   re 22 1 (ℓ "乏丼両丼乏") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "乓") ∷
   rw 22 q2 ∷
   rw⁻ 23 q3 ∷
   rw 24 q4 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 27 q5 ∷
   re 21 5 (ℓ "丮") ∷
   rw 22 q12 ∷
   re 24 1 (ℓ "乏丼丵丼乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "乓") ∷
   rw 24 q2 ∷
   rw⁻ 25 q13 ∷
   rw 26 q4 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 29 q5 ∷
   re 23 5 (ℓ "乒") ∷
   re 25 1 (ℓ "乏丼両丼乏") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw 25 q2 ∷
   rw⁻ 26 q3 ∷
   rw 27 q4 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 30 q5 ∷
   re 24 5 (ℓ "丮") ∷
   re 26 1 (ℓ "乏丼両丼乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "乓") ∷
   rw 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw 28 q4 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q5 ∷
   re 25 5 (ℓ "丮") ∷
   re 27 1 (ℓ "乏丼両丼乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw 27 q2 ∷
   rw⁻ 28 q3 ∷
   rw 29 q4 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q5 ∷
   re 26 5 (ℓ "丮") ∷
   rw 27 q14 ∷
   re 26 1 (ℓ "乏丨乏") ∷
   rw⁻ 28 q15 ∷
   rw 27 q16 ∷
   rw⁻ 26 q15 ∷
   re 27 3 (ℓ "举") ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw⁻ 27 q15 ∷
   rw 26 q16 ∷
   rw⁻ 25 q15 ∷
   re 26 3 (ℓ "举") ∷
   re 24 1 (ℓ "乏丨乏") ∷
   rw⁻ 26 q15 ∷
   rw 25 q16 ∷
   rw⁻ 24 q15 ∷
   re 25 3 (ℓ "举") ∷
   re 23 1 (ℓ "乏久乏") ∷
   rw⁻ 25 q15 ∷
   rw 24 q17 ∷
   rw⁻ 23 q15 ∷
   re 24 3 (ℓ "乕") ∷
   rw⁻ 22 q18 ∷
   re 21 1 (ℓ "乏丨乏") ∷
   rw⁻ 23 q15 ∷
   rw 22 q16 ∷
   rw⁻ 21 q15 ∷
   re 22 3 (ℓ "举") ∷
   re 20 1 (ℓ "乏丨乏") ∷
   rw⁻ 22 q15 ∷
   rw 21 q16 ∷
   rw⁻ 20 q15 ∷
   re 21 3 (ℓ "举") ∷
   re 19 1 (ℓ "乏丨乏") ∷
   rw⁻ 21 q15 ∷
   rw 20 q16 ∷
   rw⁻ 19 q15 ∷
   re 20 3 (ℓ "举") ∷
   re 18 1 (ℓ "乏丨乏") ∷
   rw⁻ 20 q15 ∷
   rw 19 q16 ∷
   rw⁻ 18 q15 ∷
   re 19 3 (ℓ "举") ∷
   re 17 1 (ℓ "乏丨乏") ∷
   rw⁻ 19 q15 ∷
   rw 18 q16 ∷
   rw⁻ 17 q15 ∷
   re 18 3 (ℓ "举") ∷
   re 16 1 (ℓ "乏丨乏") ∷
   rw⁻ 18 q15 ∷
   rw 17 q16 ∷
   rw⁻ 16 q15 ∷
   re 17 3 (ℓ "举") ∷
   rw 15 q19 ∷
   rw 14 q19 ∷
   rw 13 q20 ∷
   rw 12 q19 ∷
   rw 11 q20 ∷
   rw 10 q20 ∷
   rw 11 q21 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q15 ∷
   rw 11 q22 ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "丮") ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q15 ∷
   rw 12 q22 ∷
   rw 13 q15 ∷
   re 11 3 (ℓ "丮") ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q15 ∷
   rw 13 q22 ∷
   rw 14 q15 ∷
   re 12 3 (ℓ "丮") ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q15 ∷
   rw 14 q22 ∷
   rw 15 q15 ∷
   re 13 3 (ℓ "丮") ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q15 ∷
   rw 15 q22 ∷
   rw 16 q15 ∷
   re 14 3 (ℓ "丮") ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q15 ∷
   rw 16 q22 ∷
   rw 17 q15 ∷
   re 15 3 (ℓ "丮") ∷
   rw 16 q18 ∷
   re 18 1 (ℓ "乏么乏") ∷
   rw 17 q15 ∷
   rw 18 q23 ∷
   rw 19 q15 ∷
   re 17 3 (ℓ "乒") ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q15 ∷
   rw 19 q22 ∷
   rw 20 q15 ∷
   re 18 3 (ℓ "丮") ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q15 ∷
   rw 20 q22 ∷
   rw 21 q15 ∷
   re 19 3 (ℓ "丮") ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q15 ∷
   rw 21 q22 ∷
   rw 22 q15 ∷
   re 20 3 (ℓ "丮") ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q25 ∷
   rw 24 q24 ∷
   rw 25 q25 ∷
   rw 26 q25 ∷
   rw 27 q26 ∷
   rw 49 q27 ∷
   rw 50 q28 ∷
   rw 51 q27 ∷
   rw 48 q27 ∷
   rw 49 q28 ∷
   rw 50 q27 ∷
   rw 47 q29 ∷
   rw 48 q30 ∷
   rw 49 q29 ∷
   rw 46 q27 ∷
   rw 47 q28 ∷
   rw 48 q27 ∷
   rw 45 q29 ∷
   rw 46 q30 ∷
   rw 47 q29 ∷
   rw 44 q29 ∷
   rw 45 q30 ∷
   rw 46 q29 ∷
   rw 43 q31 ∷
   rw 42 q29 ∷
   rw 43 q30 ∷
   rw 44 q29 ∷
   rw 41 q29 ∷
   rw 42 q30 ∷
   rw 43 q29 ∷
   rw 40 q29 ∷
   rw 41 q30 ∷
   rw 42 q29 ∷
   rw 39 q29 ∷
   rw 40 q30 ∷
   rw 41 q29 ∷
   rw 38 q29 ∷
   rw 39 q30 ∷
   rw 40 q29 ∷
   rw 37 q29 ∷
   rw 38 q30 ∷
   rw 39 q29 ∷
   rw 36 q32 ∷
   rw 37 q33 ∷
   rw 38 q32 ∷
   rw 35 q27 ∷
   rw 36 q28 ∷
   rw 37 q27 ∷
   rw 34 q29 ∷
   rw 35 q30 ∷
   rw 36 q29 ∷
   rw 33 q29 ∷
   rw 34 q30 ∷
   rw 35 q29 ∷
   rw 32 q29 ∷
   rw 33 q30 ∷
   rw 34 q29 ∷
   rw 31 q32 ∷
   rw 32 q33 ∷
   rw 33 q32 ∷
   rw 30 q27 ∷
   rw 31 q28 ∷
   rw 32 q27 ∷
   rw 29 q32 ∷
   rw 30 q33 ∷
   rw 31 q32 ∷
   rw 28 q27 ∷
   rw 29 q28 ∷
   rw 30 q27 ∷
   rw 27 q31 ∷
   rw 30 q14 ∷
   rw⁻ 29 q34 ∷
   rw⁻ 28 q35 ∷
   rw⁻ 27 q34 ∷
   rw 26 q19 ∷
   rw 25 q19 ∷
   rw 24 q20 ∷
   rw 23 q19 ∷
   rw 22 q20 ∷
   rw 21 q20 ∷
   rw 22 q36 ∷
   rw 21 q34 ∷
   rw 22 q35 ∷
   rw 23 q34 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q25 ∷
   rw 27 q24 ∷
   rw 28 q25 ∷
   rw 29 q25 ∷
   rw 30 q26 ∷
   rw 24 q37 ∷
   rw 30 q38 ∷
   rw 68 q1 ∷
   re 67 1 (ℓ "乏丨乏") ∷
   rw 69 q5 ∷
   re 66 1 (ℓ "乏丨乏") ∷
   rw 68 q5 ∷
   re 65 1 (ℓ "乏久乏") ∷
   rw 67 q5 ∷
   re 64 1 (ℓ "乏丨乏") ∷
   rw 66 q5 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q7 ∷
   rw 60 q9 ∷
   rw 59 q7 ∷
   rw 58 q7 ∷
   rw 59 q39 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "丮") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乒") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "丮") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "丮") ∷
   rw⁻ 62 q7 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 64 q9 ∷
   rw⁻ 65 q7 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q9 ∷
   rw 68 q5 ∷
   re 58 1 (ℓ "乏丼両丼乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q4 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q5 ∷
   re 57 5 (ℓ "丮") ∷
   re 59 1 (ℓ "乏丼丵丼乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "乓") ∷
   rw 59 q2 ∷
   rw⁻ 60 q13 ∷
   rw 61 q4 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 64 q5 ∷
   re 58 5 (ℓ "乒") ∷
   re 60 1 (ℓ "乏丼両丼乏") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "乓") ∷
   rw 60 q2 ∷
   rw⁻ 61 q3 ∷
   rw 62 q4 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 65 q5 ∷
   re 59 5 (ℓ "丮") ∷
   re 61 1 (ℓ "乏丼両丼乏") ∷
   rw 60 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 61 q2 ∷
   rw⁻ 62 q3 ∷
   rw 63 q4 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 66 q5 ∷
   re 60 5 (ℓ "丮") ∷
   rw 61 q1 ∷
   re 60 1 (ℓ "乏丨乏") ∷
   rw 62 q5 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw 61 q5 ∷
   re 58 1 (ℓ "乏久乏") ∷
   rw 60 q5 ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw 59 q5 ∷
   rw 56 q7 ∷
   rw 55 q7 ∷
   rw 54 q7 ∷
   rw 53 q7 ∷
   rw 52 q7 ∷
   rw 51 q7 ∷
   rw 50 q8 ∷
   rw 49 q9 ∷
   rw 48 q7 ∷
   rw 47 q7 ∷
   rw 46 q7 ∷
   rw 45 q8 ∷
   rw 44 q9 ∷
   rw 43 q8 ∷
   rw 42 q9 ∷
   rw 43 q40 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "丮") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乒") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "丮") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "丮") ∷
   rw⁻ 46 q9 ∷
   rw⁻ 47 q8 ∷ []) Eq.refl
