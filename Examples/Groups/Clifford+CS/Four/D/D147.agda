{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D147 (W : Ws) where

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
  q1 = wE 13 W
  q2 : Eqn
  q2 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q3 : Eqn
  q3 = wE 78 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q8 : Eqn
  q8 = wE 689 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = wE 731 W
  q13 : Eqn
  q13 = wE 153 W
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
  q19 = wE 7 W
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 732 W
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
  q27 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q28 : Eqn
  q28 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q29 : Eqn
  q29 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q30 : Eqn
  q30 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
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
  q36 = wE 661 W
  q37 : Eqn
  q37 = wE 733 W
  q38 : Eqn
  q38 = wE 734 W
  q39 : Eqn
  q39 = wE 727 W

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丮丮丮丮丮乏乓丼両丼乏丛乒丮丮丮丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乏丨久丨丨乏乆丠丠丠临丠丠丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丮丮丮丮丮乏乓丼両丼乏丛乒丮丮丮丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乏丨久丨丨乏乆丠丠丠临丠丠丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 40 q1 ∷
   rw⁻ 41 q2 ∷
   rw 42 q3 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 45 q4 ∷
   re 39 5 (ℓ "丮") ∷
   rw 40 q5 ∷
   re 42 1 (ℓ "乏丼丵丼乏") ∷
   rw 41 q6 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q1 ∷
   rw⁻ 43 q7 ∷
   rw 44 q3 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q4 ∷
   re 41 5 (ℓ "乒") ∷
   re 43 1 (ℓ "乏丼両丼乏") ∷
   rw 42 q6 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q1 ∷
   rw⁻ 44 q2 ∷
   rw 45 q3 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q4 ∷
   re 42 5 (ℓ "丮") ∷
   re 44 1 (ℓ "乏丼両丼乏") ∷
   rw 43 q6 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q1 ∷
   rw⁻ 45 q2 ∷
   rw 46 q3 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q4 ∷
   re 43 5 (ℓ "丮") ∷
   re 45 1 (ℓ "乏丼両丼乏") ∷
   rw 44 q6 ∷
   re 45 3 (ℓ "乓") ∷
   rw 45 q1 ∷
   rw⁻ 46 q2 ∷
   rw 47 q3 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 50 q4 ∷
   re 44 5 (ℓ "丮") ∷
   rw 45 q6 ∷
   re 44 1 (ℓ "乏丨乏") ∷
   rw 46 q4 ∷
   re 43 1 (ℓ "乏丨乏") ∷
   rw 45 q4 ∷
   re 42 1 (ℓ "乏丨乏") ∷
   rw 44 q4 ∷
   re 41 1 (ℓ "乏久乏") ∷
   rw 43 q4 ∷
   rw 40 q8 ∷
   re 39 1 (ℓ "乏丨乏") ∷
   rw 41 q4 ∷
   re 38 1 (ℓ "乏丨乏") ∷
   rw 40 q4 ∷
   re 37 1 (ℓ "乏丨乏") ∷
   rw 39 q4 ∷
   re 36 1 (ℓ "乏丨乏") ∷
   rw 38 q4 ∷
   re 35 1 (ℓ "乏丨乏") ∷
   rw 37 q4 ∷
   re 34 1 (ℓ "乏丨乏") ∷
   rw 36 q4 ∷
   rw 33 q9 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 18 q12 ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "丮") ∷
   rw 20 q6 ∷
   re 18 3 (ℓ "丮") ∷
   rw 21 q6 ∷
   re 19 3 (ℓ "丮") ∷
   rw 22 q6 ∷
   re 20 3 (ℓ "丮") ∷
   rw 23 q6 ∷
   re 21 3 (ℓ "丮") ∷
   rw 24 q6 ∷
   re 22 3 (ℓ "丮") ∷
   rw 23 q13 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "乒") ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "丮") ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "丮") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "丮") ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q9 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 32 q9 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q10 ∷
   rw⁻ 36 q9 ∷
   rw⁻ 37 q9 ∷
   rw⁻ 38 q9 ∷
   rw⁻ 39 q9 ∷
   rw⁻ 40 q9 ∷
   rw⁻ 41 q9 ∷
   rw⁻ 42 q9 ∷
   rw⁻ 43 q9 ∷
   rw⁻ 44 q9 ∷
   rw 45 q4 ∷
   re 17 1 (ℓ "乏丼両丼乏") ∷
   rw 16 q6 ∷
   re 17 3 (ℓ "乓") ∷
   rw 17 q1 ∷
   rw⁻ 18 q2 ∷
   rw 19 q3 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 22 q4 ∷
   re 16 5 (ℓ "丮") ∷
   re 18 1 (ℓ "乏丼両丼乏") ∷
   rw 17 q6 ∷
   re 18 3 (ℓ "乓") ∷
   rw 18 q1 ∷
   rw⁻ 19 q2 ∷
   rw 20 q3 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 23 q4 ∷
   re 17 5 (ℓ "丮") ∷
   re 19 1 (ℓ "乏丼両丼乏") ∷
   rw 18 q6 ∷
   re 19 3 (ℓ "乓") ∷
   rw 19 q1 ∷
   rw⁻ 20 q2 ∷
   rw 21 q3 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   re 18 5 (ℓ "丮") ∷
   re 20 1 (ℓ "乏丼両丼乏") ∷
   rw 19 q6 ∷
   re 20 3 (ℓ "乓") ∷
   rw 20 q1 ∷
   rw⁻ 21 q2 ∷
   rw 22 q3 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q4 ∷
   re 19 5 (ℓ "丮") ∷
   re 21 1 (ℓ "乏丼両丼乏") ∷
   rw 20 q6 ∷
   re 21 3 (ℓ "乓") ∷
   rw 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw 23 q3 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   re 20 5 (ℓ "丮") ∷
   re 22 1 (ℓ "乏丼両丼乏") ∷
   rw 21 q6 ∷
   re 22 3 (ℓ "乓") ∷
   rw 22 q1 ∷
   rw⁻ 23 q2 ∷
   rw 24 q3 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 27 q4 ∷
   re 21 5 (ℓ "丮") ∷
   rw 22 q5 ∷
   re 24 1 (ℓ "乏丼丵丼乏") ∷
   rw 23 q6 ∷
   re 24 3 (ℓ "乓") ∷
   rw 24 q1 ∷
   rw⁻ 25 q7 ∷
   rw 26 q3 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 29 q4 ∷
   re 23 5 (ℓ "乒") ∷
   re 25 1 (ℓ "乏丼両丼乏") ∷
   rw 24 q6 ∷
   re 25 3 (ℓ "乓") ∷
   rw 25 q1 ∷
   rw⁻ 26 q2 ∷
   rw 27 q3 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 30 q4 ∷
   re 24 5 (ℓ "丮") ∷
   re 26 1 (ℓ "乏丼両丼乏") ∷
   rw 25 q6 ∷
   re 26 3 (ℓ "乓") ∷
   rw 26 q1 ∷
   rw⁻ 27 q2 ∷
   rw 28 q3 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q4 ∷
   re 25 5 (ℓ "丮") ∷
   re 27 1 (ℓ "乏丼両丼乏") ∷
   rw 26 q6 ∷
   re 27 3 (ℓ "乓") ∷
   rw 27 q1 ∷
   rw⁻ 28 q2 ∷
   rw 29 q3 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q4 ∷
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
   rw 11 q19 ∷
   rw 10 q19 ∷
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
   rw 23 q24 ∷
   rw 24 q25 ∷
   rw 25 q24 ∷
   rw 26 q24 ∷
   rw 27 q26 ∷
   rw 51 q27 ∷
   rw 52 q28 ∷
   rw 53 q27 ∷
   rw 50 q27 ∷
   rw 51 q28 ∷
   rw 52 q27 ∷
   rw 49 q29 ∷
   rw 50 q30 ∷
   rw 51 q29 ∷
   rw 48 q27 ∷
   rw 49 q28 ∷
   rw 50 q27 ∷
   rw 47 q27 ∷
   rw 48 q28 ∷
   rw 49 q27 ∷
   rw 46 q27 ∷
   rw 47 q28 ∷
   rw 48 q27 ∷
   rw 45 q31 ∷
   rw 44 q27 ∷
   rw 45 q28 ∷
   rw 46 q27 ∷
   rw 43 q27 ∷
   rw 44 q28 ∷
   rw 45 q27 ∷
   rw 42 q27 ∷
   rw 43 q28 ∷
   rw 44 q27 ∷
   rw 41 q27 ∷
   rw 42 q28 ∷
   rw 43 q27 ∷
   rw 40 q27 ∷
   rw 41 q28 ∷
   rw 42 q27 ∷
   rw 39 q27 ∷
   rw 40 q28 ∷
   rw 41 q27 ∷
   rw 38 q27 ∷
   rw 39 q28 ∷
   rw 40 q27 ∷
   rw 37 q27 ∷
   rw 38 q28 ∷
   rw 39 q27 ∷
   rw 36 q27 ∷
   rw 37 q28 ∷
   rw 38 q27 ∷
   rw 35 q32 ∷
   rw 36 q33 ∷
   rw 37 q32 ∷
   rw 34 q29 ∷
   rw 35 q30 ∷
   rw 36 q29 ∷
   rw 33 q27 ∷
   rw 34 q28 ∷
   rw 35 q27 ∷
   rw 32 q27 ∷
   rw 33 q28 ∷
   rw 34 q27 ∷
   rw 31 q27 ∷
   rw 32 q28 ∷
   rw 33 q27 ∷
   rw 30 q27 ∷
   rw 31 q28 ∷
   rw 32 q27 ∷
   rw 29 q27 ∷
   rw 30 q28 ∷
   rw 31 q27 ∷
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
   rw 22 q19 ∷
   rw 21 q19 ∷
   rw 22 q36 ∷
   rw 21 q34 ∷
   rw 22 q35 ∷
   rw 23 q34 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q24 ∷
   rw 27 q25 ∷
   rw 28 q24 ∷
   rw 29 q24 ∷
   rw 30 q26 ∷
   rw 24 q37 ∷
   rw 30 q38 ∷
   rw 70 q6 ∷
   re 69 1 (ℓ "乏丨乏") ∷
   rw 71 q4 ∷
   re 68 1 (ℓ "乏丨乏") ∷
   rw 70 q4 ∷
   re 67 1 (ℓ "乏久乏") ∷
   rw 69 q4 ∷
   re 66 1 (ℓ "乏丨乏") ∷
   rw 68 q4 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q11 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 61 q39 ∷
   rw 62 q6 ∷
   re 60 3 (ℓ "丮") ∷
   rw 63 q6 ∷
   re 61 3 (ℓ "乒") ∷
   rw 64 q6 ∷
   re 62 3 (ℓ "丮") ∷
   rw 65 q6 ∷
   re 63 3 (ℓ "丮") ∷
   rw⁻ 64 q9 ∷
   rw⁻ 65 q9 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q11 ∷
   rw⁻ 68 q9 ∷
   rw⁻ 69 q9 ∷
   rw 70 q4 ∷
   re 60 1 (ℓ "乏丼両丼乏") ∷
   rw 59 q6 ∷
   re 60 3 (ℓ "乓") ∷
   rw 60 q1 ∷
   rw⁻ 61 q2 ∷
   rw 62 q3 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 65 q4 ∷
   re 59 5 (ℓ "丮") ∷
   re 61 1 (ℓ "乏丼丵丼乏") ∷
   rw 60 q6 ∷
   re 61 3 (ℓ "乓") ∷
   rw 61 q1 ∷
   rw⁻ 62 q7 ∷
   rw 63 q3 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 66 q4 ∷
   re 60 5 (ℓ "乒") ∷
   re 62 1 (ℓ "乏丼両丼乏") ∷
   rw 61 q6 ∷
   re 62 3 (ℓ "乓") ∷
   rw 62 q1 ∷
   rw⁻ 63 q2 ∷
   rw 64 q3 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 67 q4 ∷
   re 61 5 (ℓ "丮") ∷
   re 63 1 (ℓ "乏丼両丼乏") ∷
   rw 62 q6 ∷
   re 63 3 (ℓ "乓") ∷
   rw 63 q1 ∷
   rw⁻ 64 q2 ∷
   rw 65 q3 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 68 q4 ∷
   re 62 5 (ℓ "丮") ∷
   rw 63 q6 ∷
   re 62 1 (ℓ "乏丨乏") ∷
   rw 64 q4 ∷
   re 61 1 (ℓ "乏丨乏") ∷
   rw 63 q4 ∷
   re 60 1 (ℓ "乏久乏") ∷
   rw 62 q4 ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw 61 q4 ∷ []) Eq.refl
