{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D146 (W : Ws) where

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
  q1 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q2 : Eqn
  q2 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q4 : Eqn
  q4 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 686 W
  q6 : Eqn
  q6 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q7 : Eqn
  q7 = eqn (ℓ "与乊") (ℓ "乊与") (low-comm ((S ↑)) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = wE 726 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 1 W
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = wE 727 W
  q22 : Eqn
  q22 = wE 13 W
  q23 : Eqn
  q23 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q24 : Eqn
  q24 = wE 78 W
  q25 : Eqn
  q25 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q26 : Eqn
  q26 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q27 : Eqn
  q27 = wE 728 W
  q28 : Eqn
  q28 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q29 : Eqn
  q29 = wE 76 W
  q30 : Eqn
  q30 = wE 137 W
  q31 : Eqn
  q31 = wE 729 W
  q32 : Eqn
  q32 = wE 29 W
  q33 : Eqn
  q33 = wE 139 W
  q34 : Eqn
  q34 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q35 : Eqn
  q35 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q36 : Eqn
  q36 = wE 612 W
  q37 : Eqn
  q37 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q38 : Eqn
  q38 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q39 : Eqn
  q39 = wE 661 W
  q40 : Eqn
  q40 = wE 689 W
  q41 : Eqn
  q41 = wE 730 W
  q42 : Eqn
  q42 = wE 153 W

-- Bar(SSSKSS;2,1->0) passes white iX via V2 conjugates 3 part0: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part0 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丮丮丮丮丮乏乓丼両丼乏丛乒丮丮丮丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part0 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丮丮丮丮丮乏乓丼両丼乏丛乒丮丮丮丠丠丠临丠丠丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘")
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
   rw 5 q11 ∷
   rw 4 q11 ∷
   rw 3 q12 ∷
   rw 2 q11 ∷
   rw 1 q11 ∷
   rw 0 q11 ∷
   rw 1 q13 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q14 ∷
   rw 4 q14 ∷
   rw 5 q14 ∷
   rw 6 q15 ∷
   rw 7 q14 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   rw 38 q17 ∷
   re 37 1 (ℓ "乏丨乏") ∷
   rw 39 q18 ∷
   re 36 1 (ℓ "乏丨乏") ∷
   rw 38 q18 ∷
   re 35 1 (ℓ "乏久乏") ∷
   rw 37 q18 ∷
   re 34 1 (ℓ "乏丨乏") ∷
   rw 36 q18 ∷
   rw 33 q19 ∷
   rw 32 q19 ∷
   rw 31 q20 ∷
   rw 30 q19 ∷
   rw 29 q19 ∷
   rw 28 q19 ∷
   rw 29 q21 ∷
   rw 30 q17 ∷
   re 28 3 (ℓ "丮") ∷
   rw 31 q17 ∷
   re 29 3 (ℓ "乒") ∷
   rw 32 q17 ∷
   re 30 3 (ℓ "丮") ∷
   rw 33 q17 ∷
   re 31 3 (ℓ "丮") ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 35 q20 ∷
   rw⁻ 36 q19 ∷
   rw⁻ 37 q19 ∷
   rw 38 q18 ∷
   re 28 1 (ℓ "乏丼両丼乏") ∷
   rw 27 q17 ∷
   re 28 3 (ℓ "乓") ∷
   rw 28 q22 ∷
   rw⁻ 29 q23 ∷
   rw 30 q24 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 33 q18 ∷
   re 27 5 (ℓ "丮") ∷
   re 29 1 (ℓ "乏丼丵丼乏") ∷
   rw 28 q17 ∷
   re 29 3 (ℓ "乓") ∷
   rw 29 q22 ∷
   rw⁻ 30 q25 ∷
   rw 31 q24 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q18 ∷
   re 28 5 (ℓ "乒") ∷
   re 30 1 (ℓ "乏丼両丼乏") ∷
   rw 29 q17 ∷
   re 30 3 (ℓ "乓") ∷
   rw 30 q22 ∷
   rw⁻ 31 q23 ∷
   rw 32 q24 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q18 ∷
   re 29 5 (ℓ "丮") ∷
   re 31 1 (ℓ "乏丼両丼乏") ∷
   rw 30 q17 ∷
   re 31 3 (ℓ "乓") ∷
   rw 31 q22 ∷
   rw⁻ 32 q23 ∷
   rw 33 q24 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 36 q18 ∷
   re 30 5 (ℓ "丮") ∷
   rw 31 q17 ∷
   re 30 1 (ℓ "乏丨乏") ∷
   rw 32 q18 ∷
   re 29 1 (ℓ "乏丨乏") ∷
   rw 31 q18 ∷
   re 28 1 (ℓ "乏久乏") ∷
   rw 30 q18 ∷
   re 27 1 (ℓ "乏丨乏") ∷
   rw 29 q18 ∷
   rw 26 q19 ∷
   rw 25 q19 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   rw 22 q19 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q26 ∷
   rw 16 q20 ∷
   rw 15 q19 ∷
   rw 14 q19 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q19 ∷
   rw 11 q27 ∷
   rw 12 q17 ∷
   re 10 3 (ℓ "丮") ∷
   rw 13 q17 ∷
   re 11 3 (ℓ "乒") ∷
   rw 14 q17 ∷
   re 12 3 (ℓ "丮") ∷
   rw 15 q17 ∷
   re 13 3 (ℓ "丮") ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q19 ∷
   rw⁻ 18 q19 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q20 ∷
   rw⁻ 21 q26 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q19 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q19 ∷
   rw 31 q18 ∷
   re 10 1 (ℓ "乏丼両丼乏") ∷
   rw 9 q17 ∷
   re 10 3 (ℓ "乓") ∷
   rw 10 q22 ∷
   rw⁻ 11 q23 ∷
   rw 12 q24 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 15 q18 ∷
   re 9 5 (ℓ "丮") ∷
   re 11 1 (ℓ "乏丼丵丼乏") ∷
   rw 10 q17 ∷
   re 11 3 (ℓ "乓") ∷
   rw 11 q22 ∷
   rw⁻ 12 q25 ∷
   rw 13 q24 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 16 q18 ∷
   re 10 5 (ℓ "乒") ∷
   re 12 1 (ℓ "乏丼両丼乏") ∷
   rw 11 q17 ∷
   re 12 3 (ℓ "乓") ∷
   rw 12 q22 ∷
   rw⁻ 13 q23 ∷
   rw 14 q24 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 17 q18 ∷
   re 11 5 (ℓ "丮") ∷
   re 13 1 (ℓ "乏丼両丼乏") ∷
   rw 12 q17 ∷
   re 13 3 (ℓ "乓") ∷
   rw 13 q22 ∷
   rw⁻ 14 q23 ∷
   rw 15 q24 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 18 q18 ∷
   re 12 5 (ℓ "丮") ∷
   rw 13 q8 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw⁻ 14 q28 ∷
   rw 13 q29 ∷
   rw⁻ 12 q28 ∷
   re 13 3 (ℓ "举") ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw⁻ 13 q28 ∷
   rw 12 q29 ∷
   rw⁻ 11 q28 ∷
   re 12 3 (ℓ "举") ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw⁻ 12 q28 ∷
   rw 11 q30 ∷
   rw⁻ 10 q28 ∷
   re 11 3 (ℓ "乕") ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw⁻ 11 q28 ∷
   rw 10 q29 ∷
   rw⁻ 9 q28 ∷
   re 10 3 (ℓ "举") ∷
   rw 8 q11 ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 5 q11 ∷
   rw 4 q11 ∷
   rw 3 q11 ∷
   rw 4 q31 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q28 ∷
   rw 4 q32 ∷
   rw 5 q28 ∷
   re 3 3 (ℓ "丮") ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q28 ∷
   rw 5 q33 ∷
   rw 6 q28 ∷
   re 4 3 (ℓ "乒") ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw 6 q32 ∷
   rw 7 q28 ∷
   re 5 3 (ℓ "丮") ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q28 ∷
   rw 7 q32 ∷
   rw 8 q28 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q14 ∷
   rw 8 q14 ∷
   rw 9 q14 ∷
   rw 10 q15 ∷
   rw 11 q14 ∷
   rw 12 q14 ∷
   rw 13 q16 ∷
   rw 37 q1 ∷
   rw 38 q34 ∷
   rw 39 q1 ∷
   rw 36 q1 ∷
   rw 37 q34 ∷
   rw 38 q1 ∷
   rw 35 q3 ∷
   rw 36 q35 ∷
   rw 37 q3 ∷
   rw 34 q1 ∷
   rw 35 q34 ∷
   rw 36 q1 ∷
   rw 33 q1 ∷
   rw 34 q34 ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   rw 33 q34 ∷
   rw 34 q1 ∷
   rw 31 q36 ∷
   rw 30 q1 ∷
   rw 31 q34 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q34 ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   rw 29 q34 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q34 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q34 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q34 ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   rw 25 q34 ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   rw 24 q34 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q34 ∷
   rw 24 q1 ∷
   rw 21 q6 ∷
   rw 22 q37 ∷
   rw 23 q6 ∷
   rw 20 q3 ∷
   rw 21 q35 ∷
   rw 22 q3 ∷
   rw 19 q1 ∷
   rw 20 q34 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q34 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q34 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q34 ∷
   rw 18 q1 ∷
   rw 15 q1 ∷
   rw 16 q34 ∷
   rw 17 q1 ∷
   rw 14 q1 ∷
   rw 15 q34 ∷
   rw 16 q1 ∷
   rw 13 q36 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q38 ∷
   rw⁻ 13 q9 ∷
   rw 12 q11 ∷
   rw 11 q11 ∷
   rw 10 q12 ∷
   rw 9 q11 ∷
   rw 8 q11 ∷
   rw 7 q11 ∷
   rw 8 q39 ∷
   rw 7 q9 ∷
   rw 8 q38 ∷
   rw 9 q9 ∷
   rw 10 q14 ∷
   rw 11 q14 ∷
   rw 12 q14 ∷
   rw 13 q15 ∷
   rw 14 q14 ∷
   rw 15 q14 ∷
   rw 16 q16 ∷
   rw 52 q17 ∷
   re 51 1 (ℓ "乏丨乏") ∷
   rw 53 q18 ∷
   re 50 1 (ℓ "乏丨乏") ∷
   rw 52 q18 ∷
   re 49 1 (ℓ "乏丨乏") ∷
   rw 51 q18 ∷
   re 48 1 (ℓ "乏久乏") ∷
   rw 50 q18 ∷
   rw 47 q40 ∷
   re 46 1 (ℓ "乏丨乏") ∷
   rw 48 q18 ∷
   re 45 1 (ℓ "乏丨乏") ∷
   rw 47 q18 ∷
   re 44 1 (ℓ "乏丨乏") ∷
   rw 46 q18 ∷
   re 43 1 (ℓ "乏丨乏") ∷
   rw 45 q18 ∷
   re 42 1 (ℓ "乏丨乏") ∷
   rw 44 q18 ∷
   re 41 1 (ℓ "乏丨乏") ∷
   rw 43 q18 ∷
   rw 40 q19 ∷
   rw 39 q19 ∷
   rw 38 q20 ∷
   rw 37 q19 ∷
   rw 36 q19 ∷
   rw 35 q19 ∷
   rw 36 q41 ∷
   rw 37 q17 ∷
   re 35 3 (ℓ "丮") ∷
   rw 38 q17 ∷
   re 36 3 (ℓ "丮") ∷
   rw 39 q17 ∷
   re 37 3 (ℓ "丮") ∷
   rw 40 q17 ∷
   re 38 3 (ℓ "丮") ∷
   rw 41 q17 ∷
   re 39 3 (ℓ "丮") ∷
   rw 42 q17 ∷
   re 40 3 (ℓ "丮") ∷
   rw 41 q42 ∷
   rw 44 q17 ∷
   re 42 3 (ℓ "乒") ∷
   rw 45 q17 ∷
   re 43 3 (ℓ "丮") ∷
   rw 46 q17 ∷
   re 44 3 (ℓ "丮") ∷
   rw 47 q17 ∷
   re 45 3 (ℓ "丮") ∷
   rw⁻ 46 q19 ∷
   rw⁻ 47 q19 ∷
   rw⁻ 48 q19 ∷
   rw⁻ 49 q20 ∷
   rw⁻ 50 q19 ∷
   rw⁻ 51 q19 ∷
   rw 52 q18 ∷
   re 35 1 (ℓ "乏丼両丼乏") ∷
   rw 34 q17 ∷
   re 35 3 (ℓ "乓") ∷
   rw 35 q22 ∷
   rw⁻ 36 q23 ∷
   rw 37 q24 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 40 q18 ∷
   re 34 5 (ℓ "丮") ∷
   re 36 1 (ℓ "乏丼両丼乏") ∷
   rw 35 q17 ∷
   re 36 3 (ℓ "乓") ∷
   rw 36 q22 ∷
   rw⁻ 37 q23 ∷
   rw 38 q24 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 41 q18 ∷
   re 35 5 (ℓ "丮") ∷
   re 37 1 (ℓ "乏丼両丼乏") ∷
   rw 36 q17 ∷
   re 37 3 (ℓ "乓") ∷
   rw 37 q22 ∷
   rw⁻ 38 q23 ∷
   rw 39 q24 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 42 q18 ∷
   re 36 5 (ℓ "丮") ∷
   re 38 1 (ℓ "乏丼両丼乏") ∷
   rw 37 q17 ∷
   re 38 3 (ℓ "乓") ∷
   rw 38 q22 ∷
   rw⁻ 39 q23 ∷
   rw 40 q24 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 43 q18 ∷
   re 37 5 (ℓ "丮") ∷
   re 39 1 (ℓ "乏丼両丼乏") ∷
   rw 38 q17 ∷
   re 39 3 (ℓ "乓") ∷
   rw 39 q22 ∷
   rw⁻ 40 q23 ∷
   rw 41 q24 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 44 q18 ∷
   re 38 5 (ℓ "丮") ∷
   re 40 1 (ℓ "乏丼両丼乏") ∷
   rw 39 q17 ∷
   re 40 3 (ℓ "乓") ∷ []) Eq.refl
