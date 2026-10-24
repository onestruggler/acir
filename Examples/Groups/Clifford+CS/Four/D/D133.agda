{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D133 (W : Ws) where

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
  q1 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q2 : Eqn
  q2 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q4 : Eqn
  q4 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
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
  q11 = wE 140 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 687 W
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
  q19 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 574 W
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
  q27 = wE 575 W
  q28 : Eqn
  q28 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q29 : Eqn
  q29 = wE 76 W
  q30 : Eqn
  q30 = wE 137 W
  q31 : Eqn
  q31 = wE 688 W
  q32 : Eqn
  q32 = wE 29 W
  q33 : Eqn
  q33 = wE 139 W
  q34 : Eqn
  q34 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q35 : Eqn
  q35 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q36 : Eqn
  q36 = wE 612 W
  q37 : Eqn
  q37 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q38 : Eqn
  q38 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q39 : Eqn
  q39 = wE 613 W
  q40 : Eqn
  q40 = wE 689 W
  q41 : Eqn
  q41 = wE 576 W
  q42 : Eqn
  q42 = wE 153 W
  q43 : Eqn
  q43 = eqn (ℓ "乆丛") (ℓ "丛乆") (low₃-comm ((CX₁₀ ↑)) ((S • S • S)))

-- Bar(SSKSKK;2,1->0) passes white iX via V2 conjugates 3 part0: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part0 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠丮丮丮丮丮丮丛乒乆丮丮丮丠丠临丠临临丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3-part0 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乊丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘乊丘丮乒丮丮丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠丮丮丮丮丮丮丛乒乆丮丮丮丠丠临丠临临丘乌丘丘丨久丨丨丘丘丧丧丧丘丮乒丮丮丘乌丘丮丮丮丮丮丮丛乒丮丮丮丘乌丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
   rw 22 q5 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   rw 15 q6 ∷
   rw 16 q7 ∷
   rw 17 q6 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
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
   rw 1 q12 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q14 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   rw 6 q14 ∷
   rw 7 q15 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 36 q17 ∷
   re 35 1 (ℓ "乏丨乏") ∷
   rw 37 q18 ∷
   re 34 1 (ℓ "乏丨乏") ∷
   rw 36 q18 ∷
   re 33 1 (ℓ "乏久乏") ∷
   rw 35 q18 ∷
   re 32 1 (ℓ "乏丨乏") ∷
   rw 34 q18 ∷
   rw 31 q19 ∷
   rw 30 q19 ∷
   rw 29 q20 ∷
   rw 28 q19 ∷
   rw 27 q20 ∷
   rw 26 q20 ∷
   rw 27 q21 ∷
   rw 28 q17 ∷
   re 26 3 (ℓ "丮") ∷
   rw 29 q17 ∷
   re 27 3 (ℓ "乒") ∷
   rw 30 q17 ∷
   re 28 3 (ℓ "丮") ∷
   rw 31 q17 ∷
   re 29 3 (ℓ "丮") ∷
   rw⁻ 30 q20 ∷
   rw⁻ 31 q20 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q20 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 35 q19 ∷
   rw 36 q18 ∷
   re 26 1 (ℓ "乏丼両丼乏") ∷
   rw 25 q17 ∷
   re 26 3 (ℓ "乓") ∷
   rw 26 q22 ∷
   rw⁻ 27 q23 ∷
   rw 28 q24 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q18 ∷
   re 25 5 (ℓ "丮") ∷
   re 27 1 (ℓ "乏丼丵丼乏") ∷
   rw 26 q17 ∷
   re 27 3 (ℓ "乓") ∷
   rw 27 q22 ∷
   rw⁻ 28 q25 ∷
   rw 29 q24 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q18 ∷
   re 26 5 (ℓ "乒") ∷
   re 28 1 (ℓ "乏丼両丼乏") ∷
   rw 27 q17 ∷
   re 28 3 (ℓ "乓") ∷
   rw 28 q22 ∷
   rw⁻ 29 q23 ∷
   rw 30 q24 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 33 q18 ∷
   re 27 5 (ℓ "丮") ∷
   re 29 1 (ℓ "乏丼両丼乏") ∷
   rw 28 q17 ∷
   re 29 3 (ℓ "乓") ∷
   rw 29 q22 ∷
   rw⁻ 30 q23 ∷
   rw 31 q24 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q18 ∷
   re 28 5 (ℓ "丮") ∷
   rw 29 q17 ∷
   re 28 1 (ℓ "乏丨乏") ∷
   rw 30 q18 ∷
   re 27 1 (ℓ "乏丨乏") ∷
   rw 29 q18 ∷
   re 26 1 (ℓ "乏久乏") ∷
   rw 28 q18 ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw 27 q18 ∷
   rw 24 q20 ∷
   rw 23 q20 ∷
   rw 22 q20 ∷
   rw 21 q20 ∷
   rw 20 q20 ∷
   rw 19 q20 ∷
   rw 18 q26 ∷
   rw 17 q19 ∷
   rw 16 q20 ∷
   rw 15 q20 ∷
   rw 14 q20 ∷
   rw 13 q26 ∷
   rw 12 q19 ∷
   rw 11 q26 ∷
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
   rw⁻ 15 q26 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q26 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q20 ∷
   rw⁻ 20 q20 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q26 ∷
   rw⁻ 23 q20 ∷
   rw⁻ 24 q20 ∷
   rw⁻ 25 q20 ∷
   rw⁻ 26 q20 ∷
   rw⁻ 27 q20 ∷
   rw⁻ 28 q20 ∷
   rw 29 q18 ∷
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
   rw 4 q12 ∷
   rw 3 q12 ∷
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
   rw 9 q15 ∷
   rw 10 q14 ∷
   rw 11 q15 ∷
   rw 12 q15 ∷
   rw 13 q16 ∷
   rw 35 q1 ∷
   rw 36 q34 ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   rw 35 q34 ∷
   rw 36 q1 ∷
   rw 33 q3 ∷
   rw 34 q35 ∷
   rw 35 q3 ∷
   rw 32 q1 ∷
   rw 33 q34 ∷
   rw 34 q1 ∷
   rw 31 q3 ∷
   rw 32 q35 ∷
   rw 33 q3 ∷
   rw 30 q3 ∷
   rw 31 q35 ∷
   rw 32 q3 ∷
   rw 29 q36 ∷
   rw 28 q3 ∷
   rw 29 q35 ∷
   rw 30 q3 ∷
   rw 27 q3 ∷
   rw 28 q35 ∷
   rw 29 q3 ∷
   rw 26 q3 ∷
   rw 27 q35 ∷
   rw 28 q3 ∷
   rw 25 q3 ∷
   rw 26 q35 ∷
   rw 27 q3 ∷
   rw 24 q3 ∷
   rw 25 q35 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q35 ∷
   rw 25 q3 ∷
   rw 22 q6 ∷
   rw 23 q37 ∷
   rw 24 q6 ∷
   rw 21 q1 ∷
   rw 22 q34 ∷
   rw 23 q1 ∷
   rw 20 q3 ∷
   rw 21 q35 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q35 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q35 ∷
   rw 20 q3 ∷
   rw 17 q6 ∷
   rw 18 q37 ∷
   rw 19 q6 ∷
   rw 16 q1 ∷
   rw 17 q34 ∷
   rw 18 q1 ∷
   rw 15 q6 ∷
   rw 16 q37 ∷
   rw 17 q6 ∷
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
   rw 8 q12 ∷
   rw 7 q12 ∷
   rw 8 q39 ∷
   rw 7 q9 ∷
   rw 8 q38 ∷
   rw 9 q9 ∷
   rw 10 q14 ∷
   rw 11 q14 ∷
   rw 12 q15 ∷
   rw 13 q14 ∷
   rw 14 q15 ∷
   rw 15 q15 ∷
   rw 16 q16 ∷
   rw 50 q17 ∷
   re 49 1 (ℓ "乏丨乏") ∷
   rw 51 q18 ∷
   re 48 1 (ℓ "乏丨乏") ∷
   rw 50 q18 ∷
   re 47 1 (ℓ "乏丨乏") ∷
   rw 49 q18 ∷
   re 46 1 (ℓ "乏久乏") ∷
   rw 48 q18 ∷
   rw 45 q40 ∷
   re 44 1 (ℓ "乏丨乏") ∷
   rw 46 q18 ∷
   re 43 1 (ℓ "乏丨乏") ∷
   rw 45 q18 ∷
   re 42 1 (ℓ "乏丨乏") ∷
   rw 44 q18 ∷
   re 41 1 (ℓ "乏丨乏") ∷
   rw 43 q18 ∷
   re 40 1 (ℓ "乏丨乏") ∷
   rw 42 q18 ∷
   re 39 1 (ℓ "乏丨乏") ∷
   rw 41 q18 ∷
   rw 38 q19 ∷
   rw 37 q19 ∷
   rw 36 q20 ∷
   rw 35 q19 ∷
   rw 34 q20 ∷
   rw 33 q20 ∷
   rw 34 q41 ∷
   rw 35 q17 ∷
   re 33 3 (ℓ "丮") ∷
   rw 36 q17 ∷
   re 34 3 (ℓ "丮") ∷
   rw 37 q17 ∷
   re 35 3 (ℓ "丮") ∷
   rw 38 q17 ∷
   re 36 3 (ℓ "丮") ∷
   rw 39 q17 ∷
   re 37 3 (ℓ "丮") ∷
   rw 40 q17 ∷
   re 38 3 (ℓ "丮") ∷
   rw 39 q42 ∷
   rw 42 q17 ∷
   re 40 3 (ℓ "乒") ∷
   rw 43 q17 ∷
   re 41 3 (ℓ "丮") ∷
   rw 44 q17 ∷
   re 42 3 (ℓ "丮") ∷
   rw 45 q17 ∷
   re 43 3 (ℓ "丮") ∷
   rw⁻ 44 q20 ∷
   rw⁻ 45 q20 ∷
   rw⁻ 46 q19 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 48 q19 ∷
   rw⁻ 49 q19 ∷
   rw 50 q18 ∷
   re 33 1 (ℓ "乏丼両丼乏") ∷
   rw 32 q17 ∷
   re 33 3 (ℓ "乓") ∷
   rw 33 q22 ∷
   rw⁻ 34 q23 ∷
   rw 35 q24 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q18 ∷
   re 32 5 (ℓ "丮") ∷
   re 34 1 (ℓ "乏丼両丼乏") ∷
   rw 33 q17 ∷
   re 34 3 (ℓ "乓") ∷
   rw 34 q22 ∷
   rw⁻ 35 q23 ∷
   rw 36 q24 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 39 q18 ∷
   re 33 5 (ℓ "丮") ∷
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
   rw 38 q43 ∷
   re 40 1 (ℓ "乏丼丵丼乏") ∷
   rw 39 q17 ∷
   re 40 3 (ℓ "乓") ∷
   rw 40 q22 ∷
   rw⁻ 41 q25 ∷
   rw 42 q24 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 45 q18 ∷
   re 39 5 (ℓ "乒") ∷ []) Eq.refl
