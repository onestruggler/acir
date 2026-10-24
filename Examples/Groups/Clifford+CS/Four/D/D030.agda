{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D030 (W : Ws) where

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
  q1 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 21 W
  q4 : Eqn
  q4 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q8 : Eqn
  q8 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q9 : Eqn
  q9 = wE 482 W
  q10 : Eqn
  q10 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q11 : Eqn
  q11 = wE 211 W
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 483 W
  q14 : Eqn
  q14 = wE 175 W
  q15 : Eqn
  q15 = wE 484 W
  q16 : Eqn
  q16 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q18 : Eqn
  q18 = wE 485 W
  q19 : Eqn
  q19 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q21 : Eqn
  q21 = wE 113 W
  q22 : Eqn
  q22 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q23 : Eqn
  q23 = wE 114 W
  q24 : Eqn
  q24 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q25 : Eqn
  q25 = wE 486 W

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part0: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乓丞乖丧丧乄丧乄乄両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乓丞乖丧丧乄丧乄乄両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 28 q1 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "举") ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "举") ∷
   rw 29 q1 ∷
   rw 26 q7 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q3 ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "举") ∷
   rw 28 q7 ∷
   rw 25 q1 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "乑") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "举") ∷
   rw 27 q1 ∷
   rw 24 q7 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q3 ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "举") ∷
   rw 26 q7 ∷
   rw 23 q7 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q3 ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "举") ∷
   rw 25 q7 ∷
   rw 22 q9 ∷
   rw 21 q7 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q3 ∷
   rw 25 q8 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "举") ∷
   rw 23 q7 ∷
   rw 20 q7 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q3 ∷
   rw 24 q8 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "举") ∷
   rw 22 q7 ∷
   rw 19 q7 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q3 ∷
   rw 23 q8 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "举") ∷
   rw 21 q7 ∷
   rw 18 q7 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q3 ∷
   rw 22 q8 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "举") ∷
   rw 20 q7 ∷
   rw 17 q7 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q3 ∷
   rw 21 q8 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "举") ∷
   rw 19 q7 ∷
   rw 16 q7 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q3 ∷
   rw 20 q8 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "举") ∷
   rw 18 q7 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 17 q10 ∷
   rw 14 q1 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "举") ∷
   rw 16 q1 ∷
   rw 13 q7 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q2 ∷
   re 15 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q3 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q6 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 14 3 (ℓ "举") ∷
   rw 15 q7 ∷
   rw 12 q7 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q3 ∷
   rw 16 q8 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "举") ∷
   rw 14 q7 ∷
   rw 11 q7 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   rw 14 q5 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "举") ∷
   rw 13 q7 ∷
   rw 10 q10 ∷
   rw 11 q11 ∷
   rw 12 q10 ∷
   rw 9 q1 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q2 ∷
   re 11 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   re 12 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q6 ∷
   re 10 3 (ℓ "举") ∷
   rw 11 q1 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 10 q10 ∷
   rw 7 q1 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q2 ∷
   re 9 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   re 10 5 (ℓ "乑") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q6 ∷
   re 8 3 (ℓ "举") ∷
   rw 9 q1 ∷
   rw 6 q9 ∷
   rw 9 q2 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q6 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q6 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q6 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q14 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   rw 26 q15 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q16 ∷
   rw⁻ 28 q16 ∷
   rw 10 q18 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 10 q17 ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q16 ∷
   rw 13 q2 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q19 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q6 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q6 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   rw 4 q15 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 6 q19 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乑") ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "乑") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q6 ∷
   rw 35 q1 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q2 ∷
   re 37 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q21 ∷
   rw 39 q22 ∷
   rw 38 q23 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q6 ∷
   re 38 5 (ℓ "乑") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q6 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q2 ∷
   re 36 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q21 ∷
   rw 38 q22 ∷
   rw 37 q23 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q6 ∷
   re 37 5 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q6 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q1 ∷
   rw 33 q7 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q2 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q21 ∷
   rw 37 q24 ∷
   rw 36 q23 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q6 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q6 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q7 ∷
   rw 32 q1 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q2 ∷
   re 34 3 (ℓ "乑") ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q21 ∷
   rw 36 q22 ∷
   rw 35 q23 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q6 ∷
   re 35 5 (ℓ "乑") ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q6 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q1 ∷
   rw 31 q7 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q2 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q21 ∷
   rw 35 q24 ∷
   rw 34 q23 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q6 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q6 ∷
   re 32 3 (ℓ "乓") ∷
   rw 33 q7 ∷
   rw 30 q7 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q21 ∷
   rw 34 q24 ∷
   rw 33 q23 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q6 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q6 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q7 ∷
   rw 29 q25 ∷ []) Eq.refl
