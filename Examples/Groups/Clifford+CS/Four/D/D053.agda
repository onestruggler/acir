{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D053 (W : Ws) where

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
  q1 = wE 113 W
  q2 : Eqn
  q2 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q3 : Eqn
  q3 = wE 114 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q6 : Eqn
  q6 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = wE 486 W
  q10 : Eqn
  q10 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q11 : Eqn
  q11 = wE 487 W
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 557 W
  q14 : Eqn
  q14 = wE 175 W
  q15 : Eqn
  q15 = wE 558 W
  q16 : Eqn
  q16 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "丏乖") (ℓ "乖丏") (low-comm (((S • S • S) ↑)) (CX₁₀))
  q18 : Eqn
  q18 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q19 : Eqn
  q19 = wE 559 W
  q20 : Eqn
  q20 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q21 : Eqn
  q21 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))

-- Bar(SSSKSS;3,2->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (ℓ "丞举丞両丵両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧丞乏乏丼临丼乓乏乏丞丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丞乏乏丧乏乆乏丞乄丧丧丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (ℓ "丞举丞両丵両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧丞乏乏丼临丼乓乏乏丞丧丧両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丞乏乏丧乏乆乏丞乄丧丧丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 40 q1 ∷
   rw 39 q2 ∷
   rw 38 q3 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q4 ∷
   re 38 5 (ℓ "乑") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q4 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q5 ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q7 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q7 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q1 ∷
   rw 38 q8 ∷
   rw 37 q3 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q4 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q4 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q6 ∷
   rw 33 q6 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q7 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q1 ∷
   rw 37 q8 ∷
   rw 36 q3 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q4 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q4 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q6 ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q7 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q7 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q1 ∷
   rw 36 q8 ∷
   rw 35 q3 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q4 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q6 ∷
   rw 31 q9 ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q7 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q1 ∷
   rw 34 q8 ∷
   rw 33 q3 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q4 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q4 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q6 ∷
   rw 29 q6 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q7 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q1 ∷
   rw 33 q8 ∷
   rw 32 q3 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q4 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q6 ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q7 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q1 ∷
   rw 32 q8 ∷
   rw 31 q3 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q4 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q6 ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q7 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q1 ∷
   rw 31 q8 ∷
   rw 30 q3 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q4 ∷
   re 28 3 (ℓ "乓") ∷
   rw 29 q6 ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q7 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q1 ∷
   rw 30 q8 ∷
   rw 29 q3 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q4 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q6 ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q7 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q1 ∷
   rw 29 q8 ∷
   rw 28 q3 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q4 ∷
   re 26 3 (ℓ "乓") ∷
   rw 27 q6 ∷
   rw 24 q6 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q7 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q1 ∷
   rw 28 q8 ∷
   rw 27 q3 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q4 ∷
   re 25 3 (ℓ "乓") ∷
   rw 26 q6 ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q7 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q1 ∷
   rw 27 q8 ∷
   rw 26 q3 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 24 3 (ℓ "乓") ∷
   rw 25 q6 ∷
   rw 22 q6 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q7 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q1 ∷
   rw 26 q8 ∷
   rw 25 q3 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q4 ∷
   re 23 3 (ℓ "乓") ∷
   rw 24 q6 ∷
   rw 21 q10 ∷
   rw 22 q11 ∷
   rw 23 q10 ∷
   rw 20 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q7 ∷
   re 22 3 (ℓ "乑") ∷
   re 22 1 (ℓ "乏丼临丼乏") ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "乑") ∷
   re 23 1 (ℓ "乏乄乏") ∷
   rw 25 q4 ∷
   re 21 3 (ℓ "乓") ∷
   rw 22 q5 ∷
   rw 19 q6 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q7 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q1 ∷
   rw 23 q8 ∷
   rw 22 q3 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q4 ∷
   re 20 3 (ℓ "乓") ∷
   rw 21 q6 ∷
   rw 18 q6 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q7 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q1 ∷
   rw 22 q8 ∷
   rw 21 q3 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q4 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 19 3 (ℓ "乓") ∷
   rw 20 q6 ∷
   rw 17 q6 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q7 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q7 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q1 ∷
   rw 21 q8 ∷
   rw 20 q3 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q4 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 18 3 (ℓ "乓") ∷
   rw 19 q6 ∷
   rw 16 q6 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q7 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q7 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q1 ∷
   rw 20 q8 ∷
   rw 19 q3 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q4 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 17 3 (ℓ "乓") ∷
   rw 18 q6 ∷
   rw 15 q6 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q7 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q7 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q1 ∷
   rw 19 q8 ∷
   rw 18 q3 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q4 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   re 16 3 (ℓ "乓") ∷
   rw 17 q6 ∷
   rw 14 q6 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q7 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q7 ∷
   re 20 3 (ℓ "乓") ∷
   rw 19 q1 ∷
   rw 18 q8 ∷
   rw 17 q3 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q4 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q4 ∷
   re 15 3 (ℓ "乓") ∷
   rw 16 q6 ∷
   rw 13 q9 ∷
   rw 16 q7 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 16 q4 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q4 ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "乓") ∷
   rw 9 q14 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "乑") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q4 ∷
   rw 35 q15 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 40 q17 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 42 q16 ∷
   rw⁻ 43 q16 ∷
   rw⁻ 44 q16 ∷
   rw 17 q19 ∷
   rw⁻ 16 q16 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q16 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q16 ∷
   rw⁻ 21 q16 ∷
   rw⁻ 22 q17 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 25 q16 ∷
   rw⁻ 26 q16 ∷
   rw 27 q7 ∷
   rw 26 q20 ∷
   rw 25 q20 ∷
   rw 24 q20 ∷
   rw 23 q21 ∷
   rw 22 q22 ∷
   rw 21 q20 ∷
   rw 20 q20 ∷
   rw 19 q20 ∷
   rw 18 q20 ∷
   rw 17 q20 ∷
   rw 16 q20 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q4 ∷
   rw 11 q15 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q20 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q20 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 16 q22 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q20 ∷
   rw⁻ 20 q20 ∷
   rw 23 q7 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q7 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q7 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "乑") ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q4 ∷
   rw 51 q6 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q7 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q7 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q1 ∷
   rw 55 q8 ∷
   rw 54 q3 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q4 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q4 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q6 ∷
   rw 50 q6 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q7 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q7 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q1 ∷
   rw 54 q8 ∷
   rw 53 q3 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q4 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q4 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q6 ∷
   rw 49 q5 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q7 ∷
   re 51 3 (ℓ "乑") ∷
   re 51 1 (ℓ "乏丼临丼乏") ∷
   rw 57 q7 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q4 ∷
   re 52 5 (ℓ "乑") ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw 54 q4 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q5 ∷
   rw 48 q6 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q7 ∷ []) Eq.refl
