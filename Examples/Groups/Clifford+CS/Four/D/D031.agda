{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D031 (W : Ws) where

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
  q1 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 113 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q5 : Eqn
  q5 = wE 114 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q8 : Eqn
  q8 = wE 487 W
  q9 : Eqn
  q9 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q11 : Eqn
  q11 = wE 486 W
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 488 W
  q14 : Eqn
  q14 = wE 175 W
  q15 : Eqn
  q15 = wE 489 W
  q16 : Eqn
  q16 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "丏乖") (ℓ "乖丏") (low-comm (((S • S • S) ↑)) (CX₁₀))
  q18 : Eqn
  q18 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q19 : Eqn
  q19 = wE 490 W
  q20 : Eqn
  q20 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q21 : Eqn
  q21 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (ℓ "丞举丞両丵両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乓丞乖丧丧乄丧乄乄両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丞乏乏丼丠丼乓乏乏丞丧丧丧丧乖丧丧乄丧乄乄丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (ℓ "丞举丞両丵両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乓丞乖丧丧乄丧乄乄両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞") (ℓ "丞举丞両丵両両丞乓丞両両両両両両丏丵両両両中中乑中乑乑乖乄且乄且丧丧丧乄且丧丞乏乏丼丠丼乓乏乏丞丧丧丧丧乖丧丧乄丧乄乄丞丮乒丮丮丞丞中中中丞両丵両両丞乓丞両両両両両両丏丵両両両丞乓丞丞丮乒丮丮丞丞丮丮丮丞")
  (rw 28 q1 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "乓") ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "乓") ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "乓") ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "乓") ∷
   rw 25 q1 ∷
   rw 22 q7 ∷
   rw 23 q8 ∷
   rw 24 q7 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "乑") ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q3 ∷
   rw 25 q10 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "乓") ∷
   rw 23 q9 ∷
   rw 20 q1 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "乓") ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "乓") ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "乓") ∷
   rw 20 q1 ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q7 ∷
   rw 16 q9 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "乑") ∷
   re 18 1 (ℓ "乏丼临丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q3 ∷
   rw 20 q10 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "乑") ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "乓") ∷
   rw 18 q9 ∷
   rw 15 q7 ∷
   rw 16 q8 ∷
   rw 17 q7 ∷
   rw 14 q9 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乓") ∷
   rw 19 q3 ∷
   rw 18 q10 ∷
   rw 17 q5 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "乓") ∷
   rw 16 q9 ∷
   rw 13 q11 ∷
   rw 16 q2 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 16 q6 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q6 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "乓") ∷
   rw 9 q14 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乑") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "乑") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   rw 33 q15 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q18 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 41 q16 ∷
   rw⁻ 42 q16 ∷
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
   rw 27 q2 ∷
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
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q6 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q6 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q6 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
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
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乑") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乑") ∷
   rw 27 q6 ∷
   rw 49 q9 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q2 ∷
   re 51 3 (ℓ "乑") ∷
   re 51 1 (ℓ "乏丼临丼乏") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q3 ∷
   rw 53 q10 ∷
   rw 52 q5 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q6 ∷
   re 52 5 (ℓ "乑") ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw 54 q6 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q9 ∷
   rw 48 q9 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q2 ∷
   re 50 3 (ℓ "乑") ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q3 ∷
   rw 52 q10 ∷
   rw 51 q5 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q6 ∷
   re 51 5 (ℓ "乑") ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q6 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q9 ∷
   rw 47 q1 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q6 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q6 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q1 ∷
   rw 46 q9 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q2 ∷
   re 48 3 (ℓ "乑") ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q3 ∷
   rw 50 q10 ∷
   rw 49 q5 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q6 ∷
   re 49 5 (ℓ "乑") ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw 51 q6 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q9 ∷
   rw 45 q1 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q6 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q6 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q1 ∷
   rw 44 q1 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   rw 47 q5 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q6 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q6 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q1 ∷
   rw 43 q11 ∷
   rw 42 q1 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q2 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   rw 45 q5 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q6 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q6 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q6 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q6 ∷
   re 42 3 (ℓ "乓") ∷
   rw 43 q1 ∷
   rw 40 q1 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q6 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q6 ∷
   re 41 3 (ℓ "乓") ∷
   rw 42 q1 ∷
   rw 39 q1 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q6 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q6 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q1 ∷
   rw 38 q1 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乓") ∷ []) Eq.refl
