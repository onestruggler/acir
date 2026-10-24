{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D228 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 113 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = wE 114 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = wE 673 W
  q20 : Eqn
  q20 = wE 557 W
  q21 : Eqn
  q21 = wE 76 W
  q22 : Eqn
  q22 = wE 137 W
  q23 : Eqn
  q23 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part10: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part10 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧丧乄丧丧乌中中中中中中乑业中中乏丧乏並丘並乆丘中中中中中中乌中中中乑中中丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧丧乄丧丧乌中中並乏丶乏丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丷么丷丷丘並丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part10 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧丧乄丧丧乌中中中中中中乑业中中乏丧乏並丘並乆丘中中中中中中乌中中中乑中中丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧丧乄丧丧乌中中並乏丶乏丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丷么丷丷丘並丘丨丨丨丘")
  (rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q6 ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q7 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q8 ∷
   rw 73 q9 ∷
   rw 72 q10 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q11 ∷
   re 72 5 (ℓ "中") ∷
   rw 74 q12 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q1 ∷
   rw 74 q5 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q6 ∷
   rw 71 q12 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q2 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "丽") ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q1 ∷
   rw 71 q5 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q6 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q7 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q8 ∷
   rw 72 q9 ∷
   rw 71 q10 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q11 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q12 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q1 ∷
   rw 73 q5 ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q6 ∷
   rw 70 q12 ∷
   rw⁻ 69 q4 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q1 ∷
   rw 69 q2 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (ℓ "丽") ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q1 ∷
   rw 70 q5 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q6 ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q7 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q8 ∷
   rw 71 q9 ∷
   rw 70 q10 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q11 ∷
   re 70 5 (ℓ "中") ∷
   rw 72 q12 ∷
   rw⁻ 71 q4 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q6 ∷
   rw⁻ 67 q13 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 69 q13 ∷
   rw 68 q12 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q15 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "乔") ∷
   rw 67 q16 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q1 ∷
   rw 68 q17 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q6 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 73 q7 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q8 ∷
   rw 69 q18 ∷
   rw 68 q10 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q11 ∷
   re 68 5 (ℓ "乑") ∷
   rw 70 q12 ∷
   rw⁻ 69 q4 ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw⁻ 70 q1 ∷
   rw 69 q15 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (ℓ "乔") ∷
   rw 69 q16 ∷
   rw 68 q4 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q1 ∷
   rw 70 q17 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q6 ∷
   rw 67 q12 ∷
   rw⁻ 66 q4 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q6 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q7 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q8 ∷
   rw 68 q9 ∷
   rw 67 q10 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q11 ∷
   re 67 5 (ℓ "中") ∷
   rw 69 q12 ∷
   rw⁻ 68 q4 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q1 ∷
   rw 68 q2 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (ℓ "丽") ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q5 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q6 ∷
   rw 66 q12 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q1 ∷
   rw 66 q5 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q6 ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q7 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q8 ∷
   rw 67 q9 ∷
   rw 66 q10 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q11 ∷
   re 66 5 (ℓ "中") ∷
   rw 68 q12 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q1 ∷
   rw 68 q5 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q6 ∷
   rw 65 q12 ∷
   rw⁻ 64 q4 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "丽") ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q6 ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q7 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q11 ∷
   re 65 5 (ℓ "中") ∷
   rw 67 q12 ∷
   rw⁻ 66 q4 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q6 ∷
   rw 64 q12 ∷
   rw⁻ 63 q4 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q1 ∷
   rw 63 q2 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q1 ∷
   rw 64 q5 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q6 ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q7 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q8 ∷
   rw 65 q9 ∷
   rw 64 q10 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q11 ∷
   re 64 5 (ℓ "中") ∷
   rw 66 q12 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q1 ∷
   rw 66 q5 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q6 ∷
   rw 63 q12 ∷
   rw⁻ 62 q4 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q1 ∷
   rw 62 q2 ∷
   rw⁻ 61 q1 ∷
   re 62 3 (ℓ "丽") ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q1 ∷
   rw 63 q5 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q6 ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q7 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q8 ∷
   rw 64 q9 ∷
   rw 63 q10 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q11 ∷
   re 63 5 (ℓ "中") ∷
   rw 65 q12 ∷
   rw⁻ 64 q4 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "丽") ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q6 ∷
   rw 62 q12 ∷
   rw⁻ 61 q4 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q1 ∷
   rw 61 q2 ∷
   rw⁻ 60 q1 ∷
   re 61 3 (ℓ "丽") ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q1 ∷
   rw 62 q5 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q6 ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q7 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q8 ∷
   rw 63 q9 ∷
   rw 62 q10 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q11 ∷
   re 62 5 (ℓ "中") ∷
   rw 64 q12 ∷
   rw⁻ 63 q4 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q1 ∷
   rw 63 q2 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q1 ∷
   rw 64 q5 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q6 ∷
   rw 59 q19 ∷
   rw 53 q20 ∷
   rw 93 q12 ∷
   rw⁻ 92 q4 ∷
   rw 91 q21 ∷
   rw 90 q21 ∷
   rw 89 q22 ∷
   rw 88 q21 ∷
   rw⁻ 87 q4 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q1 ∷
   rw 87 q2 ∷
   rw⁻ 86 q1 ∷
   re 87 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q1 ∷
   rw 86 q2 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw⁻ 86 q1 ∷
   rw 85 q15 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (ℓ "乔") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q1 ∷
   rw 84 q2 ∷
   rw⁻ 83 q1 ∷
   re 84 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q1 ∷
   rw 83 q2 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q1 ∷
   rw 82 q2 ∷
   rw⁻ 81 q1 ∷
   re 82 3 (ℓ "丽") ∷
   rw⁻ 80 q23 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q1 ∷
   rw 80 q2 ∷
   rw⁻ 79 q1 ∷
   re 80 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q1 ∷
   rw 79 q2 ∷
   rw⁻ 78 q1 ∷
   re 79 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q1 ∷
   rw 78 q2 ∷
   rw⁻ 77 q1 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q1 ∷
   rw 77 q2 ∷
   rw⁻ 76 q1 ∷
   re 77 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q1 ∷
   rw 76 q2 ∷
   rw⁻ 75 q1 ∷
   re 76 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q1 ∷
   rw 75 q2 ∷
   rw⁻ 74 q1 ∷
   re 75 3 (ℓ "丽") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q1 ∷
   rw 74 q2 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (ℓ "丽") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q1 ∷
   rw 73 q2 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (ℓ "丽") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q1 ∷
   rw 72 q2 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (ℓ "丽") ∷
   rw⁻ 70 q24 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q15 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "乔") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q1 ∷
   rw 69 q2 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q1 ∷
   rw 68 q2 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷ []) Eq.refl
