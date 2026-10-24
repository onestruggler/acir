{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D225 (W : Ws) where

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
  q1 = wE 555 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 629 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 113 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q12 : Eqn
  q12 = wE 114 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 630 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q18 : Eqn
  q18 = wE 673 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part7: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧両丵両両乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乆並乏丶乏丘並中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘丧丧丧乄丧丧両丵両両乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乆並乏丶乏丘並中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 35 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q3 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q4 ∷
   rw 70 q5 ∷
   rw⁻ 69 q4 ∷
   re 70 3 (ℓ "丽") ∷
   rw 70 q6 ∷
   rw 69 q3 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q4 ∷
   rw 71 q7 ∷
   rw 72 q4 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q8 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q9 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q10 ∷
   rw 72 q11 ∷
   rw 71 q12 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q13 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q2 ∷
   rw⁻ 72 q3 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q4 ∷
   rw 72 q5 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q6 ∷
   rw 71 q3 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q4 ∷
   rw 73 q7 ∷
   rw 74 q4 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q8 ∷
   rw 70 q2 ∷
   rw⁻ 69 q3 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (ℓ "丽") ∷
   rw 69 q6 ∷
   rw 68 q3 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q4 ∷
   rw 70 q7 ∷
   rw 71 q4 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q8 ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q9 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q10 ∷
   rw 71 q11 ∷
   rw 70 q12 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q13 ∷
   re 70 5 (ℓ "中") ∷
   rw 72 q2 ∷
   rw⁻ 71 q3 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q4 ∷
   rw 71 q5 ∷
   rw⁻ 70 q4 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q6 ∷
   rw 70 q3 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q4 ∷
   rw 72 q7 ∷
   rw 73 q4 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q8 ∷
   rw 69 q2 ∷
   rw⁻ 68 q3 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw⁻ 69 q4 ∷
   rw 68 q14 ∷
   rw⁻ 67 q4 ∷
   re 68 3 (ℓ "乔") ∷
   rw 68 q15 ∷
   rw 67 q3 ∷
   re 69 1 (ℓ "乏乇乏") ∷
   rw 68 q4 ∷
   rw 69 q16 ∷
   rw 70 q4 ∷
   re 68 3 (ℓ "乑") ∷
   rw 69 q8 ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q9 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q10 ∷
   rw 70 q17 ∷
   rw 69 q12 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q13 ∷
   re 69 5 (ℓ "乑") ∷
   rw 71 q2 ∷
   rw⁻ 70 q3 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q4 ∷
   rw 70 q14 ∷
   rw⁻ 69 q4 ∷
   re 70 3 (ℓ "乔") ∷
   rw 70 q15 ∷
   rw 69 q3 ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q4 ∷
   rw 71 q16 ∷
   rw 72 q4 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q8 ∷
   rw 68 q2 ∷
   rw⁻ 67 q3 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q6 ∷
   rw 66 q3 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q4 ∷
   rw 68 q7 ∷
   rw 69 q4 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q8 ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q9 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q10 ∷
   rw 69 q11 ∷
   rw 68 q12 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q13 ∷
   re 68 5 (ℓ "中") ∷
   rw 70 q2 ∷
   rw⁻ 69 q3 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (ℓ "丽") ∷
   rw 69 q6 ∷
   rw 68 q3 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q4 ∷
   rw 70 q7 ∷
   rw 71 q4 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q8 ∷
   rw 67 q2 ∷
   rw⁻ 66 q3 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q4 ∷
   rw 66 q5 ∷
   rw⁻ 65 q4 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q6 ∷
   rw 65 q3 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q4 ∷
   rw 67 q7 ∷
   rw 68 q4 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q8 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q9 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q10 ∷
   rw 68 q11 ∷
   rw 67 q12 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q13 ∷
   re 67 5 (ℓ "中") ∷
   rw 69 q2 ∷
   rw⁻ 68 q3 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q4 ∷
   rw 68 q5 ∷
   rw⁻ 67 q4 ∷
   re 68 3 (ℓ "丽") ∷
   rw 68 q6 ∷
   rw 67 q3 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q4 ∷
   rw 69 q7 ∷
   rw 70 q4 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q8 ∷
   rw 66 q2 ∷
   rw⁻ 65 q3 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q4 ∷
   rw 65 q5 ∷
   rw⁻ 64 q4 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q6 ∷
   rw 64 q3 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q4 ∷
   rw 66 q7 ∷
   rw 67 q4 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q8 ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q9 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q10 ∷
   rw 67 q11 ∷
   rw 66 q12 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q13 ∷
   re 66 5 (ℓ "中") ∷
   rw 68 q2 ∷
   rw⁻ 67 q3 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q6 ∷
   rw 66 q3 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q4 ∷
   rw 68 q7 ∷
   rw 69 q4 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q8 ∷
   rw 63 q18 ∷
   rw 64 q2 ∷
   rw⁻ 63 q3 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q4 ∷
   rw 63 q5 ∷
   rw⁻ 62 q4 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q6 ∷
   rw 62 q3 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q4 ∷
   rw 64 q7 ∷
   rw 65 q4 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q8 ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q9 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q10 ∷
   rw 65 q11 ∷
   rw 64 q12 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q13 ∷
   re 64 5 (ℓ "中") ∷
   rw 66 q2 ∷
   rw⁻ 65 q3 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q4 ∷
   rw 65 q5 ∷
   rw⁻ 64 q4 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q6 ∷
   rw 64 q3 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q4 ∷
   rw 66 q7 ∷
   rw 67 q4 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q8 ∷
   rw 63 q2 ∷
   rw⁻ 62 q3 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q4 ∷
   rw 62 q5 ∷
   rw⁻ 61 q4 ∷
   re 62 3 (ℓ "丽") ∷
   rw 62 q6 ∷
   rw 61 q3 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q4 ∷
   rw 63 q7 ∷
   rw 64 q4 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q8 ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q9 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q10 ∷
   rw 64 q11 ∷
   rw 63 q12 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q13 ∷
   re 63 5 (ℓ "中") ∷
   rw 65 q2 ∷
   rw⁻ 64 q3 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q4 ∷
   rw 64 q5 ∷
   rw⁻ 63 q4 ∷
   re 64 3 (ℓ "丽") ∷
   rw 64 q6 ∷
   rw 63 q3 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q4 ∷
   rw 65 q7 ∷
   rw 66 q4 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q8 ∷
   rw 62 q2 ∷
   rw⁻ 61 q3 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q4 ∷
   rw 61 q5 ∷
   rw⁻ 60 q4 ∷
   re 61 3 (ℓ "丽") ∷
   rw 61 q6 ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q4 ∷
   rw 62 q7 ∷
   rw 63 q4 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q8 ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q9 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q10 ∷
   rw 63 q11 ∷
   rw 62 q12 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q13 ∷
   re 62 5 (ℓ "中") ∷
   rw 64 q2 ∷
   rw⁻ 63 q3 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q4 ∷
   rw 63 q5 ∷
   rw⁻ 62 q4 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q6 ∷
   rw 62 q3 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q4 ∷
   rw 64 q7 ∷
   rw 65 q4 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q8 ∷
   rw 61 q2 ∷
   rw⁻ 60 q3 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q4 ∷
   rw 60 q5 ∷
   rw⁻ 59 q4 ∷
   re 60 3 (ℓ "丽") ∷
   rw 60 q6 ∷
   rw 59 q3 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q4 ∷
   rw 61 q7 ∷
   rw 62 q4 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q8 ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q9 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q10 ∷
   rw 62 q11 ∷
   rw 61 q12 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q13 ∷
   re 61 5 (ℓ "中") ∷
   rw 63 q2 ∷
   rw⁻ 62 q3 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q4 ∷
   rw 62 q5 ∷
   rw⁻ 61 q4 ∷
   re 62 3 (ℓ "丽") ∷
   rw 62 q6 ∷
   rw 61 q3 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q4 ∷
   rw 63 q7 ∷
   rw 64 q4 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q8 ∷
   rw 60 q2 ∷
   rw⁻ 59 q3 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q4 ∷
   rw 59 q5 ∷
   rw⁻ 58 q4 ∷
   re 59 3 (ℓ "丽") ∷
   rw 59 q6 ∷
   rw 58 q3 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q4 ∷
   rw 60 q7 ∷
   rw 61 q4 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q8 ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q9 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q10 ∷
   rw 61 q11 ∷
   rw 60 q12 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q13 ∷
   re 60 5 (ℓ "中") ∷
   rw 62 q2 ∷
   rw⁻ 61 q3 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q4 ∷
   rw 61 q5 ∷
   rw⁻ 60 q4 ∷
   re 61 3 (ℓ "丽") ∷
   rw 61 q6 ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q4 ∷
   rw 62 q7 ∷
   rw 63 q4 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q8 ∷
   rw 59 q2 ∷
   rw⁻ 58 q3 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q4 ∷
   rw 58 q5 ∷
   rw⁻ 57 q4 ∷
   re 58 3 (ℓ "丽") ∷
   rw 58 q6 ∷
   rw 57 q3 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q4 ∷
   rw 59 q7 ∷
   rw 60 q4 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q8 ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q9 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q10 ∷
   rw 60 q11 ∷
   rw 59 q12 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q13 ∷
   re 59 5 (ℓ "中") ∷
   rw 61 q2 ∷
   rw⁻ 60 q3 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q4 ∷
   rw 60 q5 ∷
   rw⁻ 59 q4 ∷
   re 60 3 (ℓ "丽") ∷
   rw 60 q6 ∷
   rw 59 q3 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q4 ∷
   rw 61 q7 ∷
   rw 62 q4 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q8 ∷
   rw 58 q2 ∷
   rw⁻ 57 q3 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q4 ∷
   rw 57 q5 ∷
   rw⁻ 56 q4 ∷
   re 57 3 (ℓ "丽") ∷
   rw 57 q6 ∷
   rw 56 q3 ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q4 ∷
   rw 58 q7 ∷
   rw 59 q4 ∷
   re 57 3 (ℓ "中") ∷
   rw 58 q8 ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q9 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q10 ∷
   rw 59 q11 ∷
   rw 58 q12 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q13 ∷
   re 58 5 (ℓ "中") ∷
   rw 60 q2 ∷
   rw⁻ 59 q3 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q4 ∷
   rw 59 q5 ∷
   rw⁻ 58 q4 ∷ []) Eq.refl
