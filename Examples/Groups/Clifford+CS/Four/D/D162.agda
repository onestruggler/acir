{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D162 (W : Ws) where

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
  q2 = wE 31 W
  q3 : Eqn
  q3 = wE 5 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 629 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 113 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 114 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 673 W
  q14 : Eqn
  q14 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q15 : Eqn
  q15 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 630 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part8: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乆丘乏丧並乏並乑中乑乑丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌丘乏丼临乖丼乏丘业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乆丘乏丧並乏並乑中乑乑丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌丘乏丼临乖丼乏丘业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丨丨丘丘丨丨丨丘")
  (rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q2 ∷
   rw 78 q3 ∷
   rw⁻ 77 q4 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q1 ∷
   rw 77 q5 ∷
   rw⁻ 76 q1 ∷
   re 77 3 (ℓ "丽") ∷
   rw 77 q6 ∷
   rw 76 q4 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q1 ∷
   rw 78 q7 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q2 ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q8 ∷
   re 81 3 (ℓ "乓") ∷
   rw 80 q9 ∷
   rw 79 q10 ∷
   rw 78 q11 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q12 ∷
   re 78 5 (ℓ "中") ∷
   rw 80 q3 ∷
   rw⁻ 79 q4 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q1 ∷
   rw 79 q5 ∷
   rw⁻ 78 q1 ∷
   re 79 3 (ℓ "丽") ∷
   rw 79 q6 ∷
   rw 78 q4 ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q1 ∷
   rw 80 q7 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   rw 80 q2 ∷
   rw 75 q13 ∷
   rw 76 q3 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q1 ∷
   rw 75 q5 ∷
   rw⁻ 74 q1 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q6 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q1 ∷
   rw 76 q7 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q2 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q9 ∷
   rw 77 q10 ∷
   rw 76 q11 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q12 ∷
   re 76 5 (ℓ "中") ∷
   rw 78 q3 ∷
   rw⁻ 77 q4 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q1 ∷
   rw 77 q5 ∷
   rw⁻ 76 q1 ∷
   re 77 3 (ℓ "丽") ∷
   rw 77 q6 ∷
   rw 76 q4 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q1 ∷
   rw 78 q7 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q2 ∷
   rw 75 q3 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q1 ∷
   rw 74 q5 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q6 ∷
   rw 73 q4 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q1 ∷
   rw 75 q7 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q2 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q9 ∷
   rw 76 q10 ∷
   rw 75 q11 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q12 ∷
   re 75 5 (ℓ "中") ∷
   rw 77 q3 ∷
   rw⁻ 76 q4 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q1 ∷
   rw 76 q5 ∷
   rw⁻ 75 q1 ∷
   re 76 3 (ℓ "丽") ∷
   rw 76 q6 ∷
   rw 75 q4 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q1 ∷
   rw 77 q7 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q2 ∷
   rw 74 q3 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q1 ∷
   rw 73 q5 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q6 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q1 ∷
   rw 74 q7 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q2 ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q9 ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q12 ∷
   re 74 5 (ℓ "中") ∷
   rw 76 q3 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q1 ∷
   rw 75 q5 ∷
   rw⁻ 74 q1 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q6 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q1 ∷
   rw 76 q7 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q2 ∷
   rw 73 q3 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q1 ∷
   rw 72 q5 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q6 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q1 ∷
   rw 73 q7 ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q2 ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q9 ∷
   rw 74 q10 ∷
   rw 73 q11 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q12 ∷
   re 73 5 (ℓ "中") ∷
   rw 75 q3 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q1 ∷
   rw 74 q5 ∷
   rw⁻ 73 q1 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q6 ∷
   rw 73 q4 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q1 ∷
   rw 75 q7 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q2 ∷
   rw 72 q3 ∷
   rw⁻ 71 q4 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q1 ∷
   rw 71 q5 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q6 ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q1 ∷
   rw 72 q7 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q2 ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q8 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q9 ∷
   rw 73 q10 ∷
   rw 72 q11 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q12 ∷
   re 72 5 (ℓ "中") ∷
   rw 74 q3 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q1 ∷
   rw 73 q5 ∷
   rw⁻ 72 q1 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q6 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q1 ∷
   rw 74 q7 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q2 ∷
   rw 71 q3 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q5 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "丽") ∷
   rw 70 q6 ∷
   rw 69 q4 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q1 ∷
   rw 71 q7 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q2 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q9 ∷
   rw 72 q10 ∷
   rw 71 q11 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q12 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q3 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q1 ∷
   rw 72 q5 ∷
   rw⁻ 71 q1 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q6 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q1 ∷
   rw 73 q7 ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q2 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 69 q15 ∷
   rw⁻ 70 q14 ∷
   rw 69 q3 ∷
   rw⁻ 68 q4 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw⁻ 69 q1 ∷
   rw 68 q16 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (ℓ "乔") ∷
   rw 68 q17 ∷
   rw 67 q4 ∷
   re 69 1 (ℓ "乏乇乏") ∷
   rw 68 q1 ∷
   rw 69 q18 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "乑") ∷
   rw 69 q2 ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q8 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q9 ∷
   rw 70 q19 ∷
   rw 69 q11 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q12 ∷
   re 69 5 (ℓ "乑") ∷
   rw 71 q3 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q16 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "乔") ∷
   rw 70 q17 ∷
   rw 69 q4 ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q1 ∷
   rw 71 q18 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q2 ∷
   rw 68 q3 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q5 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q6 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q1 ∷
   rw 68 q7 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q2 ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q8 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q9 ∷
   rw 69 q10 ∷
   rw 68 q11 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q12 ∷
   re 68 5 (ℓ "中") ∷
   rw 70 q3 ∷
   rw⁻ 69 q4 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q1 ∷
   rw 69 q5 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (ℓ "丽") ∷
   rw 69 q6 ∷
   rw 68 q4 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q1 ∷
   rw 70 q7 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q2 ∷
   rw 67 q3 ∷
   rw⁻ 66 q4 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q5 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q6 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q1 ∷
   rw 67 q7 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q2 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q9 ∷
   rw 68 q10 ∷
   rw 67 q11 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q12 ∷
   re 67 5 (ℓ "中") ∷
   rw 69 q3 ∷
   rw⁻ 68 q4 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q1 ∷
   rw 68 q5 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (ℓ "丽") ∷
   rw 68 q6 ∷
   rw 67 q4 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q7 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q2 ∷
   rw 66 q3 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q5 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q6 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q1 ∷
   rw 66 q7 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q2 ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q8 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q9 ∷
   rw 67 q10 ∷
   rw 66 q11 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q12 ∷
   re 66 5 (ℓ "中") ∷
   rw 68 q3 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q5 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q6 ∷
   rw 66 q4 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q1 ∷
   rw 68 q7 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q2 ∷
   rw⁻ 63 q14 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 65 q14 ∷
   rw 64 q3 ∷
   rw⁻ 63 q4 ∷
   re 62 1 (ℓ "乏乄乏") ∷
   rw⁻ 64 q1 ∷
   rw 63 q16 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (ℓ "乔") ∷
   rw 63 q17 ∷
   rw 62 q4 ∷
   re 64 1 (ℓ "乏乇乏") ∷
   rw 63 q1 ∷
   rw 64 q18 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q2 ∷
   re 63 1 (ℓ "乏丼临丼乏") ∷
   rw 69 q8 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q9 ∷
   rw 65 q19 ∷
   rw 64 q11 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q12 ∷
   re 64 5 (ℓ "乑") ∷
   rw 66 q3 ∷
   rw⁻ 65 q4 ∷
   re 64 1 (ℓ "乏乄乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q16 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "乔") ∷
   rw 65 q17 ∷
   rw 64 q4 ∷
   re 66 1 (ℓ "乏乇乏") ∷
   rw 65 q1 ∷
   rw 66 q18 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "乑") ∷
   rw 66 q2 ∷
   rw⁻ 61 q14 ∷
   rw⁻ 62 q15 ∷
   rw⁻ 63 q14 ∷
   rw 62 q3 ∷
   rw⁻ 61 q4 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw⁻ 62 q1 ∷
   rw 61 q16 ∷
   rw⁻ 60 q1 ∷
   re 61 3 (ℓ "乔") ∷
   rw 61 q17 ∷
   rw 60 q4 ∷
   re 62 1 (ℓ "乏乇乏") ∷
   rw 61 q1 ∷
   rw 62 q18 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乑") ∷
   rw 62 q2 ∷
   re 61 1 (ℓ "乏丼临丼乏") ∷
   rw 67 q8 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q9 ∷ []) Eq.refl
