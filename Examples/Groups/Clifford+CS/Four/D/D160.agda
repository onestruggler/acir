{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D160 (W : Ws) where

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
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 140 W
  q9 : Eqn
  q9 = wE 630 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 629 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = wE 673 W
  q18 : Eqn
  q18 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q19 : Eqn
  q19 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part6: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part6 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中丘乏丼临丼乓乏丘乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中並丽丘並乆丘中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part6 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中丘乏丼临丼乓乏丘乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中並丽丘並乆丘中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 70 q1 ∷
   rw 69 q2 ∷
   rw 68 q3 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q4 ∷
   re 68 5 (ℓ "乑") ∷
   rw 70 q5 ∷
   rw⁻ 69 q6 ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw⁻ 70 q7 ∷
   rw 69 q8 ∷
   rw⁻ 68 q7 ∷
   re 69 3 (ℓ "乔") ∷
   rw 69 q9 ∷
   rw 68 q6 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q7 ∷
   rw 70 q10 ∷
   rw 71 q7 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q11 ∷
   rw 67 q5 ∷
   rw⁻ 66 q6 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q7 ∷
   rw 66 q12 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q13 ∷
   rw 65 q6 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q11 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q15 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q1 ∷
   rw 68 q16 ∷
   rw 67 q3 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q4 ∷
   re 67 5 (ℓ "中") ∷
   rw 69 q5 ∷
   rw⁻ 68 q6 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q7 ∷
   rw 68 q12 ∷
   rw⁻ 67 q7 ∷
   re 68 3 (ℓ "丽") ∷
   rw 68 q13 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q7 ∷
   rw 69 q14 ∷
   rw 70 q7 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q11 ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (ℓ "乏乄乏") ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (ℓ "乔") ∷
   rw 65 q9 ∷
   rw 64 q6 ∷
   re 66 1 (ℓ "乏乇乏") ∷
   rw 65 q7 ∷
   rw 66 q10 ∷
   rw 67 q7 ∷
   re 65 3 (ℓ "乑") ∷
   rw 66 q11 ∷
   re 65 1 (ℓ "乏丼临丼乏") ∷
   rw 71 q15 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q1 ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q4 ∷
   re 66 5 (ℓ "乑") ∷
   rw 68 q5 ∷
   rw⁻ 67 q6 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q7 ∷
   rw 67 q8 ∷
   rw⁻ 66 q7 ∷
   re 67 3 (ℓ "乔") ∷
   rw 67 q9 ∷
   rw 66 q6 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q7 ∷
   rw 68 q10 ∷
   rw 69 q7 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q11 ∷
   rw 65 q5 ∷
   rw⁻ 64 q6 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q7 ∷
   rw 64 q12 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (ℓ "丽") ∷
   rw 64 q13 ∷
   rw 63 q6 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q7 ∷
   rw 65 q14 ∷
   rw 66 q7 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q11 ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q15 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q1 ∷
   rw 66 q16 ∷
   rw 65 q3 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q4 ∷
   re 65 5 (ℓ "中") ∷
   rw 67 q5 ∷
   rw⁻ 66 q6 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q7 ∷
   rw 66 q12 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q13 ∷
   rw 65 q6 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q11 ∷
   rw 64 q5 ∷
   rw⁻ 63 q6 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q7 ∷
   rw 63 q12 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q13 ∷
   rw 62 q6 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q7 ∷
   rw 64 q14 ∷
   rw 65 q7 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q11 ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q15 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q1 ∷
   rw 65 q16 ∷
   rw 64 q3 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q4 ∷
   re 64 5 (ℓ "中") ∷
   rw 66 q5 ∷
   rw⁻ 65 q6 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q7 ∷
   rw 65 q12 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q13 ∷
   rw 64 q6 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q7 ∷
   rw 66 q14 ∷
   rw 67 q7 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q11 ∷
   rw 61 q17 ∷
   rw 62 q5 ∷
   rw⁻ 61 q6 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q7 ∷
   rw 61 q12 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (ℓ "丽") ∷
   rw 61 q13 ∷
   rw 60 q6 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q11 ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q15 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q1 ∷
   rw 63 q16 ∷
   rw 62 q3 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q4 ∷
   re 62 5 (ℓ "中") ∷
   rw 64 q5 ∷
   rw⁻ 63 q6 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q7 ∷
   rw 63 q12 ∷
   rw⁻ 62 q7 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q13 ∷
   rw 62 q6 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q7 ∷
   rw 64 q14 ∷
   rw 65 q7 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q11 ∷
   rw 61 q5 ∷
   rw⁻ 60 q6 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q7 ∷
   rw 60 q12 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (ℓ "丽") ∷
   rw 60 q13 ∷
   rw 59 q6 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q7 ∷
   rw 61 q14 ∷
   rw 62 q7 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q11 ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q15 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q1 ∷
   rw 62 q16 ∷
   rw 61 q3 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q4 ∷
   re 61 5 (ℓ "中") ∷
   rw 63 q5 ∷
   rw⁻ 62 q6 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q7 ∷
   rw 62 q12 ∷
   rw⁻ 61 q7 ∷
   re 62 3 (ℓ "丽") ∷
   rw 62 q13 ∷
   rw 61 q6 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q7 ∷
   rw 63 q14 ∷
   rw 64 q7 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q11 ∷
   rw 60 q5 ∷
   rw⁻ 59 q6 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q7 ∷
   rw 59 q12 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (ℓ "丽") ∷
   rw 59 q13 ∷
   rw 58 q6 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q7 ∷
   rw 60 q14 ∷
   rw 61 q7 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q11 ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q15 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q1 ∷
   rw 61 q16 ∷
   rw 60 q3 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q4 ∷
   re 60 5 (ℓ "中") ∷
   rw 62 q5 ∷
   rw⁻ 61 q6 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q7 ∷
   rw 61 q12 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (ℓ "丽") ∷
   rw 61 q13 ∷
   rw 60 q6 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q11 ∷
   rw 59 q5 ∷
   rw⁻ 58 q6 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q7 ∷
   rw 58 q12 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (ℓ "丽") ∷
   rw 58 q13 ∷
   rw 57 q6 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q7 ∷
   rw 59 q14 ∷
   rw 60 q7 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q11 ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q15 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q1 ∷
   rw 60 q16 ∷
   rw 59 q3 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q4 ∷
   re 59 5 (ℓ "中") ∷
   rw 61 q5 ∷
   rw⁻ 60 q6 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q7 ∷
   rw 60 q12 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (ℓ "丽") ∷
   rw 60 q13 ∷
   rw 59 q6 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q7 ∷
   rw 61 q14 ∷
   rw 62 q7 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q11 ∷
   rw 58 q5 ∷
   rw⁻ 57 q6 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q7 ∷
   rw 57 q12 ∷
   rw⁻ 56 q7 ∷
   re 57 3 (ℓ "丽") ∷
   rw 57 q13 ∷
   rw 56 q6 ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q7 ∷
   rw 58 q14 ∷
   rw 59 q7 ∷
   re 57 3 (ℓ "中") ∷
   rw 58 q11 ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q15 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q1 ∷
   rw 59 q16 ∷
   rw 58 q3 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q4 ∷
   re 58 5 (ℓ "中") ∷
   rw 60 q5 ∷
   rw⁻ 59 q6 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q7 ∷
   rw 59 q12 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (ℓ "丽") ∷
   rw 59 q13 ∷
   rw 58 q6 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q7 ∷
   rw 60 q14 ∷
   rw 61 q7 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q11 ∷
   rw 57 q5 ∷
   rw⁻ 56 q6 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q7 ∷
   rw 56 q12 ∷
   rw⁻ 55 q7 ∷
   re 56 3 (ℓ "丽") ∷
   rw 56 q13 ∷
   rw 55 q6 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q7 ∷
   rw 57 q14 ∷
   rw 58 q7 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q11 ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q15 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q1 ∷
   rw 58 q16 ∷
   rw 57 q3 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q4 ∷
   re 57 5 (ℓ "中") ∷
   rw 59 q5 ∷
   rw⁻ 58 q6 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q7 ∷
   rw 58 q12 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (ℓ "丽") ∷
   rw 58 q13 ∷
   rw 57 q6 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q7 ∷
   rw 59 q14 ∷
   rw 60 q7 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q11 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q18 ∷
   rw 55 q5 ∷
   rw⁻ 54 q6 ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw⁻ 55 q7 ∷
   rw 54 q8 ∷
   rw⁻ 53 q7 ∷
   re 54 3 (ℓ "乔") ∷
   rw 54 q9 ∷
   rw 53 q6 ∷
   re 55 1 (ℓ "乏乇乏") ∷
   rw 54 q7 ∷
   rw 55 q10 ∷
   rw 56 q7 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q11 ∷
   re 54 1 (ℓ "乏丼临丼乏") ∷
   rw 60 q15 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q4 ∷
   re 55 5 (ℓ "乑") ∷
   rw 57 q5 ∷
   rw⁻ 56 q6 ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw⁻ 57 q7 ∷
   rw 56 q8 ∷
   rw⁻ 55 q7 ∷
   re 56 3 (ℓ "乔") ∷
   rw 56 q9 ∷
   rw 55 q6 ∷
   re 57 1 (ℓ "乏乇乏") ∷
   rw 56 q7 ∷
   rw 57 q10 ∷
   rw 58 q7 ∷
   re 56 3 (ℓ "乑") ∷
   rw 57 q11 ∷
   rw 54 q5 ∷
   rw⁻ 53 q6 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q7 ∷
   rw 53 q12 ∷
   rw⁻ 52 q7 ∷
   re 53 3 (ℓ "丽") ∷
   rw 53 q13 ∷
   rw 52 q6 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q7 ∷
   rw 54 q14 ∷
   rw 55 q7 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q11 ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q15 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q1 ∷
   rw 55 q16 ∷
   rw 54 q3 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q4 ∷
   re 54 5 (ℓ "中") ∷
   rw 56 q5 ∷
   rw⁻ 55 q6 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q7 ∷
   rw 55 q12 ∷
   rw⁻ 54 q7 ∷
   re 55 3 (ℓ "丽") ∷
   rw 55 q13 ∷
   rw 54 q6 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q7 ∷
   rw 56 q14 ∷
   rw 57 q7 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q11 ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q7 ∷
   rw 52 q12 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (ℓ "丽") ∷ []) Eq.refl
