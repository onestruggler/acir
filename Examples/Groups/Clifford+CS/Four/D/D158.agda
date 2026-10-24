{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D158 (W : Ws) where

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
  q1 = wE 31 W
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
  q20 = wE 488 W
  q21 : Eqn
  q21 = wE 76 W
  q22 : Eqn
  q22 = wE 137 W
  q23 : Eqn
  q23 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乆丘中並並中乌中中乑中乑乑丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧乄丧乄乄乌乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丷么丷丷丘並丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乆丘中並並中乌中中乑中乑乑丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧乄丧乄乄乌乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丷么丷丷丘並丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 45 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q1 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q8 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q9 ∷
   rw 43 q10 ∷
   rw 42 q11 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q12 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q6 ∷
   rw 42 q3 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q4 ∷
   rw 44 q7 ∷
   rw 45 q4 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q8 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q12 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q2 ∷
   rw⁻ 42 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q4 ∷
   rw 43 q7 ∷
   rw 44 q4 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q3 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q6 ∷
   rw 38 q3 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q4 ∷
   rw 40 q7 ∷
   rw 41 q4 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q8 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q9 ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q12 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q4 ∷
   rw 39 q7 ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q12 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q1 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q13 ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "乔") ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q8 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q9 ∷
   rw 38 q18 ∷
   rw 37 q11 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q12 ∷
   re 37 5 (ℓ "乑") ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q15 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q16 ∷
   rw 37 q3 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q4 ∷
   rw 39 q17 ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q3 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q4 ∷
   rw 35 q5 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q6 ∷
   rw 34 q3 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q4 ∷
   rw 36 q7 ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q8 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q9 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q12 ∷
   re 36 5 (ℓ "中") ∷
   rw 38 q2 ∷
   rw⁻ 37 q3 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (ℓ "丽") ∷
   rw 37 q6 ∷
   rw 36 q3 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q4 ∷
   rw 38 q7 ∷
   rw 39 q4 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q1 ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q6 ∷
   rw 33 q3 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q4 ∷
   rw 35 q7 ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q8 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q9 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q12 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q5 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q6 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q4 ∷
   rw 37 q7 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q4 ∷
   rw 33 q5 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q6 ∷
   rw 32 q3 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q4 ∷
   rw 34 q7 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q8 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q9 ∷
   rw 35 q10 ∷
   rw 34 q11 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q12 ∷
   re 34 5 (ℓ "中") ∷
   rw 36 q2 ∷
   rw⁻ 35 q3 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q4 ∷
   rw 35 q5 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q6 ∷
   rw 34 q3 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q4 ∷
   rw 36 q7 ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q1 ∷
   rw⁻ 31 q13 ∷
   rw⁻ 32 q14 ∷
   rw⁻ 33 q13 ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q15 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q16 ∷
   rw 30 q3 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q4 ∷
   rw 32 q17 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q9 ∷
   rw 33 q18 ∷
   rw 32 q11 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q12 ∷
   re 32 5 (ℓ "乑") ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q4 ∷
   rw 33 q15 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (ℓ "乔") ∷
   rw 33 q16 ∷
   rw 32 q3 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q4 ∷
   rw 34 q17 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q1 ∷
   rw⁻ 29 q13 ∷
   rw⁻ 30 q14 ∷
   rw⁻ 31 q13 ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q4 ∷
   rw 29 q15 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q16 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q4 ∷
   rw 30 q17 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q9 ∷
   rw 31 q18 ∷
   rw 30 q11 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q15 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q16 ∷
   rw 30 q3 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q4 ∷
   rw 32 q17 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q1 ∷
   rw 27 q19 ∷
   rw 21 q20 ∷
   rw 59 q2 ∷
   rw⁻ 58 q3 ∷
   rw 57 q21 ∷
   rw 56 q21 ∷
   rw 55 q22 ∷
   rw 54 q21 ∷
   rw⁻ 53 q3 ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw⁻ 54 q4 ∷
   rw 53 q15 ∷
   rw⁻ 52 q4 ∷
   re 53 3 (ℓ "乔") ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw⁻ 53 q4 ∷
   rw 52 q15 ∷
   rw⁻ 51 q4 ∷
   re 52 3 (ℓ "乔") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q4 ∷
   rw 51 q5 ∷
   rw⁻ 50 q4 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw⁻ 51 q4 ∷
   rw 50 q15 ∷
   rw⁻ 49 q4 ∷
   re 50 3 (ℓ "乔") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q4 ∷
   rw 49 q5 ∷
   rw⁻ 48 q4 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q4 ∷
   rw 48 q5 ∷
   rw⁻ 47 q4 ∷
   re 48 3 (ℓ "丽") ∷
   rw⁻ 46 q23 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q4 ∷
   rw 46 q5 ∷
   rw⁻ 45 q4 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q4 ∷
   rw 45 q5 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q4 ∷
   rw 44 q5 ∷
   rw⁻ 43 q4 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "丽") ∷
   rw⁻ 39 q24 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q4 ∷
   rw 39 q15 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (ℓ "乔") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q5 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "丽") ∷
   rw⁻ 34 q24 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q15 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乔") ∷
   rw⁻ 32 q24 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q4 ∷ []) Eq.refl
