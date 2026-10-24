{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D163 (W : Ws) where

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
  q1 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q2 : Eqn
  q2 = wE 114 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 140 W
  q8 : Eqn
  q8 = wE 630 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 673 W
  q12 : Eqn
  q12 = wE 488 W
  q13 : Eqn
  q13 = wE 76 W
  q14 : Eqn
  q14 = wE 137 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q17 : Eqn
  q17 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 740 W
  q19 : Eqn
  q19 = wE 29 W
  q20 : Eqn
  q20 = wE 139 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 742 W

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part9: 454 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌丘乏丼临乖丼乏丘业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part9 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌丘乏丼临乖丼乏丘业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 63 q1 ∷
   rw 62 q2 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q3 ∷
   re 62 5 (ℓ "乑") ∷
   rw 64 q4 ∷
   rw⁻ 63 q5 ∷
   re 62 1 (ℓ "乏乄乏") ∷
   rw⁻ 64 q6 ∷
   rw 63 q7 ∷
   rw⁻ 62 q6 ∷
   re 63 3 (ℓ "乔") ∷
   rw 63 q8 ∷
   rw 62 q5 ∷
   re 64 1 (ℓ "乏乇乏") ∷
   rw 63 q6 ∷
   rw 64 q9 ∷
   rw 65 q6 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q10 ∷
   rw 59 q11 ∷
   rw 53 q12 ∷
   rw 91 q4 ∷
   rw⁻ 90 q5 ∷
   rw 89 q13 ∷
   rw 88 q13 ∷
   rw 87 q14 ∷
   rw 86 q13 ∷
   rw⁻ 85 q5 ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw⁻ 86 q6 ∷
   rw 85 q7 ∷
   rw⁻ 84 q6 ∷
   re 85 3 (ℓ "乔") ∷
   re 83 1 (ℓ "乏乄乏") ∷
   rw⁻ 85 q6 ∷
   rw 84 q7 ∷
   rw⁻ 83 q6 ∷
   re 84 3 (ℓ "乔") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q6 ∷
   rw 83 q15 ∷
   rw⁻ 82 q6 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏乄乏") ∷
   rw⁻ 83 q6 ∷
   rw 82 q7 ∷
   rw⁻ 81 q6 ∷
   re 82 3 (ℓ "乔") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q6 ∷
   rw 81 q15 ∷
   rw⁻ 80 q6 ∷
   re 81 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q6 ∷
   rw 80 q15 ∷
   rw⁻ 79 q6 ∷
   re 80 3 (ℓ "丽") ∷
   rw⁻ 78 q16 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q6 ∷
   rw 78 q15 ∷
   rw⁻ 77 q6 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q6 ∷
   rw 77 q15 ∷
   rw⁻ 76 q6 ∷
   re 77 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q6 ∷
   rw 76 q15 ∷
   rw⁻ 75 q6 ∷
   re 76 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q6 ∷
   rw 75 q15 ∷
   rw⁻ 74 q6 ∷
   re 75 3 (ℓ "丽") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q6 ∷
   rw 74 q15 ∷
   rw⁻ 73 q6 ∷
   re 74 3 (ℓ "丽") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q6 ∷
   rw 73 q15 ∷
   rw⁻ 72 q6 ∷
   re 73 3 (ℓ "丽") ∷
   rw⁻ 71 q17 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw⁻ 72 q6 ∷
   rw 71 q7 ∷
   rw⁻ 70 q6 ∷
   re 71 3 (ℓ "乔") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q6 ∷
   rw 70 q15 ∷
   rw⁻ 69 q6 ∷
   re 70 3 (ℓ "丽") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q6 ∷
   rw 69 q15 ∷
   rw⁻ 68 q6 ∷
   re 69 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q6 ∷
   rw 68 q15 ∷
   rw⁻ 67 q6 ∷
   re 68 3 (ℓ "丽") ∷
   rw⁻ 66 q17 ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw⁻ 67 q6 ∷
   rw 66 q7 ∷
   rw⁻ 65 q6 ∷
   re 66 3 (ℓ "乔") ∷
   rw⁻ 64 q17 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw⁻ 65 q6 ∷
   rw 64 q7 ∷
   rw⁻ 63 q6 ∷
   re 64 3 (ℓ "乔") ∷
   rw⁻ 62 q16 ∷
   rw 61 q7 ∷
   rw 60 q7 ∷
   rw 59 q15 ∷
   rw 58 q7 ∷
   rw 57 q15 ∷
   rw 56 q15 ∷
   rw 57 q18 ∷
   rw 56 q5 ∷
   rw 57 q19 ∷
   rw 58 q20 ∷
   rw 59 q19 ∷
   rw 60 q19 ∷
   rw 61 q5 ∷
   rw 62 q21 ∷
   rw 63 q21 ∷
   rw 64 q9 ∷
   rw 65 q21 ∷
   rw 66 q9 ∷
   rw 67 q9 ∷
   rw 68 q16 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q6 ∷
   rw 70 q9 ∷
   rw 71 q6 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q17 ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q6 ∷
   rw 72 q9 ∷
   rw 73 q6 ∷
   re 71 3 (ℓ "乑") ∷
   rw 72 q17 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q6 ∷
   rw 74 q21 ∷
   rw 75 q6 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q6 ∷
   rw 75 q21 ∷
   rw 76 q6 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q6 ∷
   rw 76 q21 ∷
   rw 77 q6 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏乇乏") ∷
   rw 76 q6 ∷
   rw 77 q9 ∷
   rw 78 q6 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q17 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q6 ∷
   rw 79 q21 ∷
   rw 80 q6 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q6 ∷
   rw 80 q21 ∷
   rw 81 q6 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q6 ∷
   rw 81 q21 ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q6 ∷
   rw 82 q21 ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q6 ∷
   rw 83 q21 ∷
   rw 84 q6 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q6 ∷
   rw 84 q21 ∷
   rw 85 q6 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q16 ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q6 ∷
   rw 86 q21 ∷
   rw 87 q6 ∷
   re 85 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q6 ∷
   rw 87 q21 ∷
   rw 88 q6 ∷
   re 86 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏乇乏") ∷
   rw 87 q6 ∷
   rw 88 q9 ∷
   rw 89 q6 ∷
   re 87 3 (ℓ "乑") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q6 ∷
   rw 89 q21 ∷
   rw 90 q6 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏乇乏") ∷
   rw 89 q6 ∷
   rw 90 q9 ∷
   rw 91 q6 ∷
   re 89 3 (ℓ "乑") ∷
   re 91 1 (ℓ "乏乇乏") ∷
   rw 90 q6 ∷
   rw 91 q9 ∷
   rw 92 q6 ∷
   re 90 3 (ℓ "乑") ∷
   rw 91 q10 ∷
   rw 96 q4 ∷
   rw⁻ 95 q5 ∷
   rw 94 q13 ∷
   rw 93 q13 ∷
   rw 92 q13 ∷
   rw⁻ 91 q5 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw⁻ 92 q6 ∷
   rw 91 q7 ∷
   rw⁻ 90 q6 ∷
   re 91 3 (ℓ "乔") ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw⁻ 91 q6 ∷
   rw 90 q7 ∷
   rw⁻ 89 q6 ∷
   re 90 3 (ℓ "乔") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q6 ∷
   rw 89 q15 ∷
   rw⁻ 88 q6 ∷
   re 89 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏乄乏") ∷
   rw⁻ 89 q6 ∷
   rw 88 q7 ∷
   rw⁻ 87 q6 ∷
   re 88 3 (ℓ "乔") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q6 ∷
   rw 87 q15 ∷
   rw⁻ 86 q6 ∷
   re 87 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q6 ∷
   rw 86 q15 ∷
   rw⁻ 85 q6 ∷
   re 86 3 (ℓ "丽") ∷
   rw⁻ 84 q16 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q6 ∷
   rw 84 q15 ∷
   rw⁻ 83 q6 ∷
   re 84 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q6 ∷
   rw 83 q15 ∷
   rw⁻ 82 q6 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q6 ∷
   rw 82 q15 ∷
   rw⁻ 81 q6 ∷
   re 82 3 (ℓ "丽") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q6 ∷
   rw 81 q15 ∷
   rw⁻ 80 q6 ∷
   re 81 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q6 ∷
   rw 80 q15 ∷
   rw⁻ 79 q6 ∷
   re 80 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q6 ∷
   rw 79 q15 ∷
   rw⁻ 78 q6 ∷
   re 79 3 (ℓ "丽") ∷
   rw⁻ 77 q17 ∷
   re 76 1 (ℓ "乏乄乏") ∷
   rw⁻ 78 q6 ∷
   rw 77 q7 ∷
   rw⁻ 76 q6 ∷
   re 77 3 (ℓ "乔") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q6 ∷
   rw 76 q15 ∷
   rw⁻ 75 q6 ∷
   re 76 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q6 ∷
   rw 75 q15 ∷
   rw⁻ 74 q6 ∷
   re 75 3 (ℓ "丽") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q6 ∷
   rw 74 q15 ∷
   rw⁻ 73 q6 ∷
   re 74 3 (ℓ "丽") ∷
   rw⁻ 72 q17 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw⁻ 73 q6 ∷
   rw 72 q7 ∷
   rw⁻ 71 q6 ∷
   re 72 3 (ℓ "乔") ∷
   rw⁻ 70 q17 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q6 ∷
   rw 70 q7 ∷
   rw⁻ 69 q6 ∷
   re 70 3 (ℓ "乔") ∷
   rw⁻ 68 q16 ∷
   rw 67 q7 ∷
   rw 66 q7 ∷
   rw 65 q15 ∷
   rw 64 q7 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 63 q22 ∷
   rw 62 q5 ∷
   rw 63 q19 ∷
   rw 64 q19 ∷
   rw 65 q19 ∷
   rw 66 q5 ∷
   rw 67 q21 ∷
   rw 68 q21 ∷
   rw 69 q9 ∷
   rw 70 q21 ∷
   rw 71 q9 ∷
   rw 72 q9 ∷
   rw 73 q16 ∷
   re 75 1 (ℓ "乏乇乏") ∷
   rw 74 q6 ∷
   rw 75 q9 ∷
   rw 76 q6 ∷
   re 74 3 (ℓ "乑") ∷
   rw 75 q17 ∷
   re 77 1 (ℓ "乏乇乏") ∷
   rw 76 q6 ∷
   rw 77 q9 ∷
   rw 78 q6 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q17 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q6 ∷
   rw 79 q21 ∷
   rw 80 q6 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q6 ∷
   rw 80 q21 ∷
   rw 81 q6 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q6 ∷
   rw 81 q21 ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏乇乏") ∷
   rw 81 q6 ∷
   rw 82 q9 ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q17 ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q6 ∷
   rw 84 q21 ∷
   rw 85 q6 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q6 ∷
   rw 85 q21 ∷
   rw 86 q6 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q6 ∷
   rw 86 q21 ∷
   rw 87 q6 ∷
   re 85 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q6 ∷
   rw 87 q21 ∷
   rw 88 q6 ∷
   re 86 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q6 ∷
   rw 88 q21 ∷
   rw 89 q6 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q6 ∷
   rw 89 q21 ∷
   rw 90 q6 ∷
   re 88 3 (ℓ "中") ∷
   rw 89 q16 ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q6 ∷
   rw 91 q21 ∷
   rw 92 q6 ∷
   re 90 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q6 ∷
   rw 92 q21 ∷
   rw 93 q6 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏乇乏") ∷
   rw 92 q6 ∷
   rw 93 q9 ∷
   rw 94 q6 ∷
   re 92 3 (ℓ "乑") ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q6 ∷
   rw 94 q21 ∷
   rw 95 q6 ∷
   re 93 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏乇乏") ∷
   rw 94 q6 ∷
   rw 95 q9 ∷
   rw 96 q6 ∷
   re 94 3 (ℓ "乑") ∷
   re 96 1 (ℓ "乏乇乏") ∷
   rw 95 q6 ∷
   rw 96 q9 ∷
   rw 97 q6 ∷
   re 95 3 (ℓ "乑") ∷
   rw 96 q10 ∷ []) Eq.refl
