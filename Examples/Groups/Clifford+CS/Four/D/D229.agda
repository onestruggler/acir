{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D229 (W : Ws) where

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
  q3 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 818 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = wE 29 W
  q8 : Eqn
  q8 = wE 139 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = wE 76 W
  q15 : Eqn
  q15 = wE 820 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part11: 396 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part11 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧丧乄丧丧乌中中並乏丶乏丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丷么丷丷丘並丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part11 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧丧乄丧丧乌中中並乏丶乏丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丷么丷丷丘並丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "丽") ∷
   rw⁻ 62 q3 ∷
   rw 61 q2 ∷
   rw 60 q2 ∷
   rw 59 q4 ∷
   rw 58 q2 ∷
   rw 57 q2 ∷
   rw 56 q2 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw 57 q7 ∷
   rw 58 q8 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q6 ∷
   rw 62 q9 ∷
   rw 63 q9 ∷
   rw 64 q9 ∷
   rw 65 q10 ∷
   rw 66 q9 ∷
   rw 67 q9 ∷
   rw 68 q3 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q1 ∷
   rw 70 q9 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q1 ∷
   rw 71 q9 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q1 ∷
   rw 72 q9 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q1 ∷
   rw 73 q9 ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q1 ∷
   rw 74 q9 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q1 ∷
   rw 75 q9 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏乇乏") ∷
   rw 75 q1 ∷
   rw 76 q10 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "乑") ∷
   rw 76 q11 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q1 ∷
   rw 78 q9 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q1 ∷
   rw 79 q9 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q1 ∷
   rw 80 q9 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q1 ∷
   rw 81 q9 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q1 ∷
   rw 82 q9 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q9 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q9 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q1 ∷
   rw 85 q9 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q1 ∷
   rw 86 q9 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q3 ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q1 ∷
   rw 88 q9 ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q1 ∷
   rw 89 q9 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q1 ∷
   rw 90 q9 ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏乇乏") ∷
   rw 90 q1 ∷
   rw 91 q10 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q1 ∷
   rw 92 q9 ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q1 ∷
   rw 93 q9 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   rw 93 q12 ∷
   rw 98 q13 ∷
   rw⁻ 97 q6 ∷
   rw 96 q14 ∷
   rw 95 q14 ∷
   rw 94 q14 ∷
   rw⁻ 93 q6 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw⁻ 94 q1 ∷
   rw 93 q2 ∷
   rw⁻ 92 q1 ∷
   re 93 3 (ℓ "丽") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q1 ∷
   rw 92 q2 ∷
   rw⁻ 91 q1 ∷
   re 92 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw⁻ 92 q1 ∷
   rw 91 q4 ∷
   rw⁻ 90 q1 ∷
   re 91 3 (ℓ "乔") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw⁻ 91 q1 ∷
   rw 90 q2 ∷
   rw⁻ 89 q1 ∷
   re 90 3 (ℓ "丽") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q1 ∷
   rw 89 q2 ∷
   rw⁻ 88 q1 ∷
   re 89 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q1 ∷
   rw 88 q2 ∷
   rw⁻ 87 q1 ∷
   re 88 3 (ℓ "丽") ∷
   rw⁻ 86 q3 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q1 ∷
   rw 86 q2 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q1 ∷
   rw 85 q2 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (ℓ "丽") ∷
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
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q1 ∷
   rw 81 q2 ∷
   rw⁻ 80 q1 ∷
   re 81 3 (ℓ "丽") ∷
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
   rw⁻ 76 q11 ∷
   re 75 1 (ℓ "乏乄乏") ∷
   rw⁻ 77 q1 ∷
   rw 76 q4 ∷
   rw⁻ 75 q1 ∷
   re 76 3 (ℓ "乔") ∷
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
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q1 ∷
   rw 71 q2 ∷
   rw⁻ 70 q1 ∷
   re 71 3 (ℓ "丽") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q2 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "丽") ∷
   rw⁻ 68 q3 ∷
   rw 67 q2 ∷
   rw 66 q2 ∷
   rw 65 q4 ∷
   rw 64 q2 ∷
   rw 63 q2 ∷
   rw 62 q2 ∷
   rw 63 q15 ∷
   rw 62 q6 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 67 q9 ∷
   rw 68 q9 ∷
   rw 69 q9 ∷
   rw 70 q10 ∷
   rw 71 q9 ∷
   rw 72 q9 ∷
   rw 73 q3 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q1 ∷
   rw 75 q9 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q1 ∷
   rw 76 q9 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q1 ∷
   rw 77 q9 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q1 ∷
   rw 78 q9 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q1 ∷
   rw 79 q9 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q1 ∷
   rw 80 q9 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏乇乏") ∷
   rw 80 q1 ∷
   rw 81 q10 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "乑") ∷
   rw 81 q11 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q9 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q9 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q1 ∷
   rw 85 q9 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q1 ∷
   rw 86 q9 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q1 ∷
   rw 87 q9 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q1 ∷
   rw 88 q9 ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q1 ∷
   rw 89 q9 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q1 ∷
   rw 90 q9 ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q1 ∷
   rw 91 q9 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "中") ∷
   rw 91 q3 ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q1 ∷
   rw 93 q9 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q1 ∷
   rw 94 q9 ∷
   rw 95 q1 ∷
   re 93 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丶乏") ∷
   rw 94 q1 ∷
   rw 95 q9 ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "中") ∷
   re 96 1 (ℓ "乏乇乏") ∷
   rw 95 q1 ∷
   rw 96 q10 ∷
   rw 97 q1 ∷
   re 95 3 (ℓ "乑") ∷
   re 97 1 (ℓ "乏丶乏") ∷
   rw 96 q1 ∷
   rw 97 q9 ∷
   rw 98 q1 ∷
   re 96 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丶乏") ∷
   rw 97 q1 ∷
   rw 98 q9 ∷
   rw 99 q1 ∷
   re 97 3 (ℓ "中") ∷
   rw 98 q12 ∷ []) Eq.refl
