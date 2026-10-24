{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D159 (W : Ws) where

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
  q1 = wE 140 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 740 W
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
  q14 = wE 741 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 484 W
  q20 : Eqn
  q20 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q21 : Eqn
  q21 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q22 : Eqn
  q22 = wE 464 W
  q23 : Eqn
  q23 = wE 485 W
  q24 : Eqn
  q24 = wE 151 W
  q25 : Eqn
  q25 = wE 630 W
  q26 : Eqn
  q26 = wE 113 W
  q27 : Eqn
  q27 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q28 : Eqn
  q28 = wE 114 W

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part5: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧乄丧乄乄乌乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丷么丷丷丘並丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中丘乏丼临丼乓乏丘乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丧丧乄丧乄乄乌乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丷么丷丷丘並丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中丘乏丼临丼乓乏丘乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (ℓ "乔") ∷
   rw⁻ 30 q3 ∷
   rw 29 q1 ∷
   rw 28 q1 ∷
   rw 27 q4 ∷
   rw 26 q1 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 25 q7 ∷
   rw 26 q8 ∷
   rw 27 q7 ∷
   rw 28 q7 ∷
   rw 29 q6 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q10 ∷
   rw 33 q9 ∷
   rw 34 q10 ∷
   rw 35 q10 ∷
   rw 36 q3 ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q2 ∷
   rw 38 q10 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q11 ∷
   re 40 1 (ℓ "乏乇乏") ∷
   rw 39 q2 ∷
   rw 40 q10 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "乑") ∷
   rw 40 q11 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q2 ∷
   rw 42 q9 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q2 ∷
   rw 43 q9 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q2 ∷
   rw 44 q9 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏乇乏") ∷
   rw 44 q2 ∷
   rw 45 q10 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q11 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q9 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q9 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q9 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q2 ∷
   rw 50 q9 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q2 ∷
   rw 51 q9 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q2 ∷
   rw 52 q9 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q3 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q2 ∷
   rw 54 q9 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q2 ∷
   rw 55 q9 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏乇乏") ∷
   rw 55 q2 ∷
   rw 56 q10 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乑") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q2 ∷
   rw 57 q9 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 57 q2 ∷
   rw 58 q10 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "乑") ∷
   re 59 1 (ℓ "乏乇乏") ∷
   rw 58 q2 ∷
   rw 59 q10 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "乑") ∷
   rw 59 q12 ∷
   rw 64 q13 ∷
   rw⁻ 63 q6 ∷
   rw 62 q4 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw⁻ 59 q6 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw⁻ 60 q2 ∷
   rw 59 q1 ∷
   rw⁻ 58 q2 ∷
   re 59 3 (ℓ "乔") ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw⁻ 59 q2 ∷
   rw 58 q1 ∷
   rw⁻ 57 q2 ∷
   re 58 3 (ℓ "乔") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q2 ∷
   rw 57 q4 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw⁻ 57 q2 ∷
   rw 56 q1 ∷
   rw⁻ 55 q2 ∷
   re 56 3 (ℓ "乔") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q2 ∷
   rw 55 q4 ∷
   rw⁻ 54 q2 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q2 ∷
   rw 54 q4 ∷
   rw⁻ 53 q2 ∷
   re 54 3 (ℓ "丽") ∷
   rw⁻ 52 q3 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q2 ∷
   rw 52 q4 ∷
   rw⁻ 51 q2 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q2 ∷
   rw 51 q4 ∷
   rw⁻ 50 q2 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q2 ∷
   rw 50 q4 ∷
   rw⁻ 49 q2 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q2 ∷
   rw 49 q4 ∷
   rw⁻ 48 q2 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q2 ∷
   rw 48 q4 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q4 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "丽") ∷
   rw⁻ 45 q11 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q1 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "乔") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q4 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q4 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q2 ∷
   rw 42 q4 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (ℓ "丽") ∷
   rw⁻ 40 q11 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw⁻ 41 q2 ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (ℓ "乔") ∷
   rw⁻ 38 q11 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q2 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (ℓ "乔") ∷
   rw⁻ 36 q3 ∷
   rw 35 q1 ∷
   rw 34 q1 ∷
   rw 33 q4 ∷
   rw 32 q1 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 31 q14 ∷
   rw 30 q6 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q6 ∷
   rw 35 q9 ∷
   rw 36 q9 ∷
   rw 37 q10 ∷
   rw 38 q9 ∷
   rw 39 q10 ∷
   rw 40 q10 ∷
   rw 41 q3 ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 42 q2 ∷
   rw 43 q10 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "乑") ∷
   rw 43 q11 ∷
   re 45 1 (ℓ "乏乇乏") ∷
   rw 44 q2 ∷
   rw 45 q10 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q11 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q9 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q9 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q9 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q2 ∷
   rw 50 q10 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q11 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q2 ∷
   rw 52 q9 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q2 ∷
   rw 53 q9 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q2 ∷
   rw 54 q9 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q2 ∷
   rw 55 q9 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q2 ∷
   rw 56 q9 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q2 ∷
   rw 57 q9 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q3 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q2 ∷
   rw 59 q9 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q2 ∷
   rw 60 q9 ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q2 ∷
   rw 61 q10 ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q2 ∷
   rw 62 q9 ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q2 ∷
   rw 63 q10 ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "乑") ∷
   re 64 1 (ℓ "乏乇乏") ∷
   rw 63 q2 ∷
   rw 64 q10 ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q12 ∷
   rw 68 q15 ∷
   rw 67 q16 ∷
   rw 66 q16 ∷
   rw 65 q17 ∷
   rw 64 q16 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw 65 q18 ∷
   re 62 1 (ℓ "乏乄乏") ∷
   rw 64 q18 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q18 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 62 q18 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q18 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q18 ∷
   rw 59 q19 ∷
   rw⁻ 58 q16 ∷
   rw⁻ 59 q17 ∷
   rw⁻ 60 q16 ∷
   rw⁻ 61 q16 ∷
   rw 64 q15 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q15 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q15 ∷
   re 64 3 (ℓ "乑") ∷
   rw 67 q15 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q15 ∷
   re 66 3 (ℓ "乑") ∷
   rw 69 q15 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q18 ∷
   rw⁻ 57 q20 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 59 q20 ∷
   rw⁻ 60 q20 ∷
   rw 61 q15 ∷
   rw 60 q16 ∷
   rw 59 q16 ∷
   rw 58 q17 ∷
   rw 57 q16 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q18 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q18 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q18 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q18 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q18 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q18 ∷
   rw 50 q22 ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw 51 q18 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q18 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q18 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q18 ∷
   rw 45 q22 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw 46 q18 ∷
   rw 43 q22 ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw 44 q18 ∷
   rw 43 q23 ∷
   rw⁻ 42 q16 ∷
   rw⁻ 43 q17 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 45 q16 ∷
   rw 48 q15 ∷
   re 46 3 (ℓ "乑") ∷
   rw 47 q24 ∷
   rw 50 q15 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q24 ∷
   rw 52 q15 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q15 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q15 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q15 ∷
   re 53 3 (ℓ "乑") ∷
   rw 54 q24 ∷
   rw 57 q15 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q15 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q15 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q15 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q15 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q15 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q18 ∷
   rw⁻ 41 q20 ∷
   rw⁻ 42 q21 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 44 q20 ∷
   rw 35 q19 ∷
   rw 69 q13 ∷
   rw⁻ 68 q6 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw⁻ 69 q2 ∷
   rw 68 q1 ∷
   rw⁻ 67 q2 ∷
   re 68 3 (ℓ "乔") ∷
   rw 68 q25 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏乇乏") ∷
   rw 68 q2 ∷
   rw 69 q10 ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "乑") ∷
   rw 69 q12 ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q15 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q26 ∷
   rw 70 q27 ∷
   rw 69 q28 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q18 ∷
   re 69 5 (ℓ "乑") ∷
   rw 71 q13 ∷
   rw⁻ 70 q6 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q2 ∷
   rw 70 q1 ∷
   rw⁻ 69 q2 ∷
   re 70 3 (ℓ "乔") ∷
   rw 70 q25 ∷
   rw 69 q6 ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q2 ∷
   rw 71 q10 ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q12 ∷
   rw 68 q13 ∷
   rw⁻ 67 q6 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q2 ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   re 67 3 (ℓ "乔") ∷
   rw 67 q25 ∷
   rw 66 q6 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q2 ∷
   rw 68 q10 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q12 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 73 q15 ∷
   re 71 3 (ℓ "乓") ∷ []) Eq.refl
