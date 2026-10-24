{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D291 (W : Ws) where

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
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 884 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 883 W
  q14 : Eqn
  q14 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = wE 614 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 879 W
  q20 : Eqn
  q20 = wE 157 W
  q21 : Eqn
  q21 = wE 158 W
  q22 : Eqn
  q22 = wE 880 W
  q23 : Eqn
  q23 = wE 881 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part2: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中並丽丽丽丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且乇且丶丶丶丶丶丶丶丶丶且且且乇且且且且乇且並乀中中乑中乑乑丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠临丠临临乀乑业乑业中中中乑业中中中中中丒丹中丒乏乏乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中並丽丽丽丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且乇且丶丶丶丶丶丶丶丶丶且且且乇且且且且乇且並乀中中乑中乑乑丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠临丠临临乀乑业乑业中中中乑业中中中中中丒丹中丒乏乏乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (ℓ "丽") ∷
   rw⁻ 35 q3 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q1 ∷
   rw 35 q4 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q1 ∷
   rw 33 q2 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q1 ∷
   rw 32 q2 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 30 q3 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q1 ∷
   rw 30 q4 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (ℓ "乔") ∷
   rw⁻ 28 q3 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q1 ∷
   rw 28 q4 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (ℓ "乔") ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   rw 28 q6 ∷
   rw 29 q6 ∷
   rw 30 q6 ∷
   rw 31 q6 ∷
   rw 32 q6 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   rw 35 q6 ∷
   rw 36 q6 ∷
   rw 37 q6 ∷
   rw 38 q6 ∷
   rw 39 q6 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q6 ∷
   rw 45 q7 ∷
   rw 46 q7 ∷
   rw 47 q7 ∷
   rw 48 q8 ∷
   rw 49 q7 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   rw 52 q6 ∷
   rw 53 q6 ∷
   rw 54 q6 ∷
   rw 55 q6 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   rw 58 q6 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q7 ∷
   rw 67 q8 ∷
   rw 68 q7 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q1 ∷
   rw 70 q8 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q3 ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q1 ∷
   rw 72 q8 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乑") ∷
   rw 72 q3 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q1 ∷
   rw 74 q6 ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q1 ∷
   rw 75 q6 ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q1 ∷
   rw 76 q6 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏乇乏") ∷
   rw 76 q1 ∷
   rw 77 q8 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q3 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q1 ∷
   rw 79 q6 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q1 ∷
   rw 80 q6 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q1 ∷
   rw 81 q6 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q1 ∷
   rw 82 q6 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q6 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q6 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q9 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q10 ∷
   rw⁻ 27 q11 ∷
   rw 28 q12 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q10 ∷
   rw⁻ 28 q11 ∷
   rw 29 q12 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q10 ∷
   rw⁻ 29 q11 ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q10 ∷
   rw⁻ 30 q11 ∷
   rw 31 q12 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q10 ∷
   rw⁻ 31 q11 ∷
   rw 32 q12 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q10 ∷
   rw⁻ 32 q11 ∷
   rw 33 q12 ∷
   re 31 3 (ℓ "丧") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q10 ∷
   rw⁻ 33 q11 ∷
   rw 34 q12 ∷
   re 32 3 (ℓ "丧") ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 33 q10 ∷
   rw⁻ 34 q11 ∷
   rw 35 q12 ∷
   re 33 3 (ℓ "丧") ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 34 3 (ℓ "丧") ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q10 ∷
   rw⁻ 36 q11 ∷
   rw 37 q12 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q10 ∷
   rw⁻ 38 q11 ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q10 ∷
   rw⁻ 39 q11 ∷
   rw 40 q12 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q10 ∷
   rw⁻ 40 q11 ∷
   rw 41 q12 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q10 ∷
   rw⁻ 41 q11 ∷
   rw 42 q12 ∷
   re 40 3 (ℓ "丧") ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q10 ∷
   rw⁻ 42 q11 ∷
   rw 43 q12 ∷
   re 41 3 (ℓ "丧") ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q10 ∷
   rw⁻ 43 q11 ∷
   rw 44 q12 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q10 ∷
   rw⁻ 44 q11 ∷
   rw 45 q12 ∷
   re 43 3 (ℓ "丧") ∷
   rw 44 q13 ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   re 48 1 (ℓ "丼临丼") ∷
   rw 47 q10 ∷
   rw⁻ 48 q14 ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "乄") ∷
   rw 48 q13 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q10 ∷
   rw⁻ 50 q11 ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "丧") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q10 ∷
   rw⁻ 51 q11 ∷
   rw 52 q12 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q10 ∷
   rw⁻ 52 q11 ∷
   rw 53 q12 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q10 ∷
   rw⁻ 53 q11 ∷
   rw 54 q12 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q10 ∷
   rw⁻ 54 q11 ∷
   rw 55 q12 ∷
   re 53 3 (ℓ "丧") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q10 ∷
   rw⁻ 55 q11 ∷
   rw 56 q12 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q10 ∷
   rw⁻ 56 q11 ∷
   rw 57 q12 ∷
   re 55 3 (ℓ "丧") ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q10 ∷
   rw⁻ 57 q11 ∷
   rw 58 q12 ∷
   re 56 3 (ℓ "丧") ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q10 ∷
   rw⁻ 58 q11 ∷
   rw 59 q12 ∷
   re 57 3 (ℓ "丧") ∷
   rw 58 q13 ∷
   rw 59 q13 ∷
   rw 60 q13 ∷
   re 62 1 (ℓ "丼临丼") ∷
   rw 61 q10 ∷
   rw⁻ 62 q14 ∷
   rw 63 q12 ∷
   re 61 3 (ℓ "乄") ∷
   rw 62 q13 ∷
   rw 63 q13 ∷
   rw 64 q13 ∷
   rw 65 q13 ∷
   re 67 1 (ℓ "丼临丼") ∷
   rw 66 q10 ∷
   rw⁻ 67 q14 ∷
   rw 68 q12 ∷
   re 66 3 (ℓ "乄") ∷
   rw 67 q13 ∷
   rw 20 q15 ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 92 q18 ∷
   rw 91 q19 ∷
   rw⁻ 90 q17 ∷
   rw 93 q16 ∷
   re 91 3 (ℓ "乑") ∷
   rw 92 q18 ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 97 q16 ∷
   re 95 3 (ℓ "乀") ∷
   rw 94 q20 ∷
   rw 93 q14 ∷
   rw 92 q21 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 91 q18 ∷
   re 92 5 (ℓ "乑") ∷
   rw 94 q16 ∷
   rw 93 q17 ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 94 q18 ∷
   rw 93 q19 ∷
   rw⁻ 92 q17 ∷
   rw 95 q16 ∷
   re 93 3 (ℓ "乑") ∷
   rw 94 q18 ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 91 q18 ∷
   rw 90 q19 ∷
   rw⁻ 89 q17 ∷
   rw 92 q16 ∷
   re 90 3 (ℓ "乑") ∷
   rw 91 q18 ∷
   re 90 1 (ℓ "乏丼临丼乏") ∷
   rw 96 q16 ∷
   re 94 3 (ℓ "乀") ∷
   rw 93 q20 ∷
   rw 92 q14 ∷
   rw 91 q21 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 90 q18 ∷
   re 91 5 (ℓ "乑") ∷
   rw 93 q16 ∷
   rw 92 q17 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 93 q18 ∷
   rw 92 q19 ∷
   rw⁻ 91 q17 ∷
   rw 94 q16 ∷
   re 92 3 (ℓ "乑") ∷
   rw 93 q18 ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q18 ∷
   rw 89 q22 ∷
   rw⁻ 88 q17 ∷
   rw 91 q16 ∷
   re 89 3 (ℓ "中") ∷
   rw 90 q18 ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 95 q16 ∷
   re 93 3 (ℓ "乀") ∷
   rw 92 q20 ∷
   rw 91 q11 ∷
   rw 90 q21 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 89 q18 ∷
   re 90 5 (ℓ "中") ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q18 ∷
   rw 91 q22 ∷
   rw⁻ 90 q17 ∷
   rw 93 q16 ∷
   re 91 3 (ℓ "中") ∷
   rw 92 q18 ∷
   rw 89 q16 ∷
   rw 88 q17 ∷
   re 87 1 (ℓ "乏乄乏") ∷
   rw 89 q18 ∷
   rw 88 q19 ∷
   rw⁻ 87 q17 ∷
   rw 90 q16 ∷
   re 88 3 (ℓ "乑") ∷
   rw 89 q18 ∷
   re 88 1 (ℓ "乏丼临丼乏") ∷
   rw 94 q16 ∷
   re 92 3 (ℓ "乀") ∷
   rw 91 q20 ∷
   rw 90 q14 ∷
   rw 89 q21 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 88 q18 ∷
   re 89 5 (ℓ "乑") ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 91 q18 ∷
   rw 90 q19 ∷
   rw⁻ 89 q17 ∷
   rw 92 q16 ∷
   re 90 3 (ℓ "乑") ∷
   rw 91 q18 ∷
   rw 88 q16 ∷
   rw 87 q17 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q18 ∷
   rw 87 q22 ∷
   rw⁻ 86 q17 ∷
   rw 89 q16 ∷
   re 87 3 (ℓ "中") ∷
   rw 88 q18 ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q16 ∷
   re 91 3 (ℓ "乀") ∷
   rw 90 q20 ∷
   rw 89 q11 ∷
   rw 88 q21 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 87 q18 ∷
   re 88 5 (ℓ "中") ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q18 ∷
   rw 89 q22 ∷
   rw⁻ 88 q17 ∷
   rw 91 q16 ∷
   re 89 3 (ℓ "中") ∷
   rw 90 q18 ∷
   rw 87 q16 ∷
   rw 86 q17 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q18 ∷
   rw 86 q22 ∷
   rw⁻ 85 q17 ∷
   rw 88 q16 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q18 ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q16 ∷
   re 90 3 (ℓ "乀") ∷
   rw 89 q20 ∷
   rw 88 q11 ∷
   rw 87 q21 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 86 q18 ∷
   re 87 5 (ℓ "中") ∷
   rw 89 q16 ∷
   rw 88 q17 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q18 ∷
   rw 88 q22 ∷
   rw⁻ 87 q17 ∷
   rw 90 q16 ∷
   re 88 3 (ℓ "中") ∷
   rw 89 q18 ∷
   rw 84 q23 ∷
   rw 85 q16 ∷
   rw 84 q17 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q18 ∷
   rw 84 q22 ∷
   rw⁻ 83 q17 ∷
   rw 86 q16 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q18 ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q16 ∷
   re 88 3 (ℓ "乀") ∷
   rw 87 q20 ∷
   rw 86 q11 ∷
   rw 85 q21 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 84 q18 ∷
   re 85 5 (ℓ "中") ∷
   rw 87 q16 ∷ []) Eq.refl
