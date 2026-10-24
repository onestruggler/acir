{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D324 (W : Ws) where

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
  q1 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q2 : Eqn
  q2 = wE 37 W
  q3 : Eqn
  q3 = wE 36 W
  q4 : Eqn
  q4 = wE 883 W
  q5 : Eqn
  q5 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 140 W
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 947 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 142 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = wE 662 W
  q17 : Eqn
  q17 = wE 1 W
  q18 : Eqn
  q18 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = wE 880 W
  q21 : Eqn
  q21 = wE 157 W
  q22 : Eqn
  q22 = wE 158 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part2: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丼乌丠丼丧丧丧丧丧丧丧且且且乄且且且且乄且中中中乑中中丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑乏丒丧乏丹丒中乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part2 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丼乌丠丼丧丧丧丧丧丧丧且且且乄且且且且乄且中中中乑中中丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑乏丒丧乏丹丒中乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (rw⁻ 69 q1 ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "丧") ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 69 q3 ∷
   rw⁻ 70 q1 ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "丧") ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 70 q3 ∷
   rw⁻ 71 q1 ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "丧") ∷
   re 72 1 (ℓ "丼丠丼") ∷
   rw 71 q3 ∷
   rw⁻ 72 q1 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "丧") ∷
   re 73 1 (ℓ "丼丠丼") ∷
   rw 72 q3 ∷
   rw⁻ 73 q1 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "丧") ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 73 q3 ∷
   rw⁻ 74 q1 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "丧") ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 74 q3 ∷
   rw⁻ 75 q1 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "丧") ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 75 q3 ∷
   rw⁻ 76 q1 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "丧") ∷
   rw 76 q4 ∷
   rw 77 q4 ∷
   rw 78 q4 ∷
   re 80 1 (ℓ "丼临丼") ∷
   rw 79 q3 ∷
   rw⁻ 80 q5 ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "乄") ∷
   rw 80 q4 ∷
   rw 81 q4 ∷
   rw 82 q4 ∷
   rw 83 q4 ∷
   re 85 1 (ℓ "丼临丼") ∷
   rw 84 q3 ∷
   rw⁻ 85 q5 ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乄") ∷
   rw 85 q4 ∷
   rw 86 q6 ∷
   rw⁻ 85 q7 ∷
   rw 84 q8 ∷
   rw⁻ 83 q7 ∷
   rw⁻ 82 q7 ∷
   rw⁻ 81 q7 ∷
   rw⁻ 80 q7 ∷
   rw 79 q8 ∷
   rw⁻ 78 q7 ∷
   rw⁻ 77 q7 ∷
   rw⁻ 76 q7 ∷
   rw 75 q9 ∷
   rw 74 q9 ∷
   rw 73 q9 ∷
   rw 72 q9 ∷
   rw 71 q9 ∷
   rw 70 q9 ∷
   rw 69 q9 ∷
   rw 68 q9 ∷
   rw 67 q9 ∷
   rw⁻ 66 q7 ∷
   rw 65 q8 ∷
   rw⁻ 64 q7 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 62 q7 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q10 ∷
   rw 44 q9 ∷
   rw⁻ 43 q10 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q10 ∷
   rw 43 q9 ∷
   rw⁻ 42 q10 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q10 ∷
   rw 42 q9 ∷
   rw⁻ 41 q10 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q10 ∷
   rw 41 q9 ∷
   rw⁻ 40 q10 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q10 ∷
   rw 40 q9 ∷
   rw⁻ 39 q10 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q10 ∷
   rw 39 q9 ∷
   rw⁻ 38 q10 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q10 ∷
   rw 38 q9 ∷
   rw⁻ 37 q10 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q10 ∷
   rw 37 q9 ∷
   rw⁻ 36 q10 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q10 ∷
   rw 36 q9 ∷
   rw⁻ 35 q10 ∷
   re 36 3 (ℓ "丽") ∷
   rw⁻ 34 q11 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q10 ∷
   rw 34 q8 ∷
   rw⁻ 33 q10 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q10 ∷
   rw 33 q9 ∷
   rw⁻ 32 q10 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q10 ∷
   rw 32 q9 ∷
   rw⁻ 31 q10 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q10 ∷
   rw 31 q9 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q10 ∷
   rw 30 q9 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q10 ∷
   rw 29 q9 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q10 ∷
   rw 28 q9 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q12 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q13 ∷
   rw 33 q13 ∷
   rw 34 q13 ∷
   rw 35 q13 ∷
   rw 36 q13 ∷
   rw 37 q13 ∷
   rw 38 q13 ∷
   rw 39 q13 ∷
   rw 40 q13 ∷
   rw 41 q13 ∷
   rw 42 q13 ∷
   rw 43 q13 ∷
   rw 44 q13 ∷
   rw 45 q7 ∷
   rw 46 q7 ∷
   rw 47 q7 ∷
   rw 48 q14 ∷
   rw 49 q7 ∷
   rw 50 q13 ∷
   rw 51 q13 ∷
   rw 52 q13 ∷
   rw 53 q13 ∷
   rw 54 q13 ∷
   rw 55 q13 ∷
   rw 56 q13 ∷
   rw 57 q13 ∷
   rw 58 q13 ∷
   rw 59 q7 ∷
   rw 60 q7 ∷
   rw 61 q7 ∷
   rw 62 q14 ∷
   rw 63 q7 ∷
   rw 64 q7 ∷
   rw 65 q7 ∷
   rw 66 q7 ∷
   rw 67 q14 ∷
   rw 68 q7 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q10 ∷
   rw 70 q13 ∷
   rw 71 q10 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q10 ∷
   rw 71 q13 ∷
   rw 72 q10 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q10 ∷
   rw 72 q13 ∷
   rw 73 q10 ∷
   re 71 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q10 ∷
   rw 73 q13 ∷
   rw 74 q10 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q10 ∷
   rw 74 q13 ∷
   rw 75 q10 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q10 ∷
   rw 75 q13 ∷
   rw 76 q10 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏乇乏") ∷
   rw 75 q10 ∷
   rw 76 q14 ∷
   rw 77 q10 ∷
   re 75 3 (ℓ "乑") ∷
   rw 76 q11 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q10 ∷
   rw 78 q13 ∷
   rw 79 q10 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q10 ∷
   rw 79 q13 ∷
   rw 80 q10 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q10 ∷
   rw 80 q13 ∷
   rw 81 q10 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q10 ∷
   rw 81 q13 ∷
   rw 82 q10 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q10 ∷
   rw 82 q13 ∷
   rw 83 q10 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q10 ∷
   rw 83 q13 ∷
   rw 84 q10 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q10 ∷
   rw 84 q13 ∷
   rw 85 q10 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q10 ∷
   rw 85 q13 ∷
   rw 86 q10 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q10 ∷
   rw 86 q13 ∷
   rw 87 q10 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q15 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q3 ∷
   rw⁻ 27 q1 ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q3 ∷
   rw⁻ 28 q1 ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q3 ∷
   rw⁻ 29 q1 ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q3 ∷
   rw⁻ 30 q1 ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q3 ∷
   rw⁻ 31 q1 ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q3 ∷
   rw⁻ 32 q1 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "丧") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q3 ∷
   rw⁻ 33 q1 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "丧") ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 33 q3 ∷
   rw⁻ 34 q1 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "丧") ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q3 ∷
   rw⁻ 35 q1 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "丧") ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q3 ∷
   rw⁻ 36 q1 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q3 ∷
   rw⁻ 37 q1 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q3 ∷
   rw⁻ 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q3 ∷
   rw⁻ 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q3 ∷
   rw⁻ 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q3 ∷
   rw⁻ 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "丧") ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q3 ∷
   rw⁻ 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "丧") ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q3 ∷
   rw⁻ 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q3 ∷
   rw⁻ 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "丧") ∷
   rw 44 q4 ∷
   rw 45 q4 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "丼临丼") ∷
   rw 47 q3 ∷
   rw⁻ 48 q5 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乄") ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q3 ∷
   rw⁻ 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "丧") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q3 ∷
   rw⁻ 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q3 ∷
   rw⁻ 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q3 ∷
   rw⁻ 54 q1 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "丧") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q3 ∷
   rw⁻ 55 q1 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q3 ∷
   rw⁻ 56 q1 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "丧") ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q3 ∷
   rw⁻ 57 q1 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "丧") ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q3 ∷
   rw⁻ 58 q1 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "丧") ∷
   rw 58 q4 ∷
   rw 59 q4 ∷
   rw 60 q4 ∷
   re 62 1 (ℓ "丼临丼") ∷
   rw 61 q3 ∷
   rw⁻ 62 q5 ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "乄") ∷
   rw 62 q4 ∷
   rw 63 q4 ∷
   rw 64 q4 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "丼临丼") ∷
   rw 66 q3 ∷
   rw⁻ 67 q5 ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乄") ∷
   rw 67 q4 ∷
   rw 20 q16 ∷
   rw 94 q17 ∷
   rw 93 q18 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q19 ∷
   rw 93 q20 ∷
   rw⁻ 92 q18 ∷
   rw 95 q17 ∷
   re 93 3 (ℓ "中") ∷
   rw 94 q19 ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 99 q17 ∷
   re 97 3 (ℓ "乀") ∷
   rw 96 q21 ∷
   rw 95 q1 ∷
   rw 94 q22 ∷
   re 94 1 (ℓ "乏丹乏") ∷
   rw 93 q19 ∷
   re 94 5 (ℓ "中") ∷
   rw 96 q17 ∷
   rw 95 q18 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q19 ∷
   rw 95 q20 ∷
   rw⁻ 94 q18 ∷
   rw 97 q17 ∷
   re 95 3 (ℓ "中") ∷
   rw 96 q19 ∷
   rw 93 q17 ∷
   rw 92 q18 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q19 ∷
   rw 92 q20 ∷ []) Eq.refl
