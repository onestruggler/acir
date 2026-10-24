{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D323 (W : Ws) where

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
  q1 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 880 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 158 W
  q8 : Eqn
  q8 = eqn (ℓ "丒业") (ℓ "业丒") (low-comm ((X ↑)) ((S ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q10 : Eqn
  q10 = wE 879 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 881 W
  q13 : Eqn
  q13 = wE 946 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 868 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 36 W
  q24 : Eqn
  q24 = wE 37 W
  q25 : Eqn
  q25 = wE 883 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part1: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part1 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中丒乏乏丹丒中中中中中中中乀中中中乑中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丼乌丠丼丧丧丧丧丧丧丧且且且乄且且且且乄且中中中乑中中丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part1 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中丒乏乏丹丒中中中中中中中乀中中中乑中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丼乌丠丼丧丧丧丧丧丧丧且且且乄且且且且乄且中中中乑中中丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (rw 34 q1 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw⁻ 33 q1 ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q2 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   rw 35 q7 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q2 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q4 ∷
   rw 36 q1 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw⁻ 35 q1 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q2 ∷
   rw 34 q4 ∷
   rw 33 q1 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw⁻ 32 q1 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q2 ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q4 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q5 ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q2 ∷
   re 34 5 (ℓ "中") ∷
   rw 36 q4 ∷
   rw 35 q1 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw⁻ 34 q1 ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q2 ∷
   rw⁻ 31 q8 ∷
   rw⁻ 32 q9 ∷
   rw⁻ 33 q8 ∷
   rw 32 q4 ∷
   rw 31 q1 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q2 ∷
   rw 31 q10 ∷
   rw⁻ 30 q1 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q2 ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q5 ∷
   rw 33 q11 ∷
   rw 32 q7 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q2 ∷
   re 32 5 (ℓ "乑") ∷
   rw 34 q4 ∷
   rw 33 q1 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q2 ∷
   rw 33 q10 ∷
   rw⁻ 32 q1 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q2 ∷
   rw 31 q4 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q1 ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   rw 31 q7 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q2 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q4 ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q1 ∷
   rw 34 q4 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q2 ∷
   rw 30 q4 ∷
   rw 29 q1 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q1 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q2 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q7 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q2 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q4 ∷
   rw 31 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q1 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q2 ∷
   rw 29 q4 ∷
   rw 28 q1 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q1 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q4 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   rw 29 q7 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q2 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q4 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q1 ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q2 ∷
   rw 28 q4 ∷
   rw 27 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q1 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q2 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   rw 28 q7 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q2 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q4 ∷
   rw 29 q1 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q1 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q2 ∷
   rw 27 q4 ∷
   rw 26 q1 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q1 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q2 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q4 ∷
   rw 28 q1 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q1 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q2 ∷
   rw 26 q4 ∷
   rw 25 q1 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   rw⁻ 24 q1 ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q2 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   rw 26 q7 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q2 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q4 ∷
   rw 27 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q1 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q2 ∷
   rw 23 q12 ∷
   rw 17 q13 ∷
   rw 93 q14 ∷
   rw⁻ 92 q15 ∷
   rw 91 q16 ∷
   rw⁻ 90 q15 ∷
   rw⁻ 89 q15 ∷
   rw⁻ 88 q15 ∷
   rw⁻ 87 q15 ∷
   rw 86 q16 ∷
   rw⁻ 85 q15 ∷
   rw⁻ 84 q15 ∷
   rw⁻ 83 q15 ∷
   rw 82 q17 ∷
   rw 81 q17 ∷
   rw 80 q17 ∷
   rw 79 q17 ∷
   rw 78 q17 ∷
   rw 77 q17 ∷
   rw 76 q17 ∷
   rw 75 q17 ∷
   rw 74 q17 ∷
   rw⁻ 73 q15 ∷
   rw 72 q16 ∷
   rw⁻ 71 q15 ∷
   rw⁻ 70 q15 ∷
   rw⁻ 69 q15 ∷
   rw 68 q17 ∷
   rw 67 q17 ∷
   rw 66 q17 ∷
   rw 65 q17 ∷
   rw 64 q17 ∷
   rw 63 q17 ∷
   rw 62 q17 ∷
   rw 61 q17 ∷
   rw 60 q17 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q18 ∷
   rw 51 q17 ∷
   rw⁻ 50 q18 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q18 ∷
   rw 50 q17 ∷
   rw⁻ 49 q18 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q18 ∷
   rw 49 q16 ∷
   rw⁻ 48 q18 ∷
   re 49 3 (ℓ "乔") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q18 ∷
   rw 48 q17 ∷
   rw⁻ 47 q18 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q18 ∷
   rw 47 q17 ∷
   rw⁻ 46 q18 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q18 ∷
   rw 46 q17 ∷
   rw⁻ 45 q18 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q19 ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q20 ∷
   rw 49 q20 ∷
   rw 50 q20 ∷
   rw 51 q20 ∷
   rw 52 q20 ∷
   rw 53 q20 ∷
   rw 54 q20 ∷
   rw 55 q20 ∷
   rw 56 q20 ∷
   rw 57 q20 ∷
   rw 58 q20 ∷
   rw 59 q20 ∷
   rw 60 q20 ∷
   rw 61 q20 ∷
   rw 62 q20 ∷
   rw 63 q15 ∷
   rw 64 q15 ∷
   rw 65 q15 ∷
   rw 66 q21 ∷
   rw 67 q15 ∷
   rw 68 q20 ∷
   rw 69 q20 ∷
   rw 70 q20 ∷
   rw 71 q20 ∷
   rw 72 q20 ∷
   rw 73 q20 ∷
   rw 74 q20 ∷
   rw 75 q20 ∷
   rw 76 q20 ∷
   rw 77 q15 ∷
   rw 78 q15 ∷
   rw 79 q15 ∷
   rw 80 q21 ∷
   rw 81 q15 ∷
   rw 82 q15 ∷
   rw 83 q15 ∷
   rw 84 q15 ∷
   rw 85 q21 ∷
   rw 86 q15 ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q18 ∷
   rw 88 q20 ∷
   rw 89 q18 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q18 ∷
   rw 89 q20 ∷
   rw 90 q18 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q18 ∷
   rw 90 q20 ∷
   rw 91 q18 ∷
   re 89 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏乇乏") ∷
   rw 90 q18 ∷
   rw 91 q21 ∷
   rw 92 q18 ∷
   re 90 3 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q18 ∷
   rw 92 q20 ∷
   rw 93 q18 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q18 ∷
   rw 93 q20 ∷
   rw 94 q18 ∷
   re 92 3 (ℓ "中") ∷
   rw 93 q22 ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 44 q23 ∷
   rw⁻ 45 q6 ∷
   rw 46 q24 ∷
   re 44 3 (ℓ "丧") ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q23 ∷
   rw⁻ 46 q6 ∷
   rw 47 q24 ∷
   re 45 3 (ℓ "丧") ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 46 q23 ∷
   rw⁻ 47 q6 ∷
   rw 48 q24 ∷
   re 46 3 (ℓ "丧") ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q23 ∷
   rw⁻ 48 q6 ∷
   rw 49 q24 ∷
   re 47 3 (ℓ "丧") ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 48 q23 ∷
   rw⁻ 49 q6 ∷
   rw 50 q24 ∷
   re 48 3 (ℓ "丧") ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q23 ∷
   rw⁻ 50 q6 ∷
   rw 51 q24 ∷
   re 49 3 (ℓ "丧") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q23 ∷
   rw⁻ 51 q6 ∷
   rw 52 q24 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q23 ∷
   rw⁻ 52 q6 ∷
   rw 53 q24 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q23 ∷
   rw⁻ 53 q6 ∷
   rw 54 q24 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q23 ∷
   rw⁻ 54 q6 ∷
   rw 55 q24 ∷
   re 53 3 (ℓ "丧") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q23 ∷
   rw⁻ 55 q6 ∷
   rw 56 q24 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q23 ∷
   rw⁻ 56 q6 ∷
   rw 57 q24 ∷
   re 55 3 (ℓ "丧") ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q23 ∷
   rw⁻ 57 q6 ∷
   rw 58 q24 ∷
   re 56 3 (ℓ "丧") ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q23 ∷
   rw⁻ 58 q6 ∷
   rw 59 q24 ∷
   re 57 3 (ℓ "丧") ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 58 q23 ∷
   rw⁻ 59 q6 ∷
   rw 60 q24 ∷
   re 58 3 (ℓ "丧") ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 59 q23 ∷
   rw⁻ 60 q6 ∷
   rw 61 q24 ∷
   re 59 3 (ℓ "丧") ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 60 q23 ∷
   rw⁻ 61 q6 ∷
   rw 62 q24 ∷
   re 60 3 (ℓ "丧") ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 61 q23 ∷
   rw⁻ 62 q6 ∷
   rw 63 q24 ∷
   re 61 3 (ℓ "丧") ∷
   rw 62 q25 ∷
   rw 63 q25 ∷
   rw 64 q25 ∷
   re 66 1 (ℓ "丼临丼") ∷
   rw 65 q23 ∷
   rw⁻ 66 q11 ∷
   rw 67 q24 ∷
   re 65 3 (ℓ "乄") ∷
   rw 66 q25 ∷
   re 68 1 (ℓ "丼丠丼") ∷
   rw 67 q23 ∷
   rw⁻ 68 q6 ∷
   rw 69 q24 ∷
   re 67 3 (ℓ "丧") ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 68 q23 ∷ []) Eq.refl
