{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D348 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 36 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = wE 37 W
  q6 : Eqn
  q6 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 614 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = wE 879 W
  q14 : Eqn
  q14 = wE 157 W
  q15 : Eqn
  q15 = wE 158 W
  q16 : Eqn
  q16 = wE 880 W
  q17 : Eqn
  q17 = wE 956 W
  q18 : Eqn
  q18 = eqn (ℓ "丒且") (ℓ "且丒") (low-comm ((X ↑)) (S))
  q19 : Eqn
  q19 = wE 625 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part3: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中业业业乑业乏丼丠丼乀乏中中中中中中中中业业业乑业业业业乑业乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丠丠临丠临临丹乄且乄且丧丧丒乏丹乏丧丒乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part3 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中业业业乑业乏丼丠丼乀乏中中中中中中中中业业业乑业业业业乑业乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丠丠临丠临临丹乄且乄且丧丧丒乏丹乏丧丒乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乑业乑业中中中乑业中中中中中中")
  (re 53 1 (ℓ "乏丹乏") ∷
   rw 55 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   re 51 3 (ℓ "乀") ∷
   rw 51 q3 ∷
   rw⁻ 52 q4 ∷
   rw 53 q5 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q2 ∷
   re 52 3 (ℓ "乀") ∷
   rw 52 q3 ∷
   rw⁻ 53 q4 ∷
   rw 54 q5 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 57 q1 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q2 ∷
   re 53 3 (ℓ "乀") ∷
   rw 53 q3 ∷
   rw⁻ 54 q4 ∷
   rw 55 q5 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q2 ∷
   re 54 3 (ℓ "乀") ∷
   rw 54 q3 ∷
   rw⁻ 55 q4 ∷
   rw 56 q5 ∷
   re 57 1 (ℓ "乏丹乏") ∷
   rw 59 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q2 ∷
   re 55 3 (ℓ "乀") ∷
   rw 55 q3 ∷
   rw⁻ 56 q4 ∷
   rw 57 q5 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q2 ∷
   re 56 3 (ℓ "乀") ∷
   rw 56 q3 ∷
   rw⁻ 57 q4 ∷
   rw 58 q5 ∷
   re 59 1 (ℓ "乏丹乏") ∷
   rw 61 q1 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q2 ∷
   re 57 3 (ℓ "乀") ∷
   rw 57 q3 ∷
   rw⁻ 58 q4 ∷
   rw 59 q5 ∷
   re 60 1 (ℓ "乏丹乏") ∷
   rw 62 q1 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q2 ∷
   re 58 3 (ℓ "乀") ∷
   rw 58 q3 ∷
   rw⁻ 59 q4 ∷
   rw 60 q5 ∷
   re 61 1 (ℓ "乏丹乏") ∷
   rw 63 q1 ∷
   re 57 5 (ℓ "中") ∷
   rw 58 q6 ∷
   rw 59 q6 ∷
   rw 60 q6 ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q2 ∷
   re 62 3 (ℓ "乀") ∷
   rw 62 q3 ∷
   rw⁻ 63 q7 ∷
   rw 64 q5 ∷
   re 65 1 (ℓ "乏丹乏") ∷
   rw 67 q1 ∷
   re 61 5 (ℓ "乑") ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   rw 64 q6 ∷
   rw 65 q6 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q2 ∷
   re 67 3 (ℓ "乀") ∷
   rw 67 q3 ∷
   rw⁻ 68 q7 ∷
   rw 69 q5 ∷
   re 70 1 (ℓ "乏丹乏") ∷
   rw 72 q1 ∷
   re 66 5 (ℓ "乑") ∷
   rw 67 q6 ∷
   rw 68 q2 ∷
   rw 67 q8 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw 68 q1 ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q1 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q8 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q1 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q1 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q1 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q1 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q1 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   rw 48 q8 ∷
   re 47 1 (ℓ "乏乄乏") ∷
   rw 49 q1 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q8 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q1 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q1 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q1 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q1 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q1 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q1 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q1 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q1 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q1 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q1 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q10 ∷
   rw 21 q11 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q12 ∷
   rw 39 q12 ∷
   rw 40 q12 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "乑") ∷
   rw 42 q12 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q12 ∷
   rw 53 q12 ∷
   rw 54 q12 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乑") ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   rw 58 q12 ∷
   rw 59 q12 ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q12 ∷
   rw⁻ 62 q10 ∷
   rw⁻ 63 q10 ∷
   rw⁻ 64 q9 ∷
   rw⁻ 65 q10 ∷
   rw⁻ 66 q9 ∷
   rw⁻ 67 q9 ∷
   rw 68 q1 ∷
   rw 90 q13 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 91 q2 ∷
   re 92 3 (ℓ "乑") ∷
   re 92 1 (ℓ "乏丼临丼乏") ∷
   rw 98 q2 ∷
   re 96 3 (ℓ "乀") ∷
   rw 95 q14 ∷
   rw 94 q7 ∷
   rw 93 q15 ∷
   re 93 1 (ℓ "乏丹乏") ∷
   rw 92 q1 ∷
   re 93 5 (ℓ "乑") ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw 95 q1 ∷
   re 91 3 (ℓ "乀") ∷
   rw 92 q13 ∷
   rw 89 q13 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 90 q2 ∷
   re 91 3 (ℓ "乑") ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 97 q2 ∷
   re 95 3 (ℓ "乀") ∷
   rw 94 q14 ∷
   rw 93 q7 ∷
   rw 92 q15 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 91 q1 ∷
   re 92 5 (ℓ "乑") ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 94 q1 ∷
   re 90 3 (ℓ "乀") ∷
   rw 91 q13 ∷
   rw 88 q16 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 89 q2 ∷
   re 90 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 96 q2 ∷
   re 94 3 (ℓ "乀") ∷
   rw 93 q14 ∷
   rw 92 q4 ∷
   rw 91 q15 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 90 q1 ∷
   re 91 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q1 ∷
   re 89 3 (ℓ "乀") ∷
   rw 90 q16 ∷
   rw 87 q13 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 88 q2 ∷
   re 89 3 (ℓ "乑") ∷
   re 89 1 (ℓ "乏丼临丼乏") ∷
   rw 95 q2 ∷
   re 93 3 (ℓ "乀") ∷
   rw 92 q14 ∷
   rw 91 q7 ∷
   rw 90 q15 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 89 q1 ∷
   re 90 5 (ℓ "乑") ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 92 q1 ∷
   re 88 3 (ℓ "乀") ∷
   rw 89 q13 ∷
   rw 86 q16 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 87 q2 ∷
   re 88 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 94 q2 ∷
   re 92 3 (ℓ "乀") ∷
   rw 91 q14 ∷
   rw 90 q4 ∷
   rw 89 q15 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 88 q1 ∷
   re 89 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q1 ∷
   re 87 3 (ℓ "乀") ∷
   rw 88 q16 ∷
   rw 85 q16 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 86 q2 ∷
   re 87 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "乀") ∷
   rw 90 q14 ∷
   rw 89 q4 ∷
   rw 88 q15 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 87 q1 ∷
   re 88 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q1 ∷
   re 86 3 (ℓ "乀") ∷
   rw 87 q16 ∷
   rw 84 q17 ∷
   rw 83 q16 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 84 q2 ∷
   re 85 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乀") ∷
   rw 88 q14 ∷
   rw 87 q4 ∷
   rw 86 q15 ∷
   re 86 1 (ℓ "乏丹乏") ∷
   rw 85 q1 ∷
   re 86 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q1 ∷
   re 84 3 (ℓ "乀") ∷
   rw 85 q16 ∷
   rw 82 q16 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 83 q2 ∷
   re 84 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q2 ∷
   re 88 3 (ℓ "乀") ∷
   rw 87 q14 ∷
   rw 86 q4 ∷
   rw 85 q15 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 84 q1 ∷
   re 85 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q1 ∷
   re 83 3 (ℓ "乀") ∷
   rw 84 q16 ∷
   rw 81 q16 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 82 q2 ∷
   re 83 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乀") ∷
   rw 86 q14 ∷
   rw 85 q4 ∷
   rw 84 q15 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 83 q1 ∷
   re 84 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q1 ∷
   re 82 3 (ℓ "乀") ∷
   rw 83 q16 ∷
   rw 80 q16 ∷
   re 82 1 (ℓ "乏丹乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乀") ∷
   rw 85 q14 ∷
   rw 84 q4 ∷
   rw 83 q15 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 82 q1 ∷
   re 83 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q1 ∷
   re 81 3 (ℓ "乀") ∷
   rw 82 q16 ∷
   rw 79 q16 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 80 q2 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "乀") ∷
   rw 84 q14 ∷
   rw 83 q4 ∷
   rw 82 q15 ∷
   re 82 1 (ℓ "乏丹乏") ∷
   rw 81 q1 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q1 ∷
   re 80 3 (ℓ "乀") ∷
   rw 81 q16 ∷
   rw 78 q16 ∷
   re 80 1 (ℓ "乏丹乏") ∷
   rw 79 q2 ∷
   re 80 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乀") ∷
   rw 83 q14 ∷
   rw 82 q4 ∷
   rw 81 q15 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 80 q1 ∷
   re 81 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q1 ∷
   re 79 3 (ℓ "乀") ∷
   rw 80 q16 ∷
   rw⁻ 77 q18 ∷
   rw 78 q19 ∷
   rw⁻ 79 q18 ∷
   rw 76 q13 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 77 q2 ∷
   re 78 3 (ℓ "乑") ∷
   re 78 1 (ℓ "乏丼临丼乏") ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "乀") ∷
   rw 81 q14 ∷
   rw 80 q7 ∷
   rw 79 q15 ∷
   re 79 1 (ℓ "乏丹乏") ∷
   rw 78 q1 ∷
   re 79 5 (ℓ "乑") ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 81 q1 ∷
   re 77 3 (ℓ "乀") ∷
   rw 78 q13 ∷
   rw 75 q16 ∷
   re 77 1 (ℓ "乏丹乏") ∷
   rw 76 q2 ∷
   re 77 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "乀") ∷
   rw 80 q14 ∷
   rw 79 q4 ∷
   rw 78 q15 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 77 q1 ∷
   re 78 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q1 ∷ []) Eq.refl
