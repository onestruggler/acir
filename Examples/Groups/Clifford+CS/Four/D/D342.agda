{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D342 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 36 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = wE 37 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 464 W
  q7 : Eqn
  q7 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = wE 962 W
  q10 : Eqn
  q10 = wE 151 W
  q11 : Eqn
  q11 = wE 879 W
  q12 : Eqn
  q12 = wE 157 W
  q13 : Eqn
  q13 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q14 : Eqn
  q14 = wE 158 W
  q15 : Eqn
  q15 = wE 880 W
  q16 : Eqn
  q16 = wE 956 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part4: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part4 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业丹乏丼丠丼乏中中中中中中中中中中中中中中中中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丒乏丹乏丼丠丼乏乏丒丧丹丧丧乄丧乄乄中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part4 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业丹乏丼丠丼乏中中中中中中中中中中中中中中中中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丒乏丹乏丼丠丼乏乏丒丧丹丧丧乄丧乄乄中中中中中中乑业中中中中中中中中中")
  (rw 60 q1 ∷
   re 61 3 (ℓ "乀") ∷
   rw 61 q2 ∷
   rw⁻ 62 q3 ∷
   rw 63 q4 ∷
   re 64 1 (ℓ "乏丹乏") ∷
   rw 66 q5 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "乀") ∷
   rw 62 q2 ∷
   rw⁻ 63 q3 ∷
   rw 64 q4 ∷
   re 65 1 (ℓ "乏丹乏") ∷
   rw 67 q5 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q1 ∷
   re 63 3 (ℓ "乀") ∷
   rw 63 q2 ∷
   rw⁻ 64 q3 ∷
   rw 65 q4 ∷
   re 66 1 (ℓ "乏丹乏") ∷
   rw 68 q5 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q1 ∷
   re 64 3 (ℓ "乀") ∷
   rw 64 q2 ∷
   rw⁻ 65 q3 ∷
   rw 66 q4 ∷
   re 67 1 (ℓ "乏丹乏") ∷
   rw 69 q5 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q1 ∷
   re 65 3 (ℓ "乀") ∷
   rw 65 q2 ∷
   rw⁻ 66 q3 ∷
   rw 67 q4 ∷
   re 68 1 (ℓ "乏丹乏") ∷
   rw 70 q5 ∷
   re 64 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q1 ∷
   re 66 3 (ℓ "乀") ∷
   rw 66 q2 ∷
   rw⁻ 67 q3 ∷
   rw 68 q4 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 71 q5 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "乀") ∷
   rw 67 q2 ∷
   rw⁻ 68 q3 ∷
   rw 69 q4 ∷
   re 70 1 (ℓ "乏丹乏") ∷
   rw 72 q5 ∷
   re 66 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q1 ∷
   re 68 3 (ℓ "乀") ∷
   rw 68 q2 ∷
   rw⁻ 69 q3 ∷
   rw 70 q4 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 73 q5 ∷
   re 67 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q1 ∷
   re 69 3 (ℓ "乀") ∷
   rw 69 q2 ∷
   rw⁻ 70 q3 ∷
   rw 71 q4 ∷
   re 72 1 (ℓ "乏丹乏") ∷
   rw 74 q5 ∷
   re 68 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q1 ∷
   re 70 3 (ℓ "乀") ∷
   rw 70 q2 ∷
   rw⁻ 71 q3 ∷
   rw 72 q4 ∷
   re 73 1 (ℓ "乏丹乏") ∷
   rw 75 q5 ∷
   re 69 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q1 ∷
   re 71 3 (ℓ "乀") ∷
   rw 71 q2 ∷
   rw⁻ 72 q3 ∷
   rw 73 q4 ∷
   re 74 1 (ℓ "乏丹乏") ∷
   rw 76 q5 ∷
   re 70 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q1 ∷
   re 72 3 (ℓ "乀") ∷
   rw 72 q2 ∷
   rw⁻ 73 q3 ∷
   rw 74 q4 ∷
   re 75 1 (ℓ "乏丹乏") ∷
   rw 77 q5 ∷
   re 71 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q1 ∷
   re 73 3 (ℓ "乀") ∷
   rw 73 q2 ∷
   rw⁻ 74 q3 ∷
   rw 75 q4 ∷
   re 76 1 (ℓ "乏丹乏") ∷
   rw 78 q5 ∷
   re 72 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q1 ∷
   re 74 3 (ℓ "乀") ∷
   rw 74 q2 ∷
   rw⁻ 75 q3 ∷
   rw 76 q4 ∷
   re 77 1 (ℓ "乏丹乏") ∷
   rw 79 q5 ∷
   re 73 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q1 ∷
   re 75 3 (ℓ "乀") ∷
   rw 75 q2 ∷
   rw⁻ 76 q3 ∷
   rw 77 q4 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 80 q5 ∷
   re 74 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q1 ∷
   re 76 3 (ℓ "乀") ∷
   rw 76 q2 ∷
   rw⁻ 77 q3 ∷
   rw 78 q4 ∷
   re 79 1 (ℓ "乏丹乏") ∷
   rw 81 q5 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q1 ∷
   re 77 3 (ℓ "乀") ∷
   rw 77 q2 ∷
   rw⁻ 78 q3 ∷
   rw 79 q4 ∷
   re 80 1 (ℓ "乏丹乏") ∷
   rw 82 q5 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q1 ∷
   re 78 3 (ℓ "乀") ∷
   rw 78 q2 ∷
   rw⁻ 79 q3 ∷
   rw 80 q4 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 83 q5 ∷
   re 77 5 (ℓ "中") ∷
   rw 78 q1 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q5 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q5 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q5 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q5 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q5 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q5 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q5 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q5 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q5 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q5 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q5 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q5 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q5 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q5 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q5 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   rw 59 q6 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q5 ∷
   rw 57 q6 ∷
   rw 56 q6 ∷
   rw 55 q6 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q5 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q5 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q5 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q5 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q5 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q5 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   rw 24 q7 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   rw 23 q9 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q10 ∷
   rw 50 q10 ∷
   rw 51 q10 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q10 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw⁻ 72 q8 ∷
   rw⁻ 73 q8 ∷
   rw⁻ 74 q7 ∷
   rw⁻ 75 q8 ∷
   rw⁻ 76 q7 ∷
   rw⁻ 77 q7 ∷
   rw 78 q5 ∷
   rw 100 q11 ∷
   re 102 1 (ℓ "乏丹乏") ∷
   rw 101 q1 ∷
   re 102 3 (ℓ "乑") ∷
   re 102 1 (ℓ "乏丼临丼乏") ∷
   rw 108 q1 ∷
   re 106 3 (ℓ "乀") ∷
   rw 105 q12 ∷
   rw 104 q13 ∷
   rw 103 q14 ∷
   re 103 1 (ℓ "乏丹乏") ∷
   rw 102 q5 ∷
   re 103 5 (ℓ "乑") ∷
   re 103 1 (ℓ "乏乄乏") ∷
   rw 105 q5 ∷
   re 101 3 (ℓ "乀") ∷
   rw 102 q11 ∷
   rw 99 q11 ∷
   re 101 1 (ℓ "乏丹乏") ∷
   rw 100 q1 ∷
   re 101 3 (ℓ "乑") ∷
   re 101 1 (ℓ "乏丼临丼乏") ∷
   rw 107 q1 ∷
   re 105 3 (ℓ "乀") ∷
   rw 104 q12 ∷
   rw 103 q13 ∷
   rw 102 q14 ∷
   re 102 1 (ℓ "乏丹乏") ∷
   rw 101 q5 ∷
   re 102 5 (ℓ "乑") ∷
   re 102 1 (ℓ "乏乄乏") ∷
   rw 104 q5 ∷
   re 100 3 (ℓ "乀") ∷
   rw 101 q11 ∷
   rw 98 q15 ∷
   re 100 1 (ℓ "乏丹乏") ∷
   rw 99 q1 ∷
   re 100 3 (ℓ "中") ∷
   re 100 1 (ℓ "乏丼丠丼乏") ∷
   rw 106 q1 ∷
   re 104 3 (ℓ "乀") ∷
   rw 103 q12 ∷
   rw 102 q3 ∷
   rw 101 q14 ∷
   re 101 1 (ℓ "乏丹乏") ∷
   rw 100 q5 ∷
   re 101 5 (ℓ "中") ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw 103 q5 ∷
   re 99 3 (ℓ "乀") ∷
   rw 100 q15 ∷
   rw 97 q11 ∷
   re 99 1 (ℓ "乏丹乏") ∷
   rw 98 q1 ∷
   re 99 3 (ℓ "乑") ∷
   re 99 1 (ℓ "乏丼临丼乏") ∷
   rw 105 q1 ∷
   re 103 3 (ℓ "乀") ∷
   rw 102 q12 ∷
   rw 101 q13 ∷
   rw 100 q14 ∷
   re 100 1 (ℓ "乏丹乏") ∷
   rw 99 q5 ∷
   re 100 5 (ℓ "乑") ∷
   re 100 1 (ℓ "乏乄乏") ∷
   rw 102 q5 ∷
   re 98 3 (ℓ "乀") ∷
   rw 99 q11 ∷
   rw 96 q15 ∷
   re 98 1 (ℓ "乏丹乏") ∷
   rw 97 q1 ∷
   re 98 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丼丠丼乏") ∷
   rw 104 q1 ∷
   re 102 3 (ℓ "乀") ∷
   rw 101 q12 ∷
   rw 100 q3 ∷
   rw 99 q14 ∷
   re 99 1 (ℓ "乏丹乏") ∷
   rw 98 q5 ∷
   re 99 5 (ℓ "中") ∷
   re 99 1 (ℓ "乏丧乏") ∷
   rw 101 q5 ∷
   re 97 3 (ℓ "乀") ∷
   rw 98 q15 ∷
   rw 95 q15 ∷
   re 97 1 (ℓ "乏丹乏") ∷
   rw 96 q1 ∷
   re 97 3 (ℓ "中") ∷
   re 97 1 (ℓ "乏丼丠丼乏") ∷
   rw 103 q1 ∷
   re 101 3 (ℓ "乀") ∷
   rw 100 q12 ∷
   rw 99 q3 ∷
   rw 98 q14 ∷
   re 98 1 (ℓ "乏丹乏") ∷
   rw 97 q5 ∷
   re 98 5 (ℓ "中") ∷
   re 98 1 (ℓ "乏丧乏") ∷
   rw 100 q5 ∷
   re 96 3 (ℓ "乀") ∷
   rw 97 q15 ∷
   rw 94 q16 ∷
   rw 93 q15 ∷
   re 95 1 (ℓ "乏丹乏") ∷
   rw 94 q1 ∷
   re 95 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丼丠丼乏") ∷
   rw 101 q1 ∷
   re 99 3 (ℓ "乀") ∷
   rw 98 q12 ∷
   rw 97 q3 ∷
   rw 96 q14 ∷
   re 96 1 (ℓ "乏丹乏") ∷
   rw 95 q5 ∷
   re 96 5 (ℓ "中") ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q5 ∷
   re 94 3 (ℓ "乀") ∷
   rw 95 q15 ∷
   rw 92 q15 ∷
   re 94 1 (ℓ "乏丹乏") ∷
   rw 93 q1 ∷
   re 94 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丼丠丼乏") ∷
   rw 100 q1 ∷
   re 98 3 (ℓ "乀") ∷
   rw 97 q12 ∷
   rw 96 q3 ∷
   rw 95 q14 ∷
   re 95 1 (ℓ "乏丹乏") ∷
   rw 94 q5 ∷ []) Eq.refl
