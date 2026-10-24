{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D459 (W : Ws) where

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
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 464 W
  q7 : Eqn
  q7 = wE 1215 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = wE 880 W
  q10 : Eqn
  q10 = wE 157 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 158 W
  q13 : Eqn
  q13 = wE 879 W
  q14 : Eqn
  q14 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = wE 881 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part0: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part0 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丠丠丠临丠丠乀中中中中中中乑业中丒丹中丒乏乏中中中中中中中乀中中中乑中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part0 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄") (ℓ "丒丠丠临丠临临丒丠丠丠临丠丠乀中中中中中中乑业中丒丹中丒乏乏中中中中中中中乀中中中乑中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄")
  (rw 39 q1 ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q5 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q5 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q3 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乀") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "乑") ∷
   rw 22 q8 ∷
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
   re 32 3 (ℓ "乀") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q5 ∷
   rw 39 q9 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q5 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q5 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   rw 41 q9 ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q5 ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   rw 38 q9 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   rw 39 q12 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q5 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q5 ∷
   rw 40 q9 ∷
   rw⁻ 39 q2 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q5 ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q5 ∷
   rw 37 q13 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q5 ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q10 ∷
   rw 39 q14 ∷
   rw 38 q12 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q5 ∷
   re 38 5 (ℓ "乑") ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q5 ∷
   rw 39 q13 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "乑") ∷
   rw 40 q5 ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   rw 36 q9 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q5 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q5 ∷
   re 37 5 (ℓ "中") ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   rw 38 q9 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   rw 35 q9 ∷
   rw⁻ 34 q2 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q5 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q5 ∷
   re 36 5 (ℓ "中") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q5 ∷
   rw 37 q9 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q5 ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   rw 34 q9 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q5 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q12 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q5 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   rw 36 q9 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q5 ∷
   rw 32 q15 ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   rw 32 q9 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q5 ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q10 ∷
   rw 34 q11 ∷
   rw 33 q12 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   re 33 5 (ℓ "中") ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   rw 34 q9 ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q5 ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   rw 31 q9 ∷
   rw⁻ 30 q2 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q5 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q12 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q5 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   rw 33 q9 ∷
   rw⁻ 32 q2 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q5 ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   rw 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q5 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   rw 31 q12 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q5 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   rw 32 q9 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q5 ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   rw 29 q9 ∷
   rw⁻ 28 q2 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q5 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   rw 31 q9 ∷
   rw⁻ 30 q2 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q5 ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   rw 28 q9 ∷
   rw⁻ 27 q2 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q5 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   rw 29 q12 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   rw 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q5 ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   rw 27 q9 ∷
   rw⁻ 26 q2 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q5 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   rw 28 q12 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   rw 29 q9 ∷
   rw⁻ 28 q2 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   rw 27 q1 ∷
   rw 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q5 ∷
   rw 26 q9 ∷
   rw⁻ 25 q2 ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q5 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   rw 27 q12 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   rw 28 q9 ∷
   rw⁻ 27 q2 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q5 ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q5 ∷
   rw 25 q9 ∷
   rw⁻ 24 q2 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q5 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   rw 26 q12 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q5 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q1 ∷ []) Eq.refl
