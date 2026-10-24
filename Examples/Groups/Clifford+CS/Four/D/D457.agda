{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D457 (W : Ws) where

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
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 157 W
  q4 : Eqn
  q4 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q5 : Eqn
  q5 = wE 158 W
  q6 : Eqn
  q6 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q7 : Eqn
  q7 = wE 879 W
  q8 : Eqn
  q8 = wE 880 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 881 W
  q11 : Eqn
  q11 = eqn (ℓ "丒业") (ℓ "业丒") (low-comm ((X ↑)) ((S ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q13 : Eqn
  q13 = wE 882 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 7 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part2: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 : ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑丒乏乄乏丹丒丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乏乄乏並丶丶乇丶乇乇並") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 = derive (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑丒乏乄乏丹丒丧丧乄丧乄乄") (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乏乄乏並丶丶乇丶乇乇並")
  (rw 57 q1 ∷
   re 55 3 (ℓ "乑") ∷
   rw 56 q2 ∷
   re 55 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乀") ∷
   rw 58 q3 ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 55 q2 ∷
   re 56 5 (ℓ "乑") ∷
   rw 58 q1 ∷
   rw 57 q6 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q2 ∷
   rw 57 q7 ∷
   rw⁻ 56 q6 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q2 ∷
   rw 55 q1 ∷
   rw 54 q6 ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw 55 q2 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q2 ∷
   re 54 1 (ℓ "乏丼临丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乀") ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 54 q2 ∷
   re 55 5 (ℓ "乑") ∷
   rw 57 q1 ∷
   rw 56 q6 ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw 57 q2 ∷
   rw 56 q7 ∷
   rw⁻ 55 q6 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乑") ∷
   rw 57 q2 ∷
   rw 54 q1 ∷
   rw 53 q6 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q2 ∷
   rw 53 q8 ∷
   rw⁻ 52 q6 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q2 ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乀") ∷
   rw 56 q3 ∷
   rw 55 q9 ∷
   rw 54 q5 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 53 q2 ∷
   re 54 5 (ℓ "中") ∷
   rw 56 q1 ∷
   rw 55 q6 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q2 ∷
   rw 55 q8 ∷
   rw⁻ 54 q6 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q2 ∷
   rw 53 q1 ∷
   rw 52 q6 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q2 ∷
   rw 52 q7 ∷
   rw⁻ 51 q6 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q2 ∷
   re 52 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乀") ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q2 ∷
   re 53 5 (ℓ "乑") ∷
   rw 55 q1 ∷
   rw 54 q6 ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw 55 q2 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q2 ∷
   rw 52 q1 ∷
   rw 51 q6 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q2 ∷
   rw 51 q8 ∷
   rw⁻ 50 q6 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q2 ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "乀") ∷
   rw 54 q3 ∷
   rw 53 q9 ∷
   rw 52 q5 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 51 q2 ∷
   re 52 5 (ℓ "中") ∷
   rw 54 q1 ∷
   rw 53 q6 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q2 ∷
   rw 53 q8 ∷
   rw⁻ 52 q6 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q2 ∷
   rw 51 q1 ∷
   rw 50 q6 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q2 ∷
   rw 50 q8 ∷
   rw⁻ 49 q6 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q2 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乀") ∷
   rw 53 q3 ∷
   rw 52 q9 ∷
   rw 51 q5 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q2 ∷
   re 51 5 (ℓ "中") ∷
   rw 53 q1 ∷
   rw 52 q6 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q2 ∷
   rw 52 q8 ∷
   rw⁻ 51 q6 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q2 ∷
   rw 48 q10 ∷
   rw 49 q1 ∷
   rw 48 q6 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   rw 48 q8 ∷
   rw⁻ 47 q6 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q2 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乀") ∷
   rw 51 q3 ∷
   rw 50 q9 ∷
   rw 49 q5 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q2 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q1 ∷
   rw 50 q6 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q2 ∷
   rw 50 q8 ∷
   rw⁻ 49 q6 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q2 ∷
   rw 48 q1 ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   rw 47 q8 ∷
   rw⁻ 46 q6 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q2 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "乀") ∷
   rw 50 q3 ∷
   rw 49 q9 ∷
   rw 48 q5 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q2 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q1 ∷
   rw 49 q6 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q2 ∷
   rw 49 q8 ∷
   rw⁻ 48 q6 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q2 ∷
   rw 47 q1 ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   rw 46 q8 ∷
   rw⁻ 45 q6 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q2 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q3 ∷
   rw 48 q9 ∷
   rw 47 q5 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q2 ∷
   re 47 5 (ℓ "中") ∷
   rw 49 q1 ∷
   rw 48 q6 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   rw 48 q8 ∷
   rw⁻ 47 q6 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q2 ∷
   rw 46 q1 ∷
   rw 45 q6 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   rw 45 q8 ∷
   rw⁻ 44 q6 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q2 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q3 ∷
   rw 47 q9 ∷
   rw 46 q5 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q2 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q1 ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   rw 47 q8 ∷
   rw⁻ 46 q6 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q2 ∷
   rw 45 q1 ∷
   rw 44 q6 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q2 ∷
   rw 44 q8 ∷
   rw⁻ 43 q6 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q3 ∷
   rw 46 q9 ∷
   rw 45 q5 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q2 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q1 ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   rw 46 q8 ∷
   rw⁻ 45 q6 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q2 ∷
   rw 44 q1 ∷
   rw 43 q6 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q2 ∷
   rw 43 q8 ∷
   rw⁻ 42 q6 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q2 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q3 ∷
   rw 45 q9 ∷
   rw 44 q5 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q2 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q1 ∷
   rw 45 q6 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   rw 45 q8 ∷
   rw⁻ 44 q6 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q2 ∷
   rw⁻ 41 q11 ∷
   rw⁻ 42 q12 ∷
   rw⁻ 43 q11 ∷
   rw 42 q1 ∷
   rw 41 q6 ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw 42 q2 ∷
   rw 41 q7 ∷
   rw⁻ 40 q6 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乑") ∷
   rw 42 q2 ∷
   re 41 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q2 ∷
   re 42 5 (ℓ "乑") ∷
   rw 44 q1 ∷
   rw 43 q6 ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw 44 q2 ∷
   rw 43 q7 ∷
   rw⁻ 42 q6 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乑") ∷
   rw 44 q2 ∷
   rw 41 q1 ∷
   rw 40 q6 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   rw 40 q8 ∷
   rw⁻ 39 q6 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q2 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q3 ∷
   rw 42 q9 ∷
   rw 41 q5 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q2 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q1 ∷
   rw 42 q6 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q2 ∷
   rw 42 q8 ∷
   rw⁻ 41 q6 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q2 ∷
   rw 40 q1 ∷
   rw 39 q6 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q2 ∷
   rw 39 q8 ∷
   rw⁻ 38 q6 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q2 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q3 ∷
   rw 41 q9 ∷
   rw 40 q5 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q2 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q1 ∷
   rw 41 q6 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q2 ∷
   rw 41 q8 ∷
   rw⁻ 40 q6 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q2 ∷
   rw 39 q1 ∷
   rw 38 q6 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q2 ∷
   rw 38 q8 ∷
   rw⁻ 37 q6 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q2 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q3 ∷
   rw 40 q9 ∷
   rw 39 q5 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q2 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q1 ∷
   rw 40 q6 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   rw 40 q8 ∷
   rw⁻ 39 q6 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q2 ∷
   rw⁻ 36 q11 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q11 ∷
   rw 37 q1 ∷
   rw 36 q6 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q2 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q2 ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q2 ∷
   re 37 5 (ℓ "乑") ∷
   rw 39 q1 ∷
   rw 38 q6 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q2 ∷
   rw 38 q7 ∷
   rw⁻ 37 q6 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q2 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q11 ∷
   rw 35 q1 ∷
   rw 34 q6 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q2 ∷
   rw 34 q7 ∷
   rw⁻ 33 q6 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q2 ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q2 ∷
   re 35 5 (ℓ "乑") ∷
   rw 37 q1 ∷
   rw 36 q6 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q2 ∷
   rw 36 q7 ∷
   rw⁻ 35 q6 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q2 ∷
   rw 32 q10 ∷
   rw 26 q13 ∷
   rw 64 q14 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q16 ∷
   rw 60 q15 ∷
   rw 59 q16 ∷
   rw 58 q16 ∷
   re 57 1 (ℓ "乏乄乏") ∷ []) Eq.refl
