{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D180 (W : Ws) where

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
  q1 = wE 12 W
  q2 : Eqn
  q2 = wE 345 W
  q3 : Eqn
  q3 = wE 49 W
  q4 : Eqn
  q4 = wE 50 W
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 20 W
  q7 : Eqn
  q7 = wE 364 W
  q8 : Eqn
  q8 = wE 367 W
  q9 : Eqn
  q9 = wE 22 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 23 W
  q12 : Eqn
  q12 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = wE 114 W
  q14 : Eqn
  q14 = wE 14 W
  q15 : Eqn
  q15 = wE 343 W

-- AXIOM LF @0321 part2: 176 steps
lem-AXIOM-LF-at0321-part2 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丼丠丼丼临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丼") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄乢中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠乢中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-AXIOM-LF-at0321-part2 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丼丠丼丼临临乥中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧乥中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丼") (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄乢中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠乢中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (re 26 3 (ℓ "丧") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乄") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乄") ∷
   re 30 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 29 q2 ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q4 ∷
   rw 34 q6 ∷
   rw 35 q2 ∷
   rw 36 q7 ∷
   rw 29 q8 ∷
   re 29 8 (ℓ "乢") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q9 ∷
   rw⁻ 32 q10 ∷
   rw 33 q11 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q9 ∷
   rw⁻ 33 q10 ∷
   rw 34 q11 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q9 ∷
   rw⁻ 34 q10 ∷
   rw 35 q11 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q9 ∷
   rw⁻ 35 q12 ∷
   rw 36 q11 ∷
   re 33 5 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q9 ∷
   rw⁻ 36 q10 ∷
   rw 37 q11 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q9 ∷
   rw⁻ 37 q10 ∷
   rw 38 q11 ∷
   re 35 5 (ℓ "中") ∷
   rw 36 q13 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q14 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q14 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q14 ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q14 ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q14 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q14 ∷
   re 44 1 (ℓ "丼临丼") ∷
   rw 43 q14 ∷
   rw 44 q15 ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q14 ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 46 q14 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q14 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 48 q14 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q14 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q14 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q14 ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q14 ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q14 ∷
   rw 54 q13 ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q14 ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q14 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q14 ∷
   re 59 1 (ℓ "丼临丼") ∷
   rw 58 q14 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 59 q14 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 60 q14 ∷
   re 62 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 61 q2 ∷
   rw 62 q3 ∷
   rw 63 q4 ∷
   rw 64 q5 ∷
   rw 65 q4 ∷
   rw 66 q6 ∷
   rw 67 q2 ∷
   rw 68 q7 ∷
   rw 61 q8 ∷
   re 61 8 (ℓ "乢") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q9 ∷
   rw⁻ 64 q10 ∷
   rw 65 q11 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q9 ∷
   rw⁻ 65 q10 ∷
   rw 66 q11 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼临丼乏") ∷
   rw 64 q9 ∷
   rw⁻ 66 q12 ∷
   rw 67 q11 ∷
   re 64 5 (ℓ "乑") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q9 ∷
   rw⁻ 67 q10 ∷
   rw 68 q11 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q9 ∷
   rw⁻ 68 q12 ∷
   rw 69 q11 ∷
   re 66 5 (ℓ "乑") ∷
   re 68 1 (ℓ "乏丼临丼乏") ∷
   rw 67 q9 ∷
   rw⁻ 69 q12 ∷
   rw 70 q11 ∷
   re 67 5 (ℓ "乑") ∷
   rw 68 q13 ∷
   re 70 1 (ℓ "丼临丼") ∷
   rw 69 q14 ∷
   rw 70 q15 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 71 q14 ∷
   rw 72 q15 ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 73 q14 ∷
   re 75 1 (ℓ "丼丠丼") ∷
   rw 74 q14 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 75 q14 ∷
   re 77 1 (ℓ "丼临丼") ∷
   rw 76 q14 ∷
   rw 77 q15 ∷
   re 79 1 (ℓ "丼丠丼") ∷
   rw 78 q14 ∷
   re 80 1 (ℓ "丼丠丼") ∷
   rw 79 q14 ∷
   re 81 1 (ℓ "丼丠丼") ∷
   rw 80 q14 ∷
   re 82 1 (ℓ "丼丠丼") ∷
   rw 81 q14 ∷
   re 83 1 (ℓ "丼丠丼") ∷
   rw 82 q14 ∷
   re 84 1 (ℓ "丼丠丼") ∷
   rw 83 q14 ∷
   rw 84 q13 ∷
   re 86 1 (ℓ "丼丠丼") ∷
   rw 85 q14 ∷
   re 87 1 (ℓ "丼丠丼") ∷
   rw 86 q14 ∷
   re 88 1 (ℓ "丼临丼") ∷
   rw 87 q14 ∷
   re 89 1 (ℓ "丼丠丼") ∷
   rw 88 q14 ∷
   re 90 1 (ℓ "丼临丼") ∷
   rw 89 q14 ∷
   re 91 1 (ℓ "丼临丼") ∷
   rw 90 q14 ∷
   rw 91 q14 ∷ []) Eq.refl
