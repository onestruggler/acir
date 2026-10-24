{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D429 (W : Ws) where

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
  q1 = wE 14 W
  q2 : Eqn
  q2 = wE 343 W
  q3 : Eqn
  q3 = wE 114 W
  q4 : Eqn
  q4 = wE 22 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = wE 23 W
  q7 : Eqn
  q7 = eqn (ℓ "丼业") (ℓ "业丼") (low₃-comm ((Swap ↑)) (S))
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = wE 338 W
  q10 : Eqn
  q10 = wE 12 W

-- hyb sym 23 @0321 part2: 91 steps
lem-hyb-sym-23-at0321-part2 : ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丼丼丠丼丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丼") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄") ⟫ʷ
lem-hyb-sym-23-at0321-part2 = derive (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丼丼丠丼丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丼") (ℓ "中中乑中乓丠丠丠临与丠丠丠丠丠丠乓丠丠临丠乄丠丠丠与临丠丠丠丠丠丠乓丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乓中中中业乑中中中中中中且乄")
  (rw 46 q1 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q1 ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 48 q1 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q1 ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q1 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q1 ∷
   rw 52 q2 ∷
   rw 53 q2 ∷
   rw 54 q2 ∷
   rw 55 q2 ∷
   re 57 1 (ℓ "丼临丼") ∷
   rw 56 q1 ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q1 ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 58 q1 ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 59 q1 ∷
   re 61 1 (ℓ "丼丠丼") ∷
   rw 60 q1 ∷
   re 62 1 (ℓ "丼丠丼") ∷
   rw 61 q1 ∷
   re 63 1 (ℓ "丼丠丼") ∷
   rw 62 q1 ∷
   re 64 1 (ℓ "丼丠丼") ∷
   rw 63 q1 ∷
   re 65 1 (ℓ "丼丠丼") ∷
   rw 64 q1 ∷
   re 66 1 (ℓ "丼丠丼") ∷
   rw 65 q1 ∷
   rw 66 q3 ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q4 ∷
   rw⁻ 69 q5 ∷
   rw 70 q6 ∷
   re 67 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q4 ∷
   rw⁻ 70 q5 ∷
   rw 71 q6 ∷
   re 68 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q4 ∷
   rw⁻ 71 q5 ∷
   rw 72 q6 ∷
   re 69 5 (ℓ "中") ∷
   rw 70 q7 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 71 q4 ∷
   rw⁻ 73 q8 ∷
   rw 74 q6 ∷
   re 71 5 (ℓ "乑") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q4 ∷
   rw⁻ 74 q5 ∷
   rw 75 q6 ∷
   re 72 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q4 ∷
   rw⁻ 75 q5 ∷
   rw 76 q6 ∷
   re 73 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q4 ∷
   rw⁻ 76 q5 ∷
   rw 77 q6 ∷
   re 74 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q4 ∷
   rw⁻ 77 q5 ∷
   rw 78 q6 ∷
   re 75 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q4 ∷
   rw⁻ 78 q5 ∷
   rw 79 q6 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q4 ∷
   rw⁻ 79 q5 ∷
   rw 80 q6 ∷
   re 77 5 (ℓ "中") ∷
   rw 78 q9 ∷
   rw 81 q10 ∷
   re 79 3 (ℓ "乄") ∷
   rw 80 q1 ∷ []) Eq.refl
