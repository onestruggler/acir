{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D419 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 629 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 21 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q11 : Eqn
  q11 = wE 51 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 739 W
  q14 : Eqn
  q14 = wE 519 W
  q15 : Eqn
  q15 = wE 518 W
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q18 : Eqn
  q18 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q19 : Eqn
  q19 = wE 571 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q22 : Eqn
  q22 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X2 CSd12 X2] part2: 223 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CSd12-X2-part2 : ⟪ (ℓ "丧丧丧乄丧丧乌中丘丷丘中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CSd12-X2-part2 = derive (ℓ "丧丧丧乄丧丧乌中丘丷丘中中中中中乑业中中中中中中中中中乌中中中乑中中") (ℓ "丘丷丘中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q4 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q6 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q12 ∷
   re 9 5 (ℓ "中") ∷
   rw 11 q1 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q7 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q14 ∷
   rw 1 q14 ∷
   rw 0 q14 ∷
   rw 34 q1 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q4 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q16 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "乔") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   rw⁻ 27 q17 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q4 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw⁻ 17 q18 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q16 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "乔") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q4 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q4 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q4 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q4 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q4 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 9 q17 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw 6 q16 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q6 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q6 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q6 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q20 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q6 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q6 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q21 ∷
   rw 10 q6 ∷
   rw 11 q6 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q20 ∷
   rw 17 q22 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q6 ∷
   rw 27 q21 ∷
   rw 28 q6 ∷
   rw 29 q6 ∷
   rw 30 q6 ∷
   rw 31 q20 ∷
   rw 32 q6 ∷
   rw 33 q6 ∷
   rw 34 q7 ∷ []) Eq.refl
