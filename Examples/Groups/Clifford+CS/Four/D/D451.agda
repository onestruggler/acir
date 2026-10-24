{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D451 (W : Ws) where

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
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 1208 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q11 : Eqn
  q11 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 1209 W

-- respell hyb CS02 CS02 CK20 CS02 CX23 CS03 CS03 CS03  -> CS03 CS03 CK30 CS03 CX32 CS02 CS02 CS02 : 424 steps
lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- : ⟪ (ℓ "丧丧乄丧乌中中中乑业中中中中中中乌中中乑中临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ
lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- = derive (ℓ "丧丧乄丧乌中中中乑业中中中中中中乌中中乑中临中中中业乑中中中中中中乌中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乌丧丧丧且乄丧丧丧丧丧丧与临") (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临")
  (rw 21 q1 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q4 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "乔") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   rw⁻ 16 q5 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q2 ∷
   rw 16 q3 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q3 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q2 ∷
   rw 13 q3 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q2 ∷
   rw 11 q3 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 9 q6 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q4 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "乔") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q2 ∷
   rw 6 q3 ∷
   rw⁻ 5 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 4 q5 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q2 ∷
   rw 1 q8 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q2 ∷
   rw 3 q9 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   rw 4 q8 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 9 q11 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   rw 16 q10 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q9 ∷
   rw 20 q8 ∷
   rw 21 q12 ∷
   rw 78 q1 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   rw⁻ 70 q11 ∷
   rw 69 q3 ∷
   rw 68 q3 ∷
   rw 67 q3 ∷
   rw⁻ 66 q5 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q2 ∷
   rw 66 q3 ∷
   rw⁻ 65 q2 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q2 ∷
   rw 65 q3 ∷
   rw⁻ 64 q2 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q2 ∷
   rw 64 q3 ∷
   rw⁻ 63 q2 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q2 ∷
   rw 63 q3 ∷
   rw⁻ 62 q2 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q2 ∷
   rw 62 q3 ∷
   rw⁻ 61 q2 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q2 ∷
   rw 61 q3 ∷
   rw⁻ 60 q2 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q2 ∷
   rw 60 q3 ∷
   rw⁻ 59 q2 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q2 ∷
   rw 59 q3 ∷
   rw⁻ 58 q2 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw⁻ 57 q2 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q2 ∷
   rw 57 q4 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (ℓ "乔") ∷
   rw⁻ 55 q6 ∷
   rw⁻ 54 q6 ∷
   rw⁻ 53 q6 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q2 ∷
   rw 52 q3 ∷
   rw⁻ 51 q2 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q2 ∷
   rw 51 q3 ∷
   rw⁻ 50 q2 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q2 ∷
   rw 50 q3 ∷
   rw⁻ 49 q2 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q2 ∷
   rw 49 q3 ∷
   rw⁻ 48 q2 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q2 ∷
   rw 48 q3 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q3 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q2 ∷
   rw 46 q3 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q3 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q3 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q3 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q2 ∷
   rw 42 q3 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q2 ∷
   rw 41 q3 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q2 ∷
   rw 40 q3 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q2 ∷
   rw 39 q3 ∷
   rw⁻ 38 q2 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q2 ∷
   rw 38 q3 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q2 ∷
   rw 37 q3 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q2 ∷
   rw 36 q3 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q2 ∷
   rw 35 q3 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (ℓ "丽") ∷
   rw⁻ 33 q5 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q2 ∷
   rw 33 q3 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q2 ∷
   rw 27 q4 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (ℓ "乔") ∷
   rw⁻ 25 q6 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q2 ∷
   rw 25 q3 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q13 ∷
   rw 22 q8 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q11 ∷
   rw 26 q9 ∷
   rw 27 q8 ∷
   rw 28 q8 ∷
   rw 29 q8 ∷
   rw 30 q8 ∷
   rw 31 q8 ∷
   rw 32 q8 ∷
   rw 33 q10 ∷
   rw 34 q8 ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   rw 38 q8 ∷
   rw 39 q8 ∷
   rw 40 q8 ∷
   rw 41 q8 ∷
   rw 42 q8 ∷
   rw 43 q8 ∷
   rw 44 q8 ∷
   rw 45 q8 ∷
   rw 46 q8 ∷
   rw 47 q8 ∷
   rw 48 q8 ∷
   rw 49 q8 ∷
   rw 50 q8 ∷
   rw 51 q8 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q9 ∷
   rw 57 q8 ∷
   rw 58 q8 ∷
   rw 59 q8 ∷
   rw 60 q8 ∷
   rw 61 q8 ∷
   rw 62 q8 ∷
   rw 63 q8 ∷
   rw 64 q8 ∷
   rw 65 q8 ∷
   rw 66 q10 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q2 ∷
   rw 68 q8 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q2 ∷
   rw 69 q8 ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q2 ∷
   rw 70 q8 ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q6 ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q2 ∷
   rw 72 q9 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乑") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q2 ∷
   rw 73 q8 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q2 ∷
   rw 74 q8 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q2 ∷
   rw 75 q8 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q2 ∷
   rw 76 q8 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q2 ∷
   rw 77 q8 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q2 ∷
   rw 78 q8 ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q12 ∷ []) Eq.refl
