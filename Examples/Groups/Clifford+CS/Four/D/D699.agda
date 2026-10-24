{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD699 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D699 (W : Ws) (Sᴰ : SD699) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-hyb-sym-23-at0213 : St 1896
  lem-hyb-sym-23-at0213 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = sE 1896 lem-hyb-sym-23-at0213
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 1208 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q13 : Eqn
  q13 = wE 31 W
  q14 : Eqn
  q14 = wE 1209 W

-- respell hyb CS02 CS02 CK20 CS02 CX21 CS01 CS01 CS01  -> CS03 CS03 CK30 CS03 CX32 CS02 CS02 CS02 : 425 steps
lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- : ⟪ (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") ⟫ʷ ≈ ⟪ (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临") ⟫ʷ
lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- = derive (ℓ "丧丧乄丧乆丠丠丠临与丠丠丠丠丠丠乆丠丠临丠乑丠丠丠与临丠丠丠丠丠丠乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与与临丠丠丠丠丠丠丠丠丠乆丧丧丧且乄丧丧丧丧丧丧业乑") (ℓ "中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临")
  (rw 0 q1 ∷
   rw 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q5 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "乔") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q4 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw⁻ 16 q6 ∷
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
   rw⁻ 9 q7 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q3 ∷
   rw 9 q5 ∷
   rw⁻ 8 q3 ∷
   re 9 3 (ℓ "乔") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q4 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q3 ∷
   rw 7 q4 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 4 q6 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q8 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q3 ∷
   rw 3 q10 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乑") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q11 ∷
   rw 5 q9 ∷
   rw 6 q9 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q12 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q11 ∷
   rw 17 q9 ∷
   rw 18 q9 ∷
   rw 19 q10 ∷
   rw 20 q9 ∷
   rw 21 q13 ∷
   rw 78 q2 ∷
   rw 77 q4 ∷
   rw 76 q4 ∷
   rw 75 q4 ∷
   rw 74 q4 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q5 ∷
   rw⁻ 70 q12 ∷
   rw 69 q4 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   rw⁻ 66 q6 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q3 ∷
   rw 66 q4 ∷
   rw⁻ 65 q3 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q3 ∷
   rw 65 q4 ∷
   rw⁻ 64 q3 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q3 ∷
   rw 64 q4 ∷
   rw⁻ 63 q3 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q3 ∷
   rw 63 q4 ∷
   rw⁻ 62 q3 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q3 ∷
   rw 62 q4 ∷
   rw⁻ 61 q3 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q3 ∷
   rw 61 q4 ∷
   rw⁻ 60 q3 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q3 ∷
   rw 60 q4 ∷
   rw⁻ 59 q3 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q3 ∷
   rw 59 q4 ∷
   rw⁻ 58 q3 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q3 ∷
   rw 58 q4 ∷
   rw⁻ 57 q3 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q3 ∷
   rw 57 q5 ∷
   rw⁻ 56 q3 ∷
   re 57 3 (ℓ "乔") ∷
   rw⁻ 55 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 52 q7 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q3 ∷
   rw 52 q4 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q4 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q3 ∷
   rw 50 q4 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q4 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q3 ∷
   rw 48 q4 ∷
   rw⁻ 47 q3 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q3 ∷
   rw 47 q4 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q3 ∷
   rw 46 q4 ∷
   rw⁻ 45 q3 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q3 ∷
   rw 45 q4 ∷
   rw⁻ 44 q3 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q3 ∷
   rw 44 q4 ∷
   rw⁻ 43 q3 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q3 ∷
   rw 43 q4 ∷
   rw⁻ 42 q3 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q3 ∷
   rw 42 q4 ∷
   rw⁻ 41 q3 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q3 ∷
   rw 41 q4 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q3 ∷
   rw 40 q4 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q3 ∷
   rw 39 q4 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q4 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q4 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   rw⁻ 33 q6 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q4 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
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
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q5 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "乔") ∷
   rw⁻ 25 q7 ∷
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
   rw 23 q14 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q12 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q11 ∷
   rw 34 q9 ∷
   rw 35 q9 ∷
   rw 36 q9 ∷
   rw 37 q9 ∷
   rw 38 q9 ∷
   rw 39 q9 ∷
   rw 40 q9 ∷
   rw 41 q9 ∷
   rw 42 q9 ∷
   rw 43 q9 ∷
   rw 44 q9 ∷
   rw 45 q9 ∷
   rw 46 q9 ∷
   rw 47 q9 ∷
   rw 48 q9 ∷
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 51 q9 ∷
   rw 52 q12 ∷
   rw 53 q12 ∷
   rw 54 q12 ∷
   rw 55 q12 ∷
   rw 56 q10 ∷
   rw 57 q9 ∷
   rw 58 q9 ∷
   rw 59 q9 ∷
   rw 60 q9 ∷
   rw 61 q9 ∷
   rw 62 q9 ∷
   rw 63 q9 ∷
   rw 64 q9 ∷
   rw 65 q9 ∷
   rw 66 q11 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q3 ∷
   rw 68 q9 ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q3 ∷
   rw 69 q9 ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q3 ∷
   rw 70 q9 ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q7 ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q3 ∷
   rw 72 q10 ∷
   rw 73 q3 ∷
   re 71 3 (ℓ "乑") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q3 ∷
   rw 73 q9 ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q3 ∷
   rw 74 q9 ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q3 ∷
   rw 75 q9 ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q3 ∷
   rw 76 q9 ∷
   rw 77 q3 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q3 ∷
   rw 77 q9 ∷
   rw 78 q3 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q3 ∷
   rw 78 q9 ∷
   rw 79 q3 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q13 ∷ []) Eq.refl
