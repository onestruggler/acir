{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D258 (W : Ws) where

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
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 137 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 140 W
  q7 : Eqn
  q7 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q8 : Eqn
  q8 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q9 : Eqn
  q9 = wE 838 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 139 W
  q13 : Eqn
  q13 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CK30 CS03 CS03 CKd30 X3]: 157 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-CS03-CS03-CKd30-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乑中中乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑中中乒丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-CS03-CS03-CKd30-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乑中中乒丞") (ℓ "丞乑中中乒丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏久乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "乕") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q5 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q6 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乔") ∷
   rw⁻ 31 q2 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw⁻ 24 q7 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw⁻ 14 q8 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q5 ∷
   rw⁻ 6 q7 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q5 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q6 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q5 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q5 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q3 ∷
   rw 2 q10 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乑") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 3 q11 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q11 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q3 ∷
   rw 5 q12 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q2 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 7 q11 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q11 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q11 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q3 ∷
   rw 10 q10 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q11 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q11 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q7 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 20 q8 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q11 ∷
   rw 30 q7 ∷
   rw 31 q11 ∷
   rw 32 q11 ∷
   rw 33 q11 ∷
   rw 34 q10 ∷
   rw 35 q11 ∷
   rw 36 q11 ∷
   rw 37 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 839 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02 X3]: 227 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞") (ℓ "丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 64 q1 ∷
   rw⁻ 63 q2 ∷
   rw 62 q5 ∷
   rw 61 q5 ∷
   rw 60 q6 ∷
   rw 59 q5 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw⁻ 56 q7 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q5 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw⁻ 46 q8 ∷
   rw 45 q6 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw⁻ 38 q7 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q5 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q5 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q6 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q5 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q5 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 31 q2 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw⁻ 24 q7 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw⁻ 14 q8 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q5 ∷
   rw⁻ 6 q7 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q5 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q6 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q5 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q5 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q11 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 3 q11 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q11 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q3 ∷
   rw 5 q10 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q11 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 7 q11 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q7 ∷
   rw 8 q11 ∷
   rw 9 q11 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q10 ∷
   rw 15 q8 ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q7 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q10 ∷
   rw 30 q11 ∷
   rw 31 q11 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q3 ∷
   rw 34 q11 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q3 ∷
   rw 35 q11 ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q3 ∷
   rw 36 q11 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q3 ∷
   rw 37 q10 ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "乑") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q3 ∷
   rw 38 q11 ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q3 ∷
   rw 39 q11 ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q7 ∷
   rw 40 q11 ∷
   rw 41 q11 ∷
   rw 42 q11 ∷
   rw 43 q11 ∷
   rw 44 q11 ∷
   rw 45 q11 ∷
   rw 46 q10 ∷
   rw 47 q8 ∷
   rw 48 q11 ∷
   rw 49 q11 ∷
   rw 50 q11 ∷
   rw 51 q11 ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q7 ∷
   rw 58 q11 ∷
   rw 59 q11 ∷
   rw 60 q11 ∷
   rw 61 q10 ∷
   rw 62 q11 ∷
   rw 63 q11 ∷
   rw 64 q13 ∷ []) Eq.refl
