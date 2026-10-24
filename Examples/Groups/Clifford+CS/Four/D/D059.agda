{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D059 (W : Ws) where

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
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 563 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CK30 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乑丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CK30-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乑丞") (ℓ "丞乑丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乔") ∷
   rw⁻ 31 q2 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw⁻ 14 q7 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q5 ∷
   rw⁻ 6 q6 ∷
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
   rw 4 q4 ∷
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
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q10 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q10 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q10 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q9 ∷
   rw 17 q7 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q10 ∷
   rw 26 q10 ∷
   rw 27 q6 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q9 ∷
   rw 32 q10 ∷
   rw 33 q10 ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 137 W
  q13 : Eqn
  q13 = wE 564 W
  q14 : Eqn
  q14 = wE 139 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CKd30 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd30-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乒丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd30-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乒丞") (ℓ "丞乒丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏久乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q12 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乕") ∷
   rw⁻ 31 q2 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw⁻ 14 q7 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q5 ∷
   rw⁻ 6 q6 ∷
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
   rw 4 q4 ∷
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
   rw 1 q13 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏么乏") ∷
   rw 1 q3 ∷
   rw 2 q14 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乒") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q10 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q10 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q10 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q9 ∷
   rw 17 q7 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q10 ∷
   rw 26 q10 ∷
   rw 27 q6 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q9 ∷
   rw 32 q10 ∷
   rw 33 q10 ∷
   rw 34 q11 ∷ []) Eq.refl
