{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D321 (W : Ws) where

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
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = wE 944 W
  q10 : Eqn
  q10 = wE 151 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 CSd01 CKd10 CS01 CS01 X1]: 125 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-CKd10-CS01-CS01-X1 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒両丵丠丠丒") ⟫ʷ ≈ ⟪ (ℓ "丒両丵丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CSd01-CKd10-CS01-CS01-X1 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒両丵丠丠丒") (ℓ "丒両丵丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q6 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   rw 14 q7 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q6 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q8 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乀") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q10 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
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
   re 30 3 (ℓ "乀") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q6 ∷ []) Eq.refl
