{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D463 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 27 W
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = wE 36 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 37 W
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 800 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part4: 57 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part4 : ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠丠临丠丠乀丧丧乄丧乄乄中中中中中中乑业中中中中並丽丽丽丽丽並乀中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part4 = derive (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丠丠丠临丠丠乀丧丧乄丧乄乄中中中中中中乑业中中中中並丽丽丽丽丽並乀中中中乑中中") (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q1 ∷
   rw 55 q2 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q1 ∷
   rw 56 q2 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q1 ∷
   rw 57 q2 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q1 ∷
   rw 58 q2 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q1 ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q3 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q4 ∷
   rw⁻ 36 q5 ∷
   rw 37 q6 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q4 ∷
   rw⁻ 37 q5 ∷
   rw 38 q6 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼临丼") ∷
   rw 37 q4 ∷
   rw⁻ 38 q7 ∷
   rw 39 q6 ∷
   re 37 3 (ℓ "乄") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q4 ∷
   rw⁻ 39 q5 ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼临丼") ∷
   rw 39 q4 ∷
   rw⁻ 40 q7 ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "乄") ∷
   re 41 1 (ℓ "丼临丼") ∷
   rw 40 q4 ∷
   rw⁻ 41 q7 ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "乄") ∷
   rw 29 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 464 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = wE 1216 W
  q16 : Eqn
  q16 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X1]: 215 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒") (ℓ "丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 62 q9 ∷
   rw 61 q10 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q11 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q11 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q11 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q11 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q11 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q11 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q11 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q11 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q11 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q11 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q11 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q11 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q11 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q11 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q11 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q11 ∷
   rw 44 q12 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q11 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q11 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q11 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q11 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q11 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q11 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q11 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q11 ∷
   rw 35 q13 ∷
   rw 34 q13 ∷
   rw 33 q14 ∷
   rw 32 q13 ∷
   rw 31 q13 ∷
   rw 30 q13 ∷
   rw 29 q10 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q11 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q11 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q11 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q11 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q11 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q11 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q11 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q11 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q11 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q11 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q11 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q11 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q11 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q11 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q11 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q11 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q11 ∷
   rw 10 q12 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q11 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q11 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q13 ∷
   rw 0 q13 ∷
   rw 1 q15 ∷
   rw⁻ 0 q10 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 2 q13 ∷
   rw⁻ 3 q13 ∷
   rw⁻ 4 q14 ∷
   rw⁻ 5 q13 ∷
   rw⁻ 6 q13 ∷
   rw 9 q9 ∷
   re 7 3 (ℓ "乀") ∷
   rw 10 q9 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q9 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q9 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q9 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q9 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q9 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q9 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q16 ∷
   rw 18 q9 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q9 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q9 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q9 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q9 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q9 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q9 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q9 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q9 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "乑") ∷
   rw 32 q9 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q9 ∷
   re 31 3 (ℓ "中") ∷
   rw⁻ 32 q10 ∷
   rw⁻ 33 q13 ∷
   rw⁻ 34 q13 ∷
   rw⁻ 35 q14 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q14 ∷
   rw 41 q9 ∷
   re 39 3 (ℓ "乀") ∷
   rw 42 q9 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q16 ∷
   rw 44 q9 ∷
   re 42 3 (ℓ "乑") ∷
   rw 43 q16 ∷
   rw 46 q9 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q9 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q9 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q9 ∷
   re 47 3 (ℓ "乑") ∷
   rw 48 q16 ∷
   rw 51 q9 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q9 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q9 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q9 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q9 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q9 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q9 ∷
   re 55 3 (ℓ "乀") ∷
   rw 58 q9 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q9 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q9 ∷
   re 58 3 (ℓ "乑") ∷
   rw 61 q9 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q9 ∷
   re 60 3 (ℓ "乑") ∷
   rw 63 q9 ∷
   re 61 3 (ℓ "乑") ∷
   rw 62 q11 ∷ []) Eq.refl
