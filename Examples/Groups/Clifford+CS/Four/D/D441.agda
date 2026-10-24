{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D441 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 142 W
  q4 : Eqn
  q4 = wE 31 W
  q5 : Eqn
  q5 = wE 36 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 37 W
  q8 : Eqn
  q8 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q13 : Eqn
  q13 = wE 1180 W
  q14 : Eqn
  q14 = wE 800 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] part2: 257 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part2 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丧丧乄丧乄乄中中乏並丶乏乔丽丽並") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part2 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丧丧乄丧乄乄中中乏並丶乏乔丽丽並") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 57 q1 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 57 q2 ∷
   rw 58 q3 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "乑") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q2 ∷
   rw 59 q1 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q2 ∷
   rw 60 q1 ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q4 ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q5 ∷
   rw⁻ 48 q6 ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "丧") ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 48 q5 ∷
   rw⁻ 49 q6 ∷
   rw 50 q7 ∷
   re 48 3 (ℓ "丧") ∷
   re 50 1 (ℓ "丼临丼") ∷
   rw 49 q5 ∷
   rw⁻ 50 q8 ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "乄") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q5 ∷
   rw⁻ 51 q6 ∷
   rw 52 q7 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼临丼") ∷
   rw 51 q5 ∷
   rw⁻ 52 q8 ∷
   rw 53 q7 ∷
   re 51 3 (ℓ "乄") ∷
   re 53 1 (ℓ "丼临丼") ∷
   rw 52 q5 ∷
   rw⁻ 53 q8 ∷
   rw 54 q7 ∷
   re 52 3 (ℓ "乄") ∷
   rw 53 q9 ∷
   rw 52 q10 ∷
   rw 51 q10 ∷
   rw 50 q11 ∷
   rw 49 q10 ∷
   rw 48 q11 ∷
   rw 47 q11 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q11 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q2 ∷
   rw 46 q11 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q11 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q11 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q11 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q2 ∷
   rw 42 q11 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q2 ∷
   rw 41 q11 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q2 ∷
   rw 40 q11 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q2 ∷
   rw 39 q11 ∷
   rw⁻ 38 q2 ∷
   re 39 3 (ℓ "丽") ∷
   rw⁻ 37 q12 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q2 ∷
   rw 37 q10 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (ℓ "乔") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q2 ∷
   rw 36 q11 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q2 ∷
   rw 35 q11 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q2 ∷
   rw 34 q11 ∷
   rw⁻ 33 q2 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q2 ∷
   rw 33 q11 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q2 ∷
   rw 32 q11 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q2 ∷
   rw 31 q11 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q13 ∷
   rw 30 q1 ∷
   rw 31 q1 ∷
   rw 32 q3 ∷
   rw 33 q1 ∷
   rw 34 q3 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q2 ∷
   rw 37 q1 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q2 ∷
   rw 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q2 ∷
   rw 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q2 ∷
   rw 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q2 ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "乑") ∷
   rw 43 q12 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q2 ∷
   rw 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q2 ∷
   rw 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q2 ∷
   rw 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q2 ∷
   rw 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q4 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q5 ∷
   rw⁻ 30 q6 ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q5 ∷
   rw⁻ 31 q6 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼临丼") ∷
   rw 31 q5 ∷
   rw⁻ 32 q8 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "乄") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q5 ∷
   rw⁻ 33 q6 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "丧") ∷
   re 34 1 (ℓ "丼临丼") ∷
   rw 33 q5 ∷
   rw⁻ 34 q8 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "乄") ∷
   re 35 1 (ℓ "丼临丼") ∷
   rw 34 q5 ∷
   rw⁻ 35 q8 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "乄") ∷
   rw 23 q14 ∷ []) Eq.refl
