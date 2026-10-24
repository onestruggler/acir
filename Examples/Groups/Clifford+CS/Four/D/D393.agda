{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D393 (W : Ws) where

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
  q1 = wE 7 W
  q2 : Eqn
  q2 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 1117 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 142 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q17 : Eqn
  q17 = wE 846 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] part3: 147 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丠丠临丠临临丹乄且乄且丧丧丧並乇且丶丶丶丶丶丶丽丽丽乔丽丽並丹丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丠丠临丠临临丹乄且乄且丧丧丧並乇且丶丶丶丶丶丶丽丽丽乔丽丽並丹丧丧乄丧乄乄") (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 38 q1 ∷
   rw 37 q1 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   rw 34 q3 ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q5 ∷
   rw 35 q6 ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q5 ∷
   rw 36 q7 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q5 ∷
   rw 37 q6 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q5 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q7 ∷
   rw 39 q2 ∷
   rw 40 q7 ∷
   rw 41 q2 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q6 ∷
   rw 45 q7 ∷
   rw 46 q2 ∷
   rw 47 q6 ∷
   rw 48 q6 ∷
   rw 49 q6 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   rw 52 q6 ∷
   rw 53 q8 ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q9 ∷
   re 32 3 (ℓ "乀") ∷
   rw 32 q10 ∷
   rw⁻ 33 q11 ∷
   rw 34 q12 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q13 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q9 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q10 ∷
   rw⁻ 34 q11 ∷
   rw 35 q12 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q13 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q9 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q13 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q9 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q10 ∷
   rw⁻ 36 q14 ∷
   rw 37 q12 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q13 ∷
   re 34 5 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q9 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q13 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q9 ∷
   re 37 3 (ℓ "乀") ∷
   rw 37 q10 ∷
   rw⁻ 38 q11 ∷
   rw 39 q12 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q13 ∷
   re 36 5 (ℓ "中") ∷
   rw 37 q9 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q13 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q13 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q13 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q13 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q13 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q13 ∷
   rw 30 q15 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q15 ∷
   rw 26 q16 ∷
   rw 25 q16 ∷
   rw 26 q17 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q9 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q9 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q9 ∷
   re 30 3 (ℓ "中") ∷
   rw⁻ 31 q16 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 33 q15 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 35 q15 ∷
   rw⁻ 36 q15 ∷
   rw 37 q13 ∷ []) Eq.refl
