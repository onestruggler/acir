{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D438 (W : Ws) where

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
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 1178 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 142 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 36 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q11 : Eqn
  q11 = wE 37 W
  q12 : Eqn
  q12 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q13 : Eqn
  q13 = wE 1132 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] part2: 185 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part2 : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中並乏丶乏丶丶乇丶並乀中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part2 = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中並乏丶乏丶丶乇丶並乀中中中乑中中") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q1 ∷
   rw 35 q2 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q1 ∷
   rw 34 q2 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q1 ∷
   rw 33 q2 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q1 ∷
   rw 31 q4 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (ℓ "乔") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q1 ∷
   rw 30 q2 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q1 ∷
   rw 29 q2 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q1 ∷
   rw 28 q2 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q1 ∷
   rw 27 q2 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q1 ∷
   rw 26 q2 ∷
   rw⁻ 25 q1 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q1 ∷
   rw 25 q2 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q7 ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   rw 29 q6 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   rw 30 q6 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q1 ∷
   rw 31 q6 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q1 ∷
   rw 32 q6 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q1 ∷
   rw 33 q6 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q1 ∷
   rw 34 q6 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q1 ∷
   rw 35 q7 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q1 ∷
   rw 37 q6 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q1 ∷
   rw 38 q6 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q1 ∷
   rw 39 q6 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q1 ∷
   rw 40 q6 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q1 ∷
   rw 41 q6 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q1 ∷
   rw 42 q6 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q1 ∷
   rw 43 q6 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q1 ∷
   rw 44 q6 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q1 ∷
   rw 45 q6 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q8 ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q9 ∷
   rw⁻ 24 q10 ∷
   rw 25 q11 ∷
   re 23 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q9 ∷
   rw⁻ 25 q10 ∷
   rw 26 q11 ∷
   re 24 3 (ℓ "丧") ∷
   re 26 1 (ℓ "丼临丼") ∷
   rw 25 q9 ∷
   rw⁻ 26 q12 ∷
   rw 27 q11 ∷
   re 25 3 (ℓ "乄") ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q9 ∷
   rw⁻ 27 q10 ∷
   rw 28 q11 ∷
   re 26 3 (ℓ "丧") ∷
   rw 17 q13 ∷ []) Eq.refl
