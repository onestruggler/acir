{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D445 (W : Ws) where

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
  q1 = wE 142 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 27 W
  q4 : Eqn
  q4 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 36 W
  q8 : Eqn
  q8 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q9 : Eqn
  q9 = wE 37 W
  q10 : Eqn
  q10 = wE 3 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = wE 800 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part3: 119 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part3 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀丠丠丠临丠丠丹中中乑中乏並乇乏乔丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶並丹丧丧丧乄丧丧") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part3 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀丠丠丠临丠丠丹中中乑中乏並乇乏乔丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶並丹丧丧丧乄丧丧") (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 35 q1 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q2 ∷
   rw 36 q1 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q3 ∷
   rw 37 q3 ∷
   rw 38 q3 ∷
   rw 39 q3 ∷
   rw 40 q3 ∷
   rw 41 q3 ∷
   rw 42 q1 ∷
   rw 43 q4 ∷
   rw 44 q3 ∷
   rw 45 q3 ∷
   rw 46 q3 ∷
   rw 47 q3 ∷
   rw 48 q3 ∷
   rw 49 q3 ∷
   rw 50 q3 ∷
   rw 51 q3 ∷
   rw 52 q3 ∷
   rw 53 q5 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q6 ∷
   re 30 3 (ℓ "乀") ∷
   rw 30 q7 ∷
   rw⁻ 31 q8 ∷
   rw 32 q9 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q10 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q6 ∷
   re 31 3 (ℓ "乀") ∷
   rw 31 q7 ∷
   rw⁻ 32 q8 ∷
   rw 33 q9 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 36 q10 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q6 ∷
   re 32 3 (ℓ "乀") ∷
   rw 32 q7 ∷
   rw⁻ 33 q11 ∷
   rw 34 q9 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q10 ∷
   re 31 5 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q6 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q7 ∷
   rw⁻ 34 q8 ∷
   rw 35 q9 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q10 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q6 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q7 ∷
   rw⁻ 35 q11 ∷
   rw 36 q9 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q10 ∷
   re 33 5 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q6 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q7 ∷
   rw⁻ 36 q11 ∷
   rw 37 q9 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q10 ∷
   re 34 5 (ℓ "乑") ∷
   rw 35 q6 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q10 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q10 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q10 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q10 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q10 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q10 ∷
   rw 28 q12 ∷
   rw 27 q12 ∷
   rw 26 q13 ∷
   rw 25 q12 ∷
   rw 24 q12 ∷
   rw 23 q12 ∷
   rw 24 q14 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "乑") ∷
   rw⁻ 29 q12 ∷
   rw⁻ 30 q12 ∷
   rw⁻ 31 q12 ∷
   rw⁻ 32 q13 ∷
   rw⁻ 33 q12 ∷
   rw⁻ 34 q12 ∷
   rw 35 q10 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1184 W
  q16 : Eqn
  q16 = wE 464 W
  q17 : Eqn
  q17 = wE 1185 W
  q18 : Eqn
  q18 = wE 1186 W

-- X^3: 173 steps
lem-Xᵖ3 : ⟪ (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") ⟫ʷ ≈ ⟪ (ℓ "丿丸") ⟫ʷ
lem-Xᵖ3 = derive (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") (ℓ "丿丸")
  (rw 32 q15 ∷
   rw 63 q15 ∷
   rw 94 q6 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q10 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q10 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 93 q10 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q10 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q10 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q10 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 89 q10 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q10 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q10 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q10 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q10 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q10 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q10 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q10 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q10 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q10 ∷
   rw 77 q16 ∷
   re 76 1 (ℓ "乏乄乏") ∷
   rw 78 q10 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q10 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q10 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q10 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q10 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q10 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q10 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 71 q10 ∷
   rw 68 q12 ∷
   rw 67 q12 ∷
   rw 66 q13 ∷
   rw 65 q12 ∷
   rw 64 q12 ∷
   rw 63 q12 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q10 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q10 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 62 q10 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q10 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q10 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q10 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q10 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q10 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q10 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q10 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q10 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q10 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q10 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q10 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q10 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q10 ∷
   rw 46 q16 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q10 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q10 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q10 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q10 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q10 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q10 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q10 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q10 ∷
   rw 37 q12 ∷
   rw 36 q12 ∷
   rw 35 q13 ∷
   rw 34 q12 ∷
   rw 33 q12 ∷
   rw 32 q12 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q10 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q10 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q10 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q10 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q10 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q10 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q10 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q10 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q10 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q10 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q10 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q10 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q10 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q10 ∷
   rw 15 q16 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q10 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q10 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q10 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q10 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q10 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q10 ∷
   rw 6 q12 ∷
   rw 5 q12 ∷
   rw 4 q13 ∷
   rw 3 q12 ∷
   rw 2 q12 ∷
   rw 1 q12 ∷
   rw 2 q17 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "丿") ∷
   rw 2 q10 ∷
   rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 75 W
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = wE 7 W
  q22 : Eqn
  q22 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q23 : Eqn
  q23 = wE 412 W
  q24 : Eqn
  q24 = wE 13 W
  q25 : Eqn
  q25 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q26 : Eqn
  q26 = wE 78 W
  q27 : Eqn
  q27 = wE 208 W
  q28 : Eqn
  q28 = wE 205 W
  q29 : Eqn
  q29 = wE 81 W

-- comm CCZ123 CS02: 21 steps
lem-comm-CCZ123-CS02 : ⟪ (ℓ "乜丧") ⟫ʷ ≈ ⟪ (ℓ "丧乜") ⟫ʷ
lem-comm-CCZ123-CS02 = derive (ℓ "乜丧") (ℓ "丧乜")
  (rw 0 q19 ∷
   rw 6 q20 ∷
   rw 5 q21 ∷
   rw⁻ 4 q22 ∷
   rw 5 q23 ∷
   rw 4 q3 ∷
   rw 5 q22 ∷
   rw 6 q5 ∷
   re 4 1 (ℓ "丼丠丼") ∷
   rw 3 q24 ∷
   rw⁻ 4 q25 ∷
   rw 5 q26 ∷
   re 3 3 (ℓ "丧") ∷
   rw 2 q27 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q24 ∷
   rw⁻ 2 q25 ∷
   rw 3 q26 ∷
   re 1 3 (ℓ "丧") ∷
   rw 0 q28 ∷
   rw 1 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 30 W
  q31 : Eqn
  q31 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q32 : Eqn
  q32 = wE 74 W
  q33 : Eqn
  q33 = wE 26 W
  q34 : Eqn
  q34 = wE 1187 W
  q35 : Eqn
  q35 = wE 24 W
  q36 : Eqn
  q36 = wE 25 W

-- pass [CCZ023] [CS02]: 51 steps
lem-pass-CCZ023-vs-CS02 : ⟪ (ℓ "乛丧") ⟫ʷ ≈ ⟪ (ℓ "丧乛") ⟫ʷ
lem-pass-CCZ023-vs-CS02 = derive (ℓ "乛丧") (ℓ "丧乛")
  (rw 2 q20 ∷
   rw 1 q21 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q22 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q30 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q2 ∷
   rw 5 q21 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   rw⁻ 2 q31 ∷
   rw 1 q32 ∷
   rw⁻ 0 q22 ∷
   rw 1 q33 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q34 ∷
   rw 0 q3 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q22 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q30 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q20 ∷
   rw 2 q22 ∷
   rw 3 q35 ∷
   rw 4 q31 ∷
   rw 5 q35 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q36 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q33 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 76 W
  q38 : Eqn
  q38 = wE 1188 W
  q39 : Eqn
  q39 = wE 29 W

-- pass [CCZ023] [CSd02]: 51 steps
lem-pass-CCZ023-vs-CSd02 : ⟪ (ℓ "乛丨") ⟫ʷ ≈ ⟪ (ℓ "丨乛") ⟫ʷ
lem-pass-CCZ023-vs-CSd02 = derive (ℓ "乛丨") (ℓ "丨乛")
  (rw 2 q20 ∷
   rw 1 q37 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q22 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q30 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q2 ∷
   rw 5 q21 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   rw⁻ 2 q31 ∷
   rw 1 q32 ∷
   rw⁻ 0 q22 ∷
   rw 1 q33 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q22 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q30 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q20 ∷
   rw 2 q22 ∷
   rw 3 q35 ∷
   rw 4 q31 ∷
   rw 5 q35 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q36 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q33 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q5 ∷ []) Eq.refl
