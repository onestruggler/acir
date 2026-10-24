{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D385 (W : Ws) where

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
  q1 = wE 1089 W
  q2 : Eqn
  q2 = wE 1090 W
  q3 : Eqn
  q3 = wE 13 W
  q4 : Eqn
  q4 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q5 : Eqn
  q5 = wE 78 W
  q6 : Eqn
  q6 = wE 1097 W
  q7 : Eqn
  q7 = wE 1000 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = wE 710 W
  q13 : Eqn
  q13 = wE 142 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 1093 W

-- pass [CCZ123] [X2 CK20 X2]: 29 steps
lem-pass-CCZ123-vs-X2-CK20-X2 : ⟪ (ℓ "乜丘乄丘") ⟫ʷ ≈ ⟪ (ℓ "丘乄丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-CK20-X2 = derive (ℓ "乜丘乄丘") (ℓ "丘乄丘乜")
  (rw 0 q1 ∷
   rw 4 q2 ∷
   re 6 1 (ℓ "丼临丼") ∷
   rw 5 q3 ∷
   rw⁻ 6 q4 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乄") ∷
   rw 6 q2 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "丼临丼") ∷
   rw 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "乄") ∷
   rw 4 q2 ∷
   rw 1 q7 ∷
   rw 4 q8 ∷
   rw⁻ 3 q9 ∷
   rw 2 q10 ∷
   rw⁻ 1 q9 ∷
   rw⁻ 0 q11 ∷
   rw 1 q12 ∷
   rw 0 q9 ∷
   rw 1 q13 ∷
   rw 2 q9 ∷
   rw 3 q11 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1098 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CSd02 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丨丘") (ℓ "丘丨丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1099 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS02 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丘") (ℓ "丘丧丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 76 W
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q22 : Eqn
  q22 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q23 : Eqn
  q23 = wE 1100 W
  q24 : Eqn
  q24 = wE 29 W
  q25 : Eqn
  q25 = wE 27 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd02 X2]: 211 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨丘") (ℓ "丘丨丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   rw 30 q18 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q19 ∷
   rw 29 q10 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q19 ∷
   rw 28 q10 ∷
   rw⁻ 27 q19 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q19 ∷
   rw 27 q20 ∷
   rw⁻ 26 q19 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q19 ∷
   rw 26 q10 ∷
   rw⁻ 25 q19 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q19 ∷
   rw 25 q20 ∷
   rw⁻ 24 q19 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q19 ∷
   rw 24 q20 ∷
   rw⁻ 23 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q21 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q19 ∷
   rw 22 q20 ∷
   rw⁻ 21 q19 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q19 ∷
   rw 21 q20 ∷
   rw⁻ 20 q19 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q19 ∷
   rw 20 q20 ∷
   rw⁻ 19 q19 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q19 ∷
   rw 19 q20 ∷
   rw⁻ 18 q19 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q19 ∷
   rw 18 q20 ∷
   rw⁻ 17 q19 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q19 ∷
   rw 17 q20 ∷
   rw⁻ 16 q19 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q22 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q19 ∷
   rw 15 q10 ∷
   rw⁻ 14 q19 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q19 ∷
   rw 13 q20 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q19 ∷
   rw 12 q20 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q22 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q19 ∷
   rw 10 q10 ∷
   rw⁻ 9 q19 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q22 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q19 ∷
   rw 8 q10 ∷
   rw⁻ 7 q19 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q21 ∷
   rw 5 q10 ∷
   rw 4 q10 ∷
   rw 3 q20 ∷
   rw 2 q10 ∷
   rw 1 q20 ∷
   rw 0 q20 ∷
   rw 1 q23 ∷
   rw 0 q9 ∷
   rw 1 q24 ∷
   rw 2 q9 ∷
   rw 3 q25 ∷
   rw 4 q25 ∷
   rw 5 q13 ∷
   rw 6 q25 ∷
   rw 7 q13 ∷
   rw 8 q13 ∷
   rw 9 q21 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q19 ∷
   rw 11 q13 ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q22 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q19 ∷
   rw 13 q13 ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q22 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   rw 15 q25 ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q19 ∷
   rw 16 q25 ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q19 ∷
   rw 17 q25 ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q19 ∷
   rw 18 q13 ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q22 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q19 ∷
   rw 20 q25 ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q19 ∷
   rw 21 q25 ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q19 ∷
   rw 22 q25 ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q19 ∷
   rw 23 q25 ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q19 ∷
   rw 24 q25 ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q19 ∷
   rw 25 q25 ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q21 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q19 ∷
   rw 27 q25 ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q19 ∷
   rw 28 q25 ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q19 ∷
   rw 29 q13 ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   rw 30 q25 ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q19 ∷
   rw 31 q13 ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q19 ∷
   rw 32 q13 ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q14 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1101 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CS02 X2]: 211 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS02-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丧丘") (ℓ "丘丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   rw 30 q20 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q19 ∷
   rw 29 q10 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q19 ∷
   rw 28 q10 ∷
   rw⁻ 27 q19 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q19 ∷
   rw 27 q20 ∷
   rw⁻ 26 q19 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q19 ∷
   rw 26 q10 ∷
   rw⁻ 25 q19 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q19 ∷
   rw 25 q20 ∷
   rw⁻ 24 q19 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q19 ∷
   rw 24 q20 ∷
   rw⁻ 23 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q21 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q19 ∷
   rw 22 q20 ∷
   rw⁻ 21 q19 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q19 ∷
   rw 21 q20 ∷
   rw⁻ 20 q19 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q19 ∷
   rw 20 q20 ∷
   rw⁻ 19 q19 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q19 ∷
   rw 19 q20 ∷
   rw⁻ 18 q19 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q19 ∷
   rw 18 q20 ∷
   rw⁻ 17 q19 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q19 ∷
   rw 17 q20 ∷
   rw⁻ 16 q19 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q22 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q19 ∷
   rw 15 q10 ∷
   rw⁻ 14 q19 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q19 ∷
   rw 13 q20 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q19 ∷
   rw 12 q20 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q22 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q19 ∷
   rw 10 q10 ∷
   rw⁻ 9 q19 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q22 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q19 ∷
   rw 8 q10 ∷
   rw⁻ 7 q19 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q21 ∷
   rw 5 q10 ∷
   rw 4 q10 ∷
   rw 3 q20 ∷
   rw 2 q10 ∷
   rw 1 q20 ∷
   rw 0 q20 ∷
   rw 1 q26 ∷
   rw 0 q9 ∷
   rw 1 q25 ∷
   rw 2 q9 ∷
   rw 3 q25 ∷
   rw 4 q25 ∷
   rw 5 q13 ∷
   rw 6 q25 ∷
   rw 7 q13 ∷
   rw 8 q13 ∷
   rw 9 q21 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q19 ∷
   rw 11 q13 ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q22 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q19 ∷
   rw 13 q13 ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q22 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   rw 15 q25 ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q19 ∷
   rw 16 q25 ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q19 ∷
   rw 17 q25 ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q19 ∷
   rw 18 q13 ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q22 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q19 ∷
   rw 20 q25 ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q19 ∷
   rw 21 q25 ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q19 ∷
   rw 22 q25 ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q19 ∷
   rw 23 q25 ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q19 ∷
   rw 24 q25 ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q19 ∷
   rw 25 q25 ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q21 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q19 ∷
   rw 27 q25 ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q19 ∷
   rw 28 q25 ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q19 ∷
   rw 29 q13 ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   rw 30 q25 ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q19 ∷
   rw 31 q13 ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q19 ∷
   rw 32 q13 ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q14 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1102 W
  q28 : Eqn
  q28 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q30 : Eqn
  q30 = eqn (ℓ "丌丽") (ℓ "丽丌") (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q31 : Eqn
  q31 = wE 387 W
  q32 : Eqn
  q32 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q33 : Eqn
  q33 = wE 257 W
  q34 : Eqn
  q34 = wE 389 W
  q35 : Eqn
  q35 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q36 : Eqn
  q36 = wE 390 W
  q37 : Eqn
  q37 = eqn (ℓ "丌举") (ℓ "举丌") (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q38 : Eqn
  q38 = wE 258 W

-- distribute Gad(t=1, W=(0, 2, 3), d=1, e=-1) CS13 TOFF102 CSd13 TOFF102: 25 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丌丘习丌丘丞举丞丌丘习丌丘") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丌丘丞丽习举习丌丘丞") (ℓ "丞丽丞丌丘习丌丘丞举丞丌丘习丌丘")
  (rw 4 q27 ∷
   rw 11 q27 ∷
   rw 18 q27 ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw⁻ 5 q35 ∷
   rw⁻ 6 q29 ∷
   rw⁻ 7 q32 ∷
   rw 8 q36 ∷
   rw 8 q28 ∷
   rw 9 q29 ∷
   rw 10 q37 ∷
   rw 11 q31 ∷
   rw 8 q32 ∷
   rw 9 q38 ∷
   rw 10 q34 ∷
   rw⁻ 13 q35 ∷
   rw⁻ 14 q29 ∷
   rw⁻ 15 q32 ∷
   rw 16 q36 ∷ []) Eq.refl
