{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D137 (W : Ws) where

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
  q1 = wE 583 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 20 W
  q4 : Eqn
  q4 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q5 : Eqn
  q5 = wE 49 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q8 : Eqn
  q8 = wE 695 W
  q9 : Eqn
  q9 = wE 210 W
  q10 : Eqn
  q10 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = wE 607 W
  q12 : Eqn
  q12 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = wE 103 W
  q14 : Eqn
  q14 = wE 586 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [CS13]: 331 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS13 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丽") ⟫ʷ ≈ ⟪ (ℓ "丽丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS13 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丽") (ℓ "丽丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q3 ∷
   rw 29 q7 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "丽") ∷
   rw 28 q3 ∷
   rw 27 q7 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q3 ∷
   rw 26 q7 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q8 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q3 ∷
   rw 24 q7 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q3 ∷
   rw 23 q7 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q3 ∷
   rw 22 q7 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q3 ∷
   rw 21 q7 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q3 ∷
   rw 20 q7 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q3 ∷
   rw 19 q7 ∷
   rw 18 q5 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q6 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q9 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   re 15 3 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q3 ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q6 ∷
   re 16 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q6 ∷
   re 14 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q3 ∷
   rw 16 q7 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q3 ∷
   rw 15 q7 ∷
   rw 14 q5 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q2 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q3 ∷
   rw 14 q7 ∷
   rw 13 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q6 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   re 11 3 (ℓ "丽") ∷
   rw 10 q9 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q2 ∷
   re 10 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 8 q9 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q2 ∷
   re 8 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   re 9 5 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 6 q8 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q10 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q10 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q12 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q10 ∷
   rw 4 q6 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q12 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q12 ∷
   rw 2 q6 ∷
   rw 1 q14 ∷ []) Eq.refl
