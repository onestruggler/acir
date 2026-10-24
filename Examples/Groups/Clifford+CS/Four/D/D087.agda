{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D087 (W : Ws) where

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
  q1 = wE 620 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CX21 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CX21-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乆丘") ⟫ʷ ≈ ⟪ (ℓ "丘乆丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CX21-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乆丘") (ℓ "丘乆丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = wE 582 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CK21 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乇丘") (ℓ "丘乇丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = wE 583 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 107 W
  q6 : Eqn
  q6 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q7 : Eqn
  q7 = wE 108 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q10 : Eqn
  q10 = wE 621 W
  q11 : Eqn
  q11 = wE 622 W
  q12 : Eqn
  q12 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = wE 585 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 110 W
  q16 : Eqn
  q16 = wE 586 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [CZ13]: 331 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CZ13 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丿") ⟫ʷ ≈ ⟪ (ℓ "丿丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CZ13 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丿") (ℓ "丿丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q3 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q4 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "丿") ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q7 ∷
   re 30 1 (ℓ "乏丸乏") ∷
   rw 29 q8 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q8 ∷
   re 28 3 (ℓ "丿") ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q4 ∷
   re 28 3 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q4 ∷
   re 32 3 (ℓ "丿") ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   rw 29 q7 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q8 ∷
   re 29 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q8 ∷
   re 27 3 (ℓ "丿") ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q4 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "丿") ∷
   rw 30 q5 ∷
   rw 29 q9 ∷
   rw 28 q7 ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q8 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q8 ∷
   re 26 3 (ℓ "丿") ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q4 ∷
   re 26 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "丿") ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q8 ∷
   re 27 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q8 ∷
   re 25 3 (ℓ "丿") ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q4 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "丿") ∷
   rw 28 q5 ∷
   rw 27 q9 ∷
   rw 26 q7 ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q8 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q8 ∷
   re 24 3 (ℓ "丿") ∷
   re 24 1 (ℓ "乏丸乏") ∷
   rw 23 q4 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "丿") ∷
   rw 27 q5 ∷
   rw 26 q9 ∷
   rw 25 q7 ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q8 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q8 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q10 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q4 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "丿") ∷
   rw 25 q5 ∷
   rw 24 q9 ∷
   rw 23 q7 ∷
   re 23 1 (ℓ "乏丸乏") ∷
   rw 22 q8 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q8 ∷
   re 21 3 (ℓ "丿") ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q4 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "丿") ∷
   rw 24 q5 ∷
   rw 23 q9 ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q8 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q8 ∷
   re 20 3 (ℓ "丿") ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q4 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "丿") ∷
   rw 23 q5 ∷
   rw 22 q9 ∷
   rw 21 q7 ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q8 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q8 ∷
   re 19 3 (ℓ "丿") ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q4 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q5 ∷
   rw 21 q9 ∷
   rw 20 q7 ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q8 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q8 ∷
   re 18 3 (ℓ "丿") ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q4 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "丿") ∷
   rw 21 q5 ∷
   rw 20 q9 ∷
   rw 19 q7 ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q8 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q8 ∷
   re 17 3 (ℓ "丿") ∷
   re 17 1 (ℓ "乏丸乏") ∷
   rw 16 q4 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "丿") ∷
   rw 20 q5 ∷
   rw 19 q9 ∷
   rw 18 q7 ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q8 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q8 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q11 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q4 ∷
   re 15 3 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "丿") ∷
   rw 18 q5 ∷
   rw 17 q6 ∷
   rw 16 q7 ∷
   re 16 1 (ℓ "乏丸乏") ∷
   rw 15 q8 ∷
   re 16 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q8 ∷
   re 14 3 (ℓ "丿") ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q4 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "丿") ∷
   rw 17 q5 ∷
   rw 16 q9 ∷
   rw 15 q7 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q8 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q8 ∷
   re 13 3 (ℓ "丿") ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q4 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "丿") ∷
   rw 16 q5 ∷
   rw 15 q9 ∷
   rw 14 q7 ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q8 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q8 ∷
   re 12 3 (ℓ "丿") ∷
   re 12 1 (ℓ "乏丸乏") ∷
   rw 11 q4 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q5 ∷
   rw 14 q9 ∷
   rw 13 q7 ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q8 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q8 ∷
   re 11 3 (ℓ "丿") ∷
   rw 10 q11 ∷
   re 10 1 (ℓ "乏丸乏") ∷
   rw 9 q4 ∷
   re 10 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q4 ∷
   re 14 3 (ℓ "丿") ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   re 11 1 (ℓ "乏丸乏") ∷
   rw 10 q8 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q8 ∷
   re 9 3 (ℓ "丿") ∷
   rw 8 q11 ∷
   re 8 1 (ℓ "乏丸乏") ∷
   rw 7 q4 ∷
   re 8 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q4 ∷
   re 12 3 (ℓ "丿") ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   re 9 1 (ℓ "乏丸乏") ∷
   rw 8 q8 ∷
   re 9 5 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q8 ∷
   re 7 3 (ℓ "丿") ∷
   rw 6 q10 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丸乏") ∷
   rw 8 q8 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "丿") ∷
   rw⁻ 6 q12 ∷
   rw 7 q8 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丸乏") ∷
   rw 7 q8 ∷
   rw 4 q12 ∷
   rw 5 q13 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丿") ∷
   rw⁻ 5 q12 ∷
   rw 6 q8 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 6 q8 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "丿") ∷
   rw⁻ 4 q14 ∷
   rw 5 q8 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丸乏") ∷
   rw 5 q8 ∷
   rw 2 q12 ∷
   rw 3 q13 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "丿") ∷
   rw⁻ 3 q12 ∷
   rw 4 q8 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丸乏") ∷
   rw 4 q8 ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丿") ∷
   rw⁻ 2 q14 ∷
   rw 3 q8 ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw 3 q8 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丿") ∷
   rw⁻ 1 q14 ∷
   rw 2 q8 ∷
   rw 1 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 587 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [CS12]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丶") ⟫ʷ ≈ ⟪ (ℓ "丶丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丶") (ℓ "丶丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q19 : Eqn
  q19 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q20 : Eqn
  q20 = wE 407 W
  q21 : Eqn
  q21 = eqn (ℓ "与义") (ℓ "义与") (low-comm ((S ↑)) (CS))
  q22 : Eqn
  q22 = wE 5 W
  q23 : Eqn
  q23 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q24 : Eqn
  q24 = wE 140 W
  q25 : Eqn
  q25 = wE 623 W
  q26 : Eqn
  q26 = wE 142 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 7 W
  q29 : Eqn
  q29 = wE 406 W
  q30 : Eqn
  q30 = wE 27 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [CS23]: 65 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS23 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临义") ⟫ʷ ≈ ⟪ (ℓ "义丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS23 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临义") (ℓ "义丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   rw 22 q20 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q21 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q21 ∷
   rw 9 q18 ∷
   rw 8 q21 ∷
   rw 7 q18 ∷
   rw 6 q20 ∷
   rw 7 q22 ∷
   rw⁻ 6 q23 ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 5 q23 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 6 q22 ∷
   rw⁻ 5 q23 ∷
   rw 4 q24 ∷
   rw 5 q25 ∷
   rw 4 q23 ∷
   rw 5 q26 ∷
   rw 6 q27 ∷
   rw 5 q22 ∷
   rw⁻ 4 q23 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 3 q23 ∷
   rw 4 q30 ∷
   rw 5 q27 ∷
   rw 4 q22 ∷
   rw⁻ 3 q23 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   rw 2 q23 ∷
   rw 3 q26 ∷
   rw 4 q27 ∷
   rw 3 q22 ∷
   rw⁻ 2 q23 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 1 q23 ∷
   rw 2 q30 ∷
   rw 3 q27 ∷
   rw 2 q22 ∷
   rw⁻ 1 q23 ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 0 q23 ∷
   rw 1 q30 ∷
   rw 2 q27 ∷ []) Eq.refl
