{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D312 (W : Ws) where

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
  q2 = wE 21 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 51 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q7 : Eqn
  q7 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 608 W
  q9 : Eqn
  q9 = wE 200 W
  q10 : Eqn
  q10 = wE 935 W
  q11 : Eqn
  q11 = wE 609 W

-- pass [CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03] [CSd12]: 582 steps
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-CSd12 : ⟪ (ℓ "丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丷") ⟫ʷ ≈ ⟪ (ℓ "丷丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-CSd12 = derive (ℓ "丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丷") (ℓ "丷丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中")
  (re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "举") ∷
   rw 88 q2 ∷
   rw 87 q3 ∷
   rw 86 q4 ∷
   re 86 1 (ℓ "乏丷乏") ∷
   rw 85 q5 ∷
   re 86 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "举") ∷
   rw 87 q2 ∷
   rw 86 q3 ∷
   rw 85 q4 ∷
   re 85 1 (ℓ "乏丷乏") ∷
   rw 84 q5 ∷
   re 85 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "举") ∷
   rw 86 q2 ∷
   rw 85 q3 ∷
   rw 84 q4 ∷
   re 84 1 (ℓ "乏丷乏") ∷
   rw 83 q5 ∷
   re 84 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "举") ∷
   rw 85 q2 ∷
   rw 84 q3 ∷
   rw 83 q4 ∷
   re 83 1 (ℓ "乏丷乏") ∷
   rw 82 q5 ∷
   re 83 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "举") ∷
   rw 84 q2 ∷
   rw 83 q3 ∷
   rw 82 q4 ∷
   re 82 1 (ℓ "乏丷乏") ∷
   rw 81 q5 ∷
   re 82 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "举") ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw 81 q4 ∷
   re 81 1 (ℓ "乏丷乏") ∷
   rw 80 q5 ∷
   re 81 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "举") ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   re 80 1 (ℓ "乏丷乏") ∷
   rw 79 q5 ∷
   re 80 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "举") ∷
   rw 81 q2 ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 78 q5 ∷
   re 79 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "举") ∷
   rw 80 q2 ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 77 q5 ∷
   re 78 5 (ℓ "中") ∷
   rw⁻ 76 q6 ∷
   re 75 1 (ℓ "乏丼临丼乏") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "举") ∷
   rw 78 q2 ∷
   rw 77 q7 ∷
   rw 76 q4 ∷
   re 76 1 (ℓ "乏丷乏") ∷
   rw 75 q5 ∷
   re 76 5 (ℓ "乑") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "举") ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q5 ∷
   re 75 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "举") ∷
   rw 76 q2 ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q5 ∷
   re 74 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "举") ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q5 ∷
   re 73 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "举") ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 71 q5 ∷
   re 72 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "举") ∷
   rw 73 q2 ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 70 q5 ∷
   re 71 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "举") ∷
   rw 72 q2 ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q5 ∷
   re 70 5 (ℓ "中") ∷
   rw 68 q8 ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "举") ∷
   rw 70 q2 ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "举") ∷
   rw 69 q2 ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q5 ∷
   re 67 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "举") ∷
   rw 68 q2 ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q5 ∷
   re 66 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "举") ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q5 ∷
   re 65 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "举") ∷
   rw 66 q2 ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q5 ∷
   re 64 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "举") ∷
   rw 65 q2 ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 62 q5 ∷
   re 63 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "举") ∷
   rw 64 q2 ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q5 ∷
   re 62 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "举") ∷
   rw 63 q2 ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 62 q2 ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "举") ∷
   rw 60 q2 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "举") ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q4 ∷
   re 57 1 (ℓ "乏丷乏") ∷
   rw 56 q5 ∷
   re 57 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "举") ∷
   rw 58 q2 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   re 56 1 (ℓ "乏丷乏") ∷
   rw 55 q5 ∷
   re 56 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "举") ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   re 55 1 (ℓ "乏丷乏") ∷
   rw 54 q5 ∷
   re 55 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "举") ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q5 ∷
   re 54 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "举") ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q5 ∷
   re 53 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "举") ∷
   rw 54 q2 ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q5 ∷
   re 52 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "举") ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q5 ∷
   re 51 5 (ℓ "中") ∷
   rw⁻ 49 q6 ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "举") ∷
   rw 51 q2 ∷
   rw 50 q7 ∷
   rw 49 q4 ∷
   re 49 1 (ℓ "乏丷乏") ∷
   rw 48 q5 ∷
   re 49 5 (ℓ "乑") ∷
   rw⁻ 47 q6 ∷
   rw⁻ 46 q6 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "举") ∷
   rw 47 q2 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q5 ∷
   re 45 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "举") ∷
   rw 46 q2 ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q5 ∷
   re 44 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "举") ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q5 ∷
   re 43 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "举") ∷
   rw 44 q2 ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 41 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "举") ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 40 q5 ∷
   re 41 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "举") ∷
   rw 42 q2 ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   re 40 1 (ℓ "乏丷乏") ∷
   rw 39 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "举") ∷
   rw 41 q2 ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   re 39 1 (ℓ "乏丷乏") ∷
   rw 38 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "举") ∷
   rw 40 q2 ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q5 ∷
   re 38 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "举") ∷
   rw 39 q2 ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 36 q5 ∷
   re 37 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "举") ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q5 ∷
   re 36 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "举") ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q5 ∷
   re 35 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "举") ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q5 ∷
   re 34 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "举") ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q5 ∷
   re 33 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q5 ∷
   re 32 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q5 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q5 ∷
   re 30 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q5 ∷
   re 26 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q5 ∷
   re 23 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q5 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q5 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q5 ∷
   re 19 5 (ℓ "中") ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q9 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q9 ∷
   rw 9 q9 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw 6 q11 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q9 ∷
   rw 2 q9 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷ []) Eq.refl
