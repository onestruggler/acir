{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD608 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D608 (W : Ws) (Sᴰ : SD608) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 : St 1309
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 = pickᴰ 0 Sᴰ
  lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1 : St 1310
  lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1 = pickᴰ 1 Sᴰ
  lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1 : St 1319
  lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1 = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = wE 1798 W
  q9 : Eqn
  q9 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = sE 1309 lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1
  q14 : Eqn
  q14 = sE 1319 lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1
  q15 : Eqn
  q15 = sE 1310 lem-pass-CSd01-CKd10-CS01-CS01-vs-X1-TOFF312-X1
  q16 : Eqn
  q16 = wE 1799 W
  q17 : Eqn
  q17 = wE 175 W

-- pass [X0 X3 CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30 X0 X3] [X1 TOFF312 X1]: 376 steps
lem-pass-X0-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X3-vs-X1-TOFF312-X1 : ⟪ (ℓ "丌丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丞丒乨丒") ⟫ʷ ≈ ⟪ (ℓ "丒乨丒丌丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丞") ⟫ʷ
lem-pass-X0-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X3-vs-X1-TOFF312-X1 = derive (ℓ "丌丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丞丒乨丒") (ℓ "丒乨丒丌丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丞")
  (rw 33 q1 ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q4 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q4 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q4 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q4 ∷
   rw 12 q5 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q4 ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q4 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 10 q4 ∷
   rw 7 q6 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q7 ∷
   rw 1 q2 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw⁻ 0 q6 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 2 q7 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 10 q6 ∷
   rw⁻ 11 q11 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q6 ∷
   rw⁻ 16 q11 ∷
   rw⁻ 17 q7 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乀") ∷
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
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q12 ∷
   rw 43 q12 ∷
   rw 44 q12 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乑") ∷
   rw 46 q12 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   rw 58 q12 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乑") ∷
   rw 60 q12 ∷
   rw 61 q12 ∷
   rw 62 q12 ∷
   rw 63 q12 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乑") ∷
   rw 65 q12 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乀") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q12 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q12 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "乑") ∷
   rw 75 q12 ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw⁻ 82 q6 ∷
   rw⁻ 83 q7 ∷
   rw⁻ 84 q7 ∷
   rw⁻ 85 q9 ∷
   rw 86 q4 ∷
   rw 82 q13 ∷
   rw 8 q14 ∷
   rw 4 q15 ∷
   rw 0 q13 ∷
   rw 89 q1 ∷
   rw 88 q9 ∷
   rw 87 q7 ∷
   rw 86 q7 ∷
   rw 85 q6 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q4 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q4 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q4 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q4 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q4 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q4 ∷
   rw 78 q5 ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw 79 q4 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q4 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q4 ∷
   rw 73 q5 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 74 q4 ∷
   rw 71 q5 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q4 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 71 q4 ∷
   rw 68 q5 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw 69 q4 ∷
   rw 66 q5 ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   re 62 1 (ℓ "乏乄乏") ∷
   rw 64 q4 ∷
   rw 61 q5 ∷
   rw 60 q5 ∷
   rw 59 q5 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q4 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q4 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q4 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q4 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q4 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q4 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q4 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q4 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q4 ∷
   rw 49 q5 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q4 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q4 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q4 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q4 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q4 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q4 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q4 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q4 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q4 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q4 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q4 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q4 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q4 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q4 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q4 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q4 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q4 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 28 q4 ∷
   rw 25 q7 ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q11 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q11 ∷
   rw 13 q6 ∷
   rw 12 q11 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw 6 q9 ∷
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 3 q6 ∷
   rw 4 q16 ∷
   rw⁻ 3 q3 ∷
   rw 4 q17 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q6 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乀") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q12 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q12 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q12 ∷
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
   re 27 3 (ℓ "乀") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乑") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乑") ∷
   rw⁻ 34 q3 ∷
   rw 35 q17 ∷
   rw 36 q4 ∷ []) Eq.refl
