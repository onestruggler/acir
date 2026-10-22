{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD607 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D607 (W : Ws) (Sᴰ : SD607) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 : St 1309
  lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1 = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-vs-X1-TOFF312-X1 : St 1317
  lem-pass-CS01-CS01-CK10-CS01-vs-X1-TOFF312-X1 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1 : St 1318
  lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1 = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = wE 1804 W
  q9 : Eqn
  q9 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = wE 151 W
  q12 : Eqn
  q12 = sE 1309 lem-pass-CK10-CS01-CS01-CKd10-vs-X1-TOFF312-X1
  q13 : Eqn
  q13 = sE 1318 lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-TOFF312-X1
  q14 : Eqn
  q14 = sE 1317 lem-pass-CS01-CS01-CK10-CS01-vs-X1-TOFF312-X1
  q15 : Eqn
  q15 = wE 1805 W
  q16 : Eqn
  q16 = wE 175 W

-- pass [X0 X3 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X0 X3] [X1 TOFF312 X1]: 452 steps
lem-pass-X0-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X3-vs-X1-TOFF312-X1 : ⟪ (X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X3 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff312 ∷ X1 ∷ X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X3-vs-X1-TOFF312-X1 = derive (X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X3 ∷ X1 ∷ Toff312 ∷ X1 ∷ []) (X1 ∷ Toff312 ∷ X1 ∷ X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X3 ∷ [])
  (rw 35 q1 ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q5 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q6 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q6 ∷
   rw 2 q6 ∷
   rw 1 q2 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw⁻ 0 q7 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 21 q6 ∷
   rw⁻ 22 q6 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q6 ∷
   rw 27 q1 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 58 q1 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q11 ∷
   rw 60 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CX13 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q1 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw 82 q1 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 83 q1 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 84 q1 ∷
   re 82 3 (CS03 ∷ []) ∷
   rw 85 q1 ∷
   re 83 3 (CK30 ∷ []) ∷
   rw 84 q11 ∷
   rw 87 q1 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q1 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 89 q1 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 90 q1 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 91 q1 ∷
   re 89 3 (CS03 ∷ []) ∷
   rw 92 q1 ∷
   re 90 3 (CS03 ∷ []) ∷
   rw 93 q1 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 94 q1 ∷
   re 92 3 (CS03 ∷ []) ∷
   rw 95 q1 ∷
   re 93 3 (CS03 ∷ []) ∷
   rw⁻ 94 q7 ∷
   rw⁻ 95 q6 ∷
   rw⁻ 96 q6 ∷
   rw⁻ 97 q9 ∷
   rw 98 q4 ∷
   rw 94 q12 ∷
   rw 8 q13 ∷
   rw 4 q14 ∷
   rw 0 q12 ∷
   rw 101 q1 ∷
   rw 100 q9 ∷
   rw 99 q6 ∷
   rw 98 q6 ∷
   rw 97 q7 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q4 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q4 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q4 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q4 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q4 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q4 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q4 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q4 ∷
   rw 87 q5 ∷
   re 86 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 88 q4 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q4 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q4 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q4 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q4 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q4 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   re 79 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 81 q4 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q4 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   rw 60 q5 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw 56 q5 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q4 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q4 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q4 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q4 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   rw 27 q6 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q10 ∷
   rw 17 q7 ∷
   rw 16 q6 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q6 ∷
   rw 6 q9 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 4 q15 ∷
   rw⁻ 3 q3 ∷
   rw 4 q16 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q6 ∷
   rw 13 q1 ∷
   re 11 3 (CX13 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CK30 ∷ []) ∷
   rw 19 q11 ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 37 q16 ∷
   rw 38 q4 ∷ []) Eq.refl
