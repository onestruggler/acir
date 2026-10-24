{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD647 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D647 (W : Ws) (Sᴰ : SD647) where

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
  lem-pass-TOFF312-vs-X1-TOFF312-X1 : St 1013
  lem-pass-TOFF312-vs-X1-TOFF312-X1 = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 : St 729
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1 : St 1314
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1 = pickᴰ 2 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1 : St 1328
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 : St 1398
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 : St 1399
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 = pickᴰ 5 Sᴰ
  lem-pass-TOFF312-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 : St 1594
  lem-pass-TOFF312-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 = pickᴰ 6 Sᴰ
  lem-pass-TOFF312-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 : St 1595
  lem-pass-TOFF312-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = wE 872 W
  q3 : Eqn
  q3 = sE 1398 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1
  q4 : Eqn
  q4 = sE 1594 lem-pass-TOFF312-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1
  q5 : Eqn
  q5 = sE 1399 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1
  q6 : Eqn
  q6 = sE 1314 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF312-X1
  q7 : Eqn
  q7 = sE 1013 lem-pass-TOFF312-vs-X1-TOFF312-X1
  q8 : Eqn
  q8 = sE 1328 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1
  q9 : Eqn
  q9 = sE 729 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1
  q10 : Eqn
  q10 = sE 1595 lem-pass-TOFF312-vs-X1-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X1
  q11 : Eqn
  q11 = wE 1946 W
  q12 : Eqn
  q12 = wE 1947 W
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = wE 464 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q19 : Eqn
  q19 = wE 1948 W

-- L87 merge-k CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02  1: 285 steps
lem-L87-merge-k-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02--1 : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒") ⟫ʷ ≈ ⟪ (ℓ "丧丧乄丧乄乄丧丧乄丧乄乄乌中中中乑中中中中中乑中中乌中中乑中乑乑中中乑中乑乑") ⟫ʷ
lem-L87-merge-k-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02--1 = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒") (ℓ "丧丧乄丧乄乄丧丧乄丧乄乄乌中中中乑中中中中中乑中中乌中中乑中乑乑中中乑中乑乑")
  (rw 0 q1 ∷
   rw 92 q1 ∷
   rw 121 q2 ∷
   rw 124 q2 ∷
   rw 157 q2 ∷
   rw 160 q2 ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   rw 30 q5 ∷
   rw 29 q4 ∷
   rw 93 q6 ∷
   rw 92 q7 ∷
   rw 61 q8 ∷
   rw 96 q9 ∷
   rw 95 q10 ∷
   rw 129 q6 ∷
   rw 0 q11 ∷
   rw 12 q12 ∷
   rw 77 q13 ∷
   rw 76 q14 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q15 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q15 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw 75 q15 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q15 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q15 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q15 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 71 q15 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q15 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q15 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q15 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q15 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q15 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q15 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q15 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q15 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q15 ∷
   rw 59 q16 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q15 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q15 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q15 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q15 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q15 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q15 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q15 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q15 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q18 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw 45 q17 ∷
   rw 44 q14 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q15 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q15 ∷
   re 41 1 (ℓ "乏乄乏") ∷
   rw 43 q15 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q15 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q15 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q15 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q15 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q15 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q15 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q15 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q15 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q15 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q15 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q15 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q15 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q15 ∷
   rw 27 q16 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q15 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q15 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q15 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q15 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q15 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q15 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q15 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 21 q15 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q18 ∷
   rw 15 q17 ∷
   rw 14 q17 ∷
   rw 13 q17 ∷
   rw 14 q19 ∷
   rw 15 q13 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q13 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q13 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q13 ∷
   re 16 3 (ℓ "乑") ∷
   rw 19 q13 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q13 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q13 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q13 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q13 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q13 ∷
   re 22 3 (ℓ "乑") ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q13 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q15 ∷
   rw 25 q12 ∷
   rw 86 q13 ∷
   rw 85 q14 ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q15 ∷
   re 83 1 (ℓ "乏乄乏") ∷
   rw 85 q15 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q15 ∷
   re 81 1 (ℓ "乏乄乏") ∷
   rw 83 q15 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q15 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q15 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 80 q15 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q15 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q15 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q15 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q15 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q15 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q15 ∷
   rw 71 q16 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q15 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q15 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q15 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q15 ∷
   rw 66 q16 ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw 67 q15 ∷
   rw 64 q16 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw 65 q15 ∷
   re 62 1 (ℓ "乏丹乏") ∷
   rw 64 q15 ∷
   rw 61 q18 ∷
   rw 60 q18 ∷
   rw 59 q17 ∷
   rw 58 q18 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q14 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q15 ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw 55 q15 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q15 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q15 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q15 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q15 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 50 q15 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q15 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q15 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q15 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q15 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q15 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q15 ∷
   rw 41 q16 ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw 42 q15 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q15 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q15 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q15 ∷
   rw 36 q16 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q15 ∷
   rw 34 q16 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q15 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 34 q15 ∷
   rw 31 q18 ∷
   rw 30 q18 ∷
   rw 29 q17 ∷
   rw 28 q18 ∷
   rw 27 q17 ∷
   rw 26 q17 ∷
   rw 27 q11 ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q13 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q13 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q13 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q13 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q13 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q13 ∷
   re 36 3 (ℓ "乑") ∷
   rw 39 q13 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q15 ∷ []) Eq.refl
