{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD616 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D616 (W : Ws) (Sᴰ : SD616) where

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
  lem-HD-X-form : St 1390
  lem-HD-X-form = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02 : St 1391
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 : St 1392
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 = pickᴰ 2 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 : St 1393
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-ᵖinv : St 1394
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-ᵖinv = pickᴰ 4 Sᴰ
  lem-pass-X2-CS20-X2-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 1395
  lem-pass-X2-CS20-X2-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 5 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : St 1396
  lem-pass-X2-CSd20-X2-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = pickᴰ 6 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 : St 1397
  lem-pass-X3-CKd30-X3-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = sE 1391 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = wE 1829 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = wE 1830 W
  q10 : Eqn
  q10 = sE 1394 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-ᵖinv
  q11 : Eqn
  q11 = wE 1831 W
  q12 : Eqn
  q12 = wE 1832 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK30 CS02 CS02 CS02 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S3 CK30]: 228 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 0 q1 ∷
   rw 51 q2 ∷
   re 50 1 (ℓ "乏乄乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q3 ∷
   rw 36 q4 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q3 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q3 ∷
   rw 31 q4 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q3 ∷
   rw 29 q4 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 29 q3 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 22 q7 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "乑") ∷
   rw⁻ 22 q6 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 27 q6 ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乀") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q8 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "乀") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "乑") ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q3 ∷
   rw 53 q9 ∷
   rw 22 q10 ∷
   rw 22 q11 ∷
   rw 111 q2 ∷
   re 110 1 (ℓ "乏乄乏") ∷
   rw 112 q3 ∷
   rw 109 q4 ∷
   re 108 1 (ℓ "乏丧乏") ∷
   rw 110 q3 ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw 109 q3 ∷
   re 106 1 (ℓ "乏乄乏") ∷
   rw 108 q3 ∷
   re 105 1 (ℓ "乏丧乏") ∷
   rw 107 q3 ∷
   re 104 1 (ℓ "乏丧乏") ∷
   rw 106 q3 ∷
   re 103 1 (ℓ "乏丧乏") ∷
   rw 105 q3 ∷
   re 102 1 (ℓ "乏丹乏") ∷
   rw 104 q3 ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw 103 q3 ∷
   re 100 1 (ℓ "乏丧乏") ∷
   rw 102 q3 ∷
   re 99 1 (ℓ "乏丧乏") ∷
   rw 101 q3 ∷
   re 98 1 (ℓ "乏丧乏") ∷
   rw 100 q3 ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q3 ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q3 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q3 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q3 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q3 ∷
   rw 92 q4 ∷
   re 91 1 (ℓ "乏乄乏") ∷
   rw 93 q3 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q3 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q3 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q3 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q3 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q3 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q3 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 86 q3 ∷
   rw 83 q6 ∷
   rw 82 q6 ∷
   rw 81 q5 ∷
   rw 80 q6 ∷
   rw 79 q6 ∷
   rw 78 q6 ∷
   rw 79 q12 ∷
   rw 78 q8 ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "乑") ∷
   rw⁻ 80 q6 ∷
   rw⁻ 81 q6 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q6 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乀") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乑") ∷
   rw 88 q8 ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乑") ∷
   rw 90 q8 ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "中") ∷
   rw 94 q2 ∷
   re 92 3 (ℓ "中") ∷
   rw 95 q2 ∷
   re 93 3 (ℓ "中") ∷
   rw 96 q2 ∷
   re 94 3 (ℓ "乑") ∷
   rw 95 q8 ∷
   rw 98 q2 ∷
   re 96 3 (ℓ "中") ∷
   rw 99 q2 ∷
   re 97 3 (ℓ "中") ∷
   rw 100 q2 ∷
   re 98 3 (ℓ "中") ∷
   rw 101 q2 ∷
   re 99 3 (ℓ "中") ∷
   rw 102 q2 ∷
   re 100 3 (ℓ "中") ∷
   rw 103 q2 ∷
   re 101 3 (ℓ "中") ∷
   rw 104 q2 ∷
   re 102 3 (ℓ "乀") ∷
   rw 105 q2 ∷
   re 103 3 (ℓ "中") ∷
   rw 106 q2 ∷
   re 104 3 (ℓ "中") ∷
   rw 107 q2 ∷
   re 105 3 (ℓ "乑") ∷
   rw 108 q2 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q2 ∷
   re 107 3 (ℓ "乑") ∷
   rw 110 q2 ∷
   re 108 3 (ℓ "乑") ∷
   rw 109 q3 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 1390 lem-HD-X-form
  q14 : Eqn
  q14 = sE 1392 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20
  q15 : Eqn
  q15 = sE 1393 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30
  q16 : Eqn
  q16 = wE 1845 W
  q17 : Eqn
  q17 = sE 1390 lem-HD-X-form

-- X P1 -> P1 X: 5 steps
lem-X-P1--⟶-P1-X : ⟪ (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") ⟫ʷ
lem-X-P1--⟶-P1-X = derive (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨")
  (rw 0 q13 ∷
   rw 111 q14 ∷
   rw⁻ 31 q15 ∷
   rw 0 q16 ∷
   rw⁻ 29 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1459 W
  q19 : Eqn
  q19 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q20 : Eqn
  q20 = wE 175 W
  q21 : Eqn
  q21 = sE 1397 lem-pass-X3-CKd30-X3-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1
  q22 : Eqn
  q22 = eqn (ℓ "上丒") (ℓ "丒上") (low₁-comm (K) (X))
  q23 : Eqn
  q23 = wE 1846 W
  q24 : Eqn
  q24 = wE 1460 W
  q25 : Eqn
  q25 = wE 173 W
  q26 : Eqn
  q26 = wE 1461 W

-- CA CK30 Gad(t=0, W=(1,), d=Kd, e=1): 25 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨1⟩-d≡Kd-e≡1⟩ : ⟪ (ℓ "乑丒下九中九丮上丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乑") ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨1⟩-d≡Kd-e≡1⟩ = derive (ℓ "乑丒下九中九丮上丒") (ℓ "丒九中九丮丒乑")
  (rw 1 q2 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q3 ∷
   rw 1 q18 ∷
   rw⁻ 0 q19 ∷
   rw 1 q20 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q20 ∷
   rw 4 q3 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷
   rw 5 q24 ∷
   rw 5 q22 ∷
   rw 10 q2 ∷
   rw 9 q25 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q3 ∷
   rw 7 q25 ∷
   rw 6 q19 ∷
   rw 7 q26 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q3 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1812 W
  q28 : Eqn
  q28 = sE 1395 lem-pass-X2-CS20-X2-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q29 : Eqn
  q29 = eqn (ℓ "三丒") (ℓ "丒三") (low₁-comm ((S • S • S)) (X))
  q30 : Eqn
  q30 = wE 1813 W
  q31 : Eqn
  q31 = wE 1732 W
  q32 : Eqn
  q32 = wE 1814 W

-- CA CSd20 Gad(t=0, W=(1,), d=1, e=1): 7 steps
lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (ℓ "丨丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒三九中九丮丈丒丨") ⟫ʷ
lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (ℓ "丨丒九中九丮丒") (ℓ "丒三九中九丮丈丒丨")
  (rw 0 q27 ∷
   rw 1 q28 ∷
   rw 0 q29 ∷
   rw 1 q30 ∷
   rw 6 q31 ∷
   rw 7 q29 ∷
   rw 8 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1815 W
  q34 : Eqn
  q34 = sE 1396 lem-pass-X2-CSd20-X2-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1
  q35 : Eqn
  q35 = eqn (ℓ "丈丒") (ℓ "丒丈") (low₁-comm (S) (X))
  q36 : Eqn
  q36 = wE 1728 W
  q37 : Eqn
  q37 = wE 1727 W
  q38 : Eqn
  q38 = wE 1816 W

-- CA CS20 Gad(t=0, W=(1,), d=Sd, e=1): 7 steps
lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : ⟪ (ℓ "丧丒三九中九丮丈丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丧") ⟫ʷ
lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = derive (ℓ "丧丒三九中九丮丈丒") (ℓ "丒九中九丮丒丧")
  (rw 0 q33 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   rw 5 q37 ∷
   rw 5 q35 ∷
   rw 6 q38 ∷ []) Eq.refl
