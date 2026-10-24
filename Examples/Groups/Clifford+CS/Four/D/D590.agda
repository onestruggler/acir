{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD590 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D590 (W : Ws) (Sᴰ : SD590) where

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
  lem-AXIOM-LF-at0132 : St 638
  lem-AXIOM-LF-at0132 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 : St 254
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 : St 257
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 : St 1032
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : St 1033
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 1051
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 6 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02 : St 1052
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02 = pickᴰ 7 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 : St 1053
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-TOFF213 : St 1054
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-TOFF213 = pickᴰ 9 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 1055
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 10 Sᴰ
  lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1056
  lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = sE 638 lem-AXIOM-LF-at0132
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
  q7 = wE 1700 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = sE 1054 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-TOFF213
  q10 : Eqn
  q10 = sE 1052 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02
  q11 : Eqn
  q11 = sE 1053 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20
  q12 : Eqn
  q12 = sE 638 lem-AXIOM-LF-at0132

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK20 CS03 CS03 CS03 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S2 CK20]: 205 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q1 ∷
   rw 58 q2 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q3 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q3 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q3 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q3 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q3 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q3 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q3 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   rw 44 q4 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   rw 39 q4 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q3 ∷
   rw 37 q4 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q3 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q3 ∷
   rw 34 q5 ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   rw 29 q6 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q6 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q8 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q8 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q8 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乀") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乑") ∷
   rw⁻ 29 q6 ∷
   rw⁻ 30 q6 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q6 ∷
   rw⁻ 33 q5 ∷
   rw⁻ 34 q5 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乀") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q8 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q8 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "乑") ∷
   rw 44 q8 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "乀") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "乑") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乑") ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q3 ∷
   rw 29 q9 ∷
   rw 30 q10 ∷
   rw 61 q9 ∷
   rw 62 q11 ∷
   rw⁻ 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1376 W
  q14 : Eqn
  q14 = wE 1377 W
  q15 : Eqn
  q15 = wE 1378 W
  q16 : Eqn
  q16 = sE 1051 lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q17 : Eqn
  q17 = wE 1379 W
  q18 : Eqn
  q18 = wE 1380 W
  q19 : Eqn
  q19 = wE 1381 W

-- pass [X3 CKd31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乕丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乕丞丽习举习") (ℓ "丽习举习丞乕丞")
  (rw 0 q13 ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   rw 3 q14 ∷
   rw⁻ 4 q16 ∷
   rw 10 q17 ∷
   rw 9 q18 ∷
   rw 8 q19 ∷
   rw 7 q18 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 1056 lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [S1]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1 : ⟪ (ℓ "中九丮九与") ⟫ʷ ≈ ⟪ (ℓ "与中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1 = derive (ℓ "中九丮九与") (ℓ "与中九丮九")
  (rw⁻ 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 5 W
  q22 : Eqn
  q22 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q23 : Eqn
  q23 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = wE 140 W
  q26 : Eqn
  q26 = wE 1412 W
  q27 : Eqn
  q27 = wE 142 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 173 W
  q30 : Eqn
  q30 = wE 1413 W
  q31 : Eqn
  q31 = wE 175 W
  q32 : Eqn
  q32 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X3 CK30 X3] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 61 steps
lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丞乑丞丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丞乑丞丘中九丮九丘") (ℓ "丘中九丮九丘丞乑丞")
  (rw 4 q21 ∷
   rw⁻ 3 q22 ∷
   rw⁻ 2 q23 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q24 ∷
   rw 2 q25 ∷
   rw⁻ 1 q24 ∷
   re 2 3 (ℓ "乔") ∷
   rw⁻ 0 q23 ∷
   rw 1 q26 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q24 ∷
   rw 3 q27 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   rw 4 q2 ∷
   rw 3 q29 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q31 ∷
   rw 4 q3 ∷
   rw 1 q32 ∷
   rw 8 q2 ∷
   rw 7 q29 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q3 ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 5 q31 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q31 ∷
   rw 8 q3 ∷
   rw 9 q21 ∷
   rw⁻ 8 q22 ∷
   rw⁻ 7 q23 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q24 ∷
   rw 7 q25 ∷
   rw⁻ 6 q24 ∷
   re 7 3 (ℓ "乔") ∷
   rw⁻ 5 q23 ∷
   rw 6 q26 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q24 ∷
   rw 8 q27 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q23 ∷
   rw 9 q28 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1033 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2
  q34 : Eqn
  q34 = sE 257 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2
  q35 : Eqn
  q35 = sE 1032 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2
  q36 : Eqn
  q36 = sE 1055 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2
  q37 : Eqn
  q37 = sE 254 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q33 ∷
   rw 3 q34 ∷
   rw 6 q35 ∷
   rw 9 q35 ∷
   rw 12 q36 ∷
   rw 20 q33 ∷
   rw 23 q33 ∷
   rw 26 q37 ∷
   rw 29 q35 ∷ []) Eq.refl
