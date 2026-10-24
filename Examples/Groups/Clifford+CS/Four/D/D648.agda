{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD648 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D648 (W : Ws) (Sᴰ : SD648) where

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
  lem-AXIOM-LF-at1023 : St 1596
  lem-AXIOM-LF-at1023 = pickᴰ 0 Sᴰ
  lem-pass-TOFF302-vs-X0-TOFF302-X0 : St 1597
  lem-pass-TOFF302-vs-X0-TOFF302-X0 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 : St 752
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 = pickᴰ 2 Sᴰ
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : St 1069
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : St 1079
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-TOFF302-X0 : St 1401
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-TOFF302-X0 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 : St 1402
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 = pickᴰ 6 Sᴰ
  lem-pass-TOFF302-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : St 1598
  lem-pass-TOFF302-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = pickᴰ 7 Sᴰ
  lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 : St 1599
  lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = sE 1596 lem-AXIOM-LF-at1023
  q2 : Eqn
  q2 = wE 873 W
  q3 : Eqn
  q3 = sE 1069 lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0
  q4 : Eqn
  q4 = sE 1598 lem-pass-TOFF302-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0
  q5 : Eqn
  q5 = sE 1079 lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0
  q6 : Eqn
  q6 = sE 1401 lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-TOFF302-X0
  q7 : Eqn
  q7 = sE 1597 lem-pass-TOFF302-vs-X0-TOFF302-X0
  q8 : Eqn
  q8 = sE 1402 lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0
  q9 : Eqn
  q9 = sE 752 lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0
  q10 : Eqn
  q10 = sE 1599 lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0
  q11 : Eqn
  q11 = wE 1949 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = wE 1106 W
  q14 : Eqn
  q14 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = wE 30 W
  q17 : Eqn
  q17 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 122 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = wE 127 W
  q23 : Eqn
  q23 = wE 7 W
  q24 : Eqn
  q24 = wE 74 W
  q25 : Eqn
  q25 = wE 337 W
  q26 : Eqn
  q26 = wE 1947 W
  q27 : Eqn
  q27 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q28 : Eqn
  q28 = wE 1 W
  q29 : Eqn
  q29 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q30 : Eqn
  q30 = wE 3 W
  q31 : Eqn
  q31 = wE 464 W
  q32 : Eqn
  q32 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q34 : Eqn
  q34 = wE 1950 W

-- L87 merge-k CS01 CS01 CK01 CS01 CX02 CS12 CS12 CS12  0: 411 steps
lem-L87-merge-k-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12--0 : ⟪ (ℓ "丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丌丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丌") ⟫ʷ ≈ ⟪ (ℓ "丶丶乇丶乇乇丶丶乇丶乇乇乌丽丽丽乔丽丽丽丽丽乔丽丽乌丽丽乔丽乔乔丽丽乔丽乔乔") ⟫ʷ
lem-L87-merge-k-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12--0 = derive (ℓ "丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丌丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丌") (ℓ "丶丶乇丶乇乇丶丶乇丶乇乇乌丽丽丽乔丽丽丽丽丽乔丽丽乌丽丽乔丽乔乔丽丽乔丽乔乔")
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
   rw 16 q12 ∷
   rw 15 q13 ∷
   re 14 1 (ℓ "並乨並") ∷
   re 15 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 14 q14 ∷
   rw 15 q15 ∷
   rw 16 q16 ∷
   rw 17 q17 ∷
   rw 18 q16 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q18 ∷
   rw 20 q19 ∷
   rw 21 q18 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   rw 21 q20 ∷
   rw 22 q21 ∷
   rw 21 q22 ∷
   rw⁻ 20 q14 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q18 ∷
   rw 20 q23 ∷
   rw⁻ 19 q18 ∷
   re 20 3 (ℓ "丽") ∷
   rw 18 q24 ∷
   rw⁻ 17 q17 ∷
   rw 16 q24 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 14 q14 ∷
   rw 15 q25 ∷
   re 15 8 (ℓ "乨") ∷
   rw 13 q13 ∷
   re 12 1 (ℓ "並乨並") ∷
   re 13 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 12 q14 ∷
   rw 13 q15 ∷
   rw 14 q16 ∷
   rw 15 q17 ∷
   rw 16 q16 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q18 ∷
   rw 18 q19 ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q14 ∷
   rw 19 q20 ∷
   rw 20 q21 ∷
   rw 19 q22 ∷
   rw⁻ 18 q14 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q18 ∷
   rw 18 q23 ∷
   rw⁻ 17 q18 ∷
   re 18 3 (ℓ "丽") ∷
   rw 16 q24 ∷
   rw⁻ 15 q17 ∷
   rw 14 q24 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q14 ∷
   rw 13 q25 ∷
   re 13 8 (ℓ "乨") ∷
   rw 13 q26 ∷
   rw 12 q27 ∷
   rw 13 q21 ∷
   rw 77 q28 ∷
   rw 76 q29 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 77 q30 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 76 q30 ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw 75 q30 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 74 q30 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 73 q30 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 72 q30 ∷
   re 69 1 (ℓ "乏个乏") ∷
   rw 71 q30 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 70 q30 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 69 q30 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 68 q30 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 67 q30 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 66 q30 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 65 q30 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 64 q30 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 63 q30 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 62 q30 ∷
   rw 59 q31 ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 60 q30 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 59 q30 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 58 q30 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 57 q30 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 56 q30 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 55 q30 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 54 q30 ∷
   re 51 1 (ℓ "乏个乏") ∷
   rw 53 q30 ∷
   rw 50 q32 ∷
   rw 49 q32 ∷
   rw 48 q33 ∷
   rw 47 q32 ∷
   rw 46 q32 ∷
   rw 45 q32 ∷
   rw 44 q29 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 45 q30 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 44 q30 ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 43 q30 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 42 q30 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 41 q30 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 40 q30 ∷
   re 37 1 (ℓ "乏个乏") ∷
   rw 39 q30 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 38 q30 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 37 q30 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 36 q30 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q30 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 34 q30 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q30 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q30 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q30 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q30 ∷
   rw 27 q31 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 28 q30 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q30 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q30 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q30 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q30 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q30 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q30 ∷
   re 19 1 (ℓ "乏个乏") ∷
   rw 21 q30 ∷
   rw 18 q32 ∷
   rw 17 q32 ∷
   rw 16 q33 ∷
   rw 15 q32 ∷
   rw 14 q32 ∷
   rw 13 q32 ∷
   rw 14 q34 ∷
   rw 15 q28 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q28 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q28 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q28 ∷
   re 16 3 (ℓ "乔") ∷
   rw 19 q28 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q28 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q28 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q28 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q28 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q28 ∷
   re 22 3 (ℓ "乔") ∷
   rw 25 q28 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q28 ∷
   re 24 3 (ℓ "丽") ∷
   rw 25 q30 ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   re 27 1 (ℓ "並乨並") ∷
   re 28 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 27 q14 ∷
   rw 28 q15 ∷
   rw 29 q16 ∷
   rw 30 q17 ∷
   rw 31 q16 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q18 ∷
   rw 33 q19 ∷
   rw 34 q18 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q14 ∷
   rw 34 q20 ∷
   rw 35 q21 ∷
   rw 34 q22 ∷
   rw⁻ 33 q14 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q18 ∷
   rw 33 q23 ∷
   rw⁻ 32 q18 ∷
   re 33 3 (ℓ "丽") ∷
   rw 31 q24 ∷
   rw⁻ 30 q17 ∷
   rw 29 q24 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 27 q14 ∷
   rw 28 q25 ∷
   re 28 8 (ℓ "乨") ∷
   rw 26 q13 ∷
   re 25 1 (ℓ "並乨並") ∷
   re 26 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 25 q14 ∷
   rw 26 q15 ∷
   rw 27 q16 ∷
   rw 28 q17 ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q18 ∷
   rw 31 q19 ∷
   rw 32 q18 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q14 ∷
   rw 32 q20 ∷
   rw 33 q21 ∷
   rw 32 q22 ∷
   rw⁻ 31 q14 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q18 ∷
   rw 31 q23 ∷
   rw⁻ 30 q18 ∷
   re 31 3 (ℓ "丽") ∷
   rw 29 q24 ∷
   rw⁻ 28 q17 ∷
   rw 27 q24 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q14 ∷
   rw 26 q25 ∷
   re 26 8 (ℓ "乨") ∷
   rw 26 q26 ∷
   rw 25 q27 ∷
   rw 26 q21 ∷
   rw 86 q28 ∷
   rw 85 q29 ∷
   re 84 1 (ℓ "乏乇乏") ∷
   rw 86 q30 ∷
   re 83 1 (ℓ "乏乇乏") ∷
   rw 85 q30 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 84 q30 ∷
   re 81 1 (ℓ "乏乇乏") ∷
   rw 83 q30 ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 82 q30 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 81 q30 ∷
   re 78 1 (ℓ "乏个乏") ∷
   rw 80 q30 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 79 q30 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 78 q30 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 77 q30 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 76 q30 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 75 q30 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 74 q30 ∷
   rw 71 q31 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 72 q30 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 71 q30 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 70 q30 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 69 q30 ∷
   rw 66 q31 ∷
   re 65 1 (ℓ "乏乇乏") ∷
   rw 67 q30 ∷
   rw 64 q31 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 65 q30 ∷
   re 62 1 (ℓ "乏个乏") ∷
   rw 64 q30 ∷
   rw 61 q33 ∷
   rw 60 q33 ∷
   rw 59 q32 ∷
   rw 58 q33 ∷
   rw 57 q32 ∷
   rw 56 q32 ∷
   rw 55 q29 ∷
   re 54 1 (ℓ "乏乇乏") ∷
   rw 56 q30 ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 55 q30 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 54 q30 ∷
   re 51 1 (ℓ "乏乇乏") ∷
   rw 53 q30 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 52 q30 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 51 q30 ∷
   re 48 1 (ℓ "乏个乏") ∷
   rw 50 q30 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 49 q30 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 48 q30 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 47 q30 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 46 q30 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 45 q30 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 44 q30 ∷
   rw 41 q31 ∷
   re 40 1 (ℓ "乏乇乏") ∷
   rw 42 q30 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 41 q30 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 40 q30 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 39 q30 ∷
   rw 36 q31 ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 37 q30 ∷
   rw 34 q31 ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 35 q30 ∷
   re 32 1 (ℓ "乏个乏") ∷
   rw 34 q30 ∷
   rw 31 q33 ∷
   rw 30 q33 ∷
   rw 29 q32 ∷
   rw 28 q33 ∷
   rw 27 q32 ∷
   rw 26 q32 ∷
   rw 27 q11 ∷
   rw 28 q28 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q28 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q28 ∷
   re 28 3 (ℓ "乔") ∷
   rw 31 q28 ∷
   re 29 3 (ℓ "丽") ∷
   rw 32 q28 ∷
   re 30 3 (ℓ "乔") ∷
   rw 33 q28 ∷
   re 31 3 (ℓ "乔") ∷
   rw 34 q28 ∷
   re 32 3 (ℓ "丽") ∷
   rw 35 q28 ∷
   re 33 3 (ℓ "丽") ∷
   rw 36 q28 ∷
   re 34 3 (ℓ "乔") ∷
   rw 37 q28 ∷
   re 35 3 (ℓ "丽") ∷
   rw 38 q28 ∷
   re 36 3 (ℓ "乔") ∷
   rw 39 q28 ∷
   re 37 3 (ℓ "乔") ∷
   rw 38 q30 ∷ []) Eq.refl
