{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD618 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D618 (W : Ws) (Sᴰ : SD618) where

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
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 : St 1402
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0 : St 1403
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 : St 1404
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 : St 1405
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = wE 30 W
  q5 : Eqn
  q5 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 122 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 127 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 74 W
  q13 : Eqn
  q13 = wE 337 W
  q14 : Eqn
  q14 = wE 1800 W
  q15 : Eqn
  q15 = wE 317 W
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 124 W
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = wE 464 W
  q23 : Eqn
  q23 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q24 : Eqn
  q24 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q25 : Eqn
  q25 = wE 1853 W
  q26 : Eqn
  q26 = wE 151 W
  q27 : Eqn
  q27 = sE 1402 lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0
  q28 : Eqn
  q28 = wE 1854 W
  q29 : Eqn
  q29 = wE 1106 W
  q30 : Eqn
  q30 = wE 1803 W

-- pass [TOFF302] [X0 CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13 X0]: 365 steps
lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 : ⟪ (ℓ "乧丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌") ⟫ʷ ≈ ⟪ (ℓ "丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌乧") ⟫ʷ
lem-pass-TOFF302-vs-X0-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-X0 = derive (ℓ "乧丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌") (ℓ "丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌乧")
  (rw 1 q1 ∷
   re 0 1 (ℓ "並乨並") ∷
   re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q11 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q12 ∷
   rw⁻ 3 q5 ∷
   rw 2 q12 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 0 q2 ∷
   rw 1 q13 ∷
   re 1 8 (ℓ "乨") ∷
   rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q16 ∷
   rw 6 q5 ∷
   rw 7 q16 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q2 ∷
   rw 10 q18 ∷
   rw 3 q13 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 3 q15 ∷
   rw 4 q15 ∷
   rw 5 q9 ∷
   rw 38 q19 ∷
   rw 37 q20 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 38 q21 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 37 q21 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 36 q21 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q21 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 34 q21 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q21 ∷
   re 30 1 (ℓ "乏个乏") ∷
   rw 32 q21 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q21 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q21 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q21 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q21 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q21 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q21 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q21 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q21 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q21 ∷
   rw 20 q22 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 21 q21 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q21 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q21 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q21 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q21 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 16 q21 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q21 ∷
   re 12 1 (ℓ "乏个乏") ∷
   rw 14 q21 ∷
   rw 11 q23 ∷
   rw 10 q23 ∷
   rw 9 q24 ∷
   rw 8 q23 ∷
   rw 7 q23 ∷
   rw 6 q23 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 5 q25 ∷
   rw⁻ 4 q23 ∷
   rw⁻ 5 q23 ∷
   rw⁻ 6 q23 ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q23 ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "丰") ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q19 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "乔") ∷
   rw 18 q26 ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q19 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "丰") ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "丽") ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "丽") ∷
   rw 34 q19 ∷
   re 32 3 (ℓ "乔") ∷
   rw 35 q19 ∷
   re 33 3 (ℓ "丽") ∷
   rw 36 q19 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q20 ∷
   rw 36 q21 ∷
   rw⁻ 1 q27 ∷
   rw 32 q19 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q21 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q21 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 31 q21 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q21 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q21 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q21 ∷
   re 25 1 (ℓ "乏个乏") ∷
   rw 27 q21 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q21 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q21 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q21 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q21 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q21 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q21 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q21 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q21 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q21 ∷
   rw 15 q22 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q21 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q21 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q21 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q21 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 12 q21 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q21 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q21 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw 9 q21 ∷
   rw 6 q23 ∷
   rw 5 q23 ∷
   rw 4 q24 ∷
   rw 3 q23 ∷
   rw 2 q23 ∷
   rw 1 q23 ∷
   rw 0 q20 ∷
   rw 1 q28 ∷
   rw⁻ 0 q20 ∷
   rw⁻ 1 q23 ∷
   rw⁻ 2 q23 ∷
   rw⁻ 3 q23 ∷
   rw⁻ 4 q24 ∷
   rw⁻ 5 q23 ∷
   rw⁻ 6 q23 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "丰") ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "丽") ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "丽") ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "丽") ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "丽") ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q19 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "乔") ∷
   rw 15 q26 ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q19 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q19 ∷
   re 25 3 (ℓ "丰") ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "丽") ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "乔") ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "丽") ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q20 ∷
   rw⁻ 33 q20 ∷
   rw 34 q21 ∷
   rw 38 q1 ∷
   rw 37 q29 ∷
   rw 36 q29 ∷
   re 35 1 (ℓ "並乨並") ∷
   re 36 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 35 q2 ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q5 ∷
   rw 39 q4 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q6 ∷
   rw 41 q7 ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q2 ∷
   rw 42 q8 ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q6 ∷
   rw 41 q11 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (ℓ "丽") ∷
   rw 39 q12 ∷
   rw⁻ 38 q5 ∷
   rw 37 q12 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 35 q2 ∷
   rw 36 q13 ∷
   re 36 8 (ℓ "乨") ∷
   rw 34 q29 ∷
   rw 33 q29 ∷
   rw 34 q30 ∷
   re 34 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 33 q2 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw 37 q4 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q6 ∷
   rw 39 q7 ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q2 ∷
   rw 40 q8 ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   rw 35 q3 ∷
   rw 36 q16 ∷
   rw 37 q5 ∷
   rw 38 q16 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q6 ∷
   rw 40 q17 ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "丽") ∷
   rw 40 q2 ∷
   rw 41 q18 ∷
   rw 34 q13 ∷
   re 34 8 (ℓ "乨") ∷
   re 33 3 (ℓ "乧") ∷
   rw 34 q9 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 335 W
  q32 : Eqn
  q32 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q33 : Eqn
  q33 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q34 : Eqn
  q34 = wE 1294 W
  q35 : Eqn
  q35 = wE 368 W
  q36 : Eqn
  q36 = wE 1855 W
  q37 : Eqn
  q37 = wE 336 W
  q38 : Eqn
  q38 = wE 1856 W
  q39 : Eqn
  q39 = sE 1403 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0
  q40 : Eqn
  q40 = wE 1857 W
  q41 : Eqn
  q41 = wE 1858 W

-- pass [TOFF301] [X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0]: 125 steps
lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (ℓ "书丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌书") ⟫ʷ
lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = derive (ℓ "书丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌书")
  (rw 1 q19 ∷
   re 0 1 (ℓ "乏乣乏") ∷
   re 1 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 0 q31 ∷
   rw 3 q19 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q32 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q32 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q31 ∷
   rw⁻ 7 q33 ∷
   rw 8 q21 ∷
   rw 7 q33 ∷
   rw 6 q34 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q21 ∷
   rw 4 q32 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q21 ∷
   rw 2 q32 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   re 1 8 (ℓ "乣") ∷
   rw 1 q36 ∷
   rw⁻ 0 q20 ∷
   rw⁻ 1 q20 ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 2 q31 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q32 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q32 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q31 ∷
   rw⁻ 9 q33 ∷
   rw 2 q19 ∷
   rw 3 q37 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw⁻ 5 q32 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q21 ∷
   rw⁻ 7 q32 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q21 ∷
   rw 9 q37 ∷
   rw⁻ 10 q33 ∷
   rw 3 q35 ∷
   re 3 8 (ℓ "乣") ∷
   re 2 3 (ℓ "书") ∷
   rw⁻ 3 q20 ∷
   rw⁻ 4 q20 ∷
   rw 5 q21 ∷
   rw 4 q38 ∷
   rw⁻ 1 q39 ∷
   rw 0 q40 ∷
   rw 36 q19 ∷
   rw 35 q20 ∷
   rw 34 q20 ∷
   re 33 1 (ℓ "乏乣乏") ∷
   re 34 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 33 q31 ∷
   rw 36 q19 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q32 ∷
   rw 38 q19 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q32 ∷
   rw 40 q19 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q31 ∷
   rw⁻ 40 q33 ∷
   rw 41 q21 ∷
   rw 40 q33 ∷
   rw 39 q34 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q21 ∷
   rw 37 q32 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 38 q21 ∷
   rw 35 q32 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 36 q21 ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   re 34 8 (ℓ "乣") ∷
   rw 32 q20 ∷
   rw 31 q20 ∷
   rw 32 q41 ∷
   re 32 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 31 q31 ∷
   rw 34 q19 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 33 q32 ∷
   rw 36 q19 ∷
   re 34 3 (ℓ "举") ∷
   rw⁻ 35 q32 ∷
   rw 38 q19 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q31 ∷
   rw⁻ 38 q33 ∷
   rw 31 q19 ∷
   rw 32 q37 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q21 ∷
   rw⁻ 34 q32 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q21 ∷
   rw⁻ 36 q32 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q21 ∷
   rw 38 q37 ∷
   rw⁻ 39 q33 ∷
   rw 32 q35 ∷
   re 32 8 (ℓ "乣") ∷
   re 31 3 (ℓ "书") ∷
   rw 32 q21 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 1404 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0

-- Bar(SSKSKK;0,3->2) passes factors of X0 TOFF301 X0: 1 steps
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌书丌") ⟫ʷ ≈ ⟪ (ℓ "丌书丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌书丌") (ℓ "丌书丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 1405 lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0

-- Bar(SSSKSS;0,3->2) passes factors of X0 TOFF301 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌书丌") ⟫ʷ ≈ ⟪ (ℓ "丌书丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-TOFF301-X0 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌书丌") (ℓ "丌书丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 0 q43 ∷ []) Eq.refl
