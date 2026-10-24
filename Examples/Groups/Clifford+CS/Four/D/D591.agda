{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD591 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D591 (W : Ws) (Sᴰ : SD591) where

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
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 : St 278
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 : St 284
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 : St 1034
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 : St 1035
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 = pickᴰ 3 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-Z-passes-X0-CS01-CS01-CK10-CS01-CX13-CS : St 1057
  lem-Z-passes-X0-CS01-CS01-CK10-CS01-CX13-CS = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 1058
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = wE 1701 W
  q2 : Eqn
  q2 = sE 1057 lem-Z-passes-X0-CS01-CS01-CK10-CS01-CX13-CS
  q3 : Eqn
  q3 = wE 387 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 219 W
  q6 : Eqn
  q6 = wE 327 W
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 30 W
  q9 : Eqn
  q9 = wE 25 W
  q10 : Eqn
  q10 = wE 275 W
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 315 W
  q13 : Eqn
  q13 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 1702 W

-- conjF X0 CS01 CS01 CK10 CS01 CX13 CS: 310 steps
lem-conjF-X0-CS01-CS01-CK10-CS01-CX13-CS : ⟪ (ℓ "丳丢丒丣丢丒丌丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丌") ⟫ʷ ≈ ⟪ (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丳丢丒丣丢丒") ⟫ʷ
lem-conjF-X0-CS01-CS01-CK10-CS01-CX13-CS = derive (ℓ "丳丢丒丣丢丒丌丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄丌") (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丳丢丒丣丢丒")
  (rw 0 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 81 q4 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   rw 3 q5 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q7 ∷
   rw 5 q8 ∷
   rw 6 q7 ∷
   re 4 3 (ℓ "丰") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   rw 6 q9 ∷
   rw 7 q7 ∷
   re 5 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 7 q9 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q9 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "乔") ∷
   rw 9 q11 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   rw 11 q9 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 12 q9 ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q7 ∷
   rw 13 q9 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q7 ∷
   rw 14 q9 ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q7 ∷
   rw 15 q9 ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q7 ∷
   rw 16 q9 ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q7 ∷
   rw 17 q8 ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丰") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 18 q7 ∷
   rw 19 q9 ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw 19 q7 ∷
   rw 20 q10 ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "乔") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q7 ∷
   rw 21 q9 ∷
   rw 22 q7 ∷
   re 20 3 (ℓ "丽") ∷
   rw 21 q10 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 22 q7 ∷
   rw 23 q9 ∷
   rw 24 q7 ∷
   re 22 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 23 q7 ∷
   rw 24 q9 ∷
   rw 25 q7 ∷
   re 23 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 24 q7 ∷
   rw 25 q9 ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "丽") ∷
   rw 25 q11 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 26 q7 ∷
   rw 27 q10 ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "乔") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 27 q7 ∷
   rw 28 q9 ∷
   rw 29 q7 ∷
   re 27 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 28 q7 ∷
   rw 29 q9 ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 29 q7 ∷
   rw 30 q9 ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q7 ∷
   rw 31 q9 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q7 ∷
   rw 32 q9 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q7 ∷
   rw 33 q9 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q7 ∷
   rw 34 q8 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "丰") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q7 ∷
   rw 35 q9 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q7 ∷
   rw 36 q9 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q7 ∷
   rw 37 q9 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q7 ∷
   rw 38 q9 ∷
   rw 39 q7 ∷
   re 37 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q7 ∷
   rw 39 q9 ∷
   rw 40 q7 ∷
   re 38 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q7 ∷
   rw 40 q9 ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q7 ∷
   rw 41 q9 ∷
   rw 42 q7 ∷
   re 40 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q7 ∷
   rw 42 q9 ∷
   rw 43 q7 ∷
   re 41 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q7 ∷
   rw 43 q9 ∷
   rw 44 q7 ∷
   re 42 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q7 ∷
   rw 44 q9 ∷
   rw 45 q7 ∷
   re 43 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q7 ∷
   rw 45 q9 ∷
   rw 46 q7 ∷
   re 44 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q7 ∷
   rw 46 q9 ∷
   rw 47 q7 ∷
   re 45 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q7 ∷
   rw 47 q9 ∷
   rw 48 q7 ∷
   re 46 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q7 ∷
   rw 48 q9 ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q7 ∷
   rw 49 q9 ∷
   rw 50 q7 ∷
   re 48 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q7 ∷
   rw 50 q9 ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q7 ∷
   rw 51 q9 ∷
   rw 52 q7 ∷
   re 50 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q7 ∷
   rw 52 q9 ∷
   rw 53 q7 ∷
   re 51 3 (ℓ "丽") ∷
   rw 52 q11 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 56 q7 ∷
   rw 57 q10 ∷
   rw 58 q7 ∷
   re 56 3 (ℓ "乔") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q7 ∷
   rw 58 q9 ∷
   rw 59 q7 ∷
   re 57 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 58 q7 ∷
   rw 59 q9 ∷
   rw 60 q7 ∷
   re 58 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q7 ∷
   rw 60 q9 ∷
   rw 61 q7 ∷
   re 59 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q7 ∷
   rw 61 q9 ∷
   rw 62 q7 ∷
   re 60 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q7 ∷
   rw 62 q9 ∷
   rw 63 q7 ∷
   re 61 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q7 ∷
   rw 63 q9 ∷
   rw 64 q7 ∷
   re 62 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q7 ∷
   rw 64 q9 ∷
   rw 65 q7 ∷
   re 63 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 64 q7 ∷
   rw 65 q9 ∷
   rw 66 q7 ∷
   re 64 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 65 q7 ∷
   rw 66 q9 ∷
   rw 67 q7 ∷
   re 65 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏丹乏") ∷
   rw 66 q7 ∷
   rw 67 q8 ∷
   rw 68 q7 ∷
   re 66 3 (ℓ "丰") ∷
   rw 67 q5 ∷
   rw 68 q5 ∷
   rw 69 q5 ∷
   rw 70 q12 ∷
   rw 71 q6 ∷
   rw 72 q5 ∷
   rw 73 q5 ∷
   rw 74 q5 ∷
   rw 75 q5 ∷
   rw 76 q5 ∷
   rw 77 q5 ∷
   rw 78 q13 ∷
   rw 79 q10 ∷
   rw 80 q14 ∷
   rw 80 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1498 W
  q17 : Eqn
  q17 = wE 1663 W
  q18 : Eqn
  q18 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q19 : Eqn
  q19 = wE 1664 W

-- pass [X2 CKd21 X2] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丘么丘三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丘么丘三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丘么丘")
  (rw 0 q16 ∷
   rw 0 q17 ∷
   rw 4 q18 ∷
   rw 8 q19 ∷
   rw 12 q16 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1496 W
  q21 : Eqn
  q21 = wE 1665 W
  q22 : Eqn
  q22 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q23 : Eqn
  q23 = wE 1666 W

-- pass [X2 CK21 X2] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丘乇丘三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丘乇丘三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丘乇丘")
  (rw 0 q20 ∷
   rw 0 q21 ∷
   rw 4 q22 ∷
   rw 8 q23 ∷
   rw 12 q20 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = sE 1035 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2
  q25 : Eqn
  q25 = sE 284 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2
  q26 : Eqn
  q26 = sE 1034 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2
  q27 : Eqn
  q27 = sE 1058 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2
  q28 : Eqn
  q28 = sE 278 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2

-- Bar(SSSKSS;2,1->0) passes split Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丽习举习丌丘丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q24 ∷
   rw 3 q25 ∷
   rw 6 q26 ∷
   rw 9 q26 ∷
   rw 12 q27 ∷
   rw 20 q24 ∷
   rw 23 q24 ∷
   rw 26 q28 ∷
   rw 29 q26 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1703 W
  q30 : Eqn
  q30 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q31 : Eqn
  q31 = wE 1704 W

-- pass [X1 CS10 X1] [Sd0 K0 K0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 Kd0 Kd0 S0]: 3 steps
lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0 : ⟪ (ℓ "丒丠丒三上上上上九中九丮下下下下丈") ⟫ʷ ≈ ⟪ (ℓ "三上上上上九中九丮下下下下丈丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-Sd0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-S0 = derive (ℓ "丒丠丒三上上上上九中九丮下下下下丈") (ℓ "三上上上上九中九丮下下下下丈丒丠丒")
  (rw 0 q29 ∷
   rw 5 q30 ∷
   rw 9 q31 ∷ []) Eq.refl
