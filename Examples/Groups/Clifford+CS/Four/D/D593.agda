{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD593 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D593 (W : Ws) (Sᴰ : SD593) where

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
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶2⟩-passes-II/IV-units-3-1 : St 1075
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶2⟩-passes-II/IV-units-3-1 = pickᴰ 0 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'02-⟶1⟩-passes-II/IV-units-3-2 : St 1076
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'02-⟶1⟩-passes-II/IV-units-3-2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK03-⟶1⟩-passes-II/IV-units-3-2 : St 1077
  lem-Bar⟨SSKSKK03-⟶1⟩-passes-II/IV-units-3-2 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2 : St 1078
  lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : St 1079
  lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : St 1080
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : St 1081
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 1106 W
  q3 : Eqn
  q3 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 127 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 337 W
  q15 : Eqn
  q15 = wE 1405 W
  q16 : Eqn
  q16 = wE 317 W
  q17 : Eqn
  q17 = wE 329 W
  q18 : Eqn
  q18 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q19 : Eqn
  q19 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q20 : Eqn
  q20 = wE 29 W
  q21 : Eqn
  q21 = wE 330 W
  q22 : Eqn
  q22 = sE 1076 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'02-⟶1⟩-passes-II/IV-units-3-2
  q23 : Eqn
  q23 = wE 1228 W
  q24 : Eqn
  q24 = wE 76 W
  q25 : Eqn
  q25 = wE 772 W
  q26 : Eqn
  q26 = wE 1406 W
  q27 : Eqn
  q27 = wE 24 W
  q28 : Eqn
  q28 = wE 25 W
  q29 : Eqn
  q29 = wE 124 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [X0 TOFF302 X0]: 125 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-TOFF302-X0 : ⟪ (ℓ "丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌乧丌") ⟫ʷ ≈ ⟪ (ℓ "丌乧丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-TOFF302-X0 = derive (ℓ "丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌乧丌") (ℓ "丌乧丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "並乨並") ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q3 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q12 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q13 ∷
   rw⁻ 33 q6 ∷
   rw 32 q13 ∷
   rw⁻ 31 q4 ∷
   rw⁻ 30 q3 ∷
   rw 31 q14 ∷
   re 31 8 (ℓ "乨") ∷
   rw 29 q2 ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "乏为乏") ∷
   rw 30 q7 ∷
   rw 31 q17 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "丱") ∷
   rw 31 q16 ∷
   rw 32 q18 ∷
   rw 33 q8 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q7 ∷
   rw 35 q8 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q19 ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 36 q7 ∷
   rw 37 q20 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "丮") ∷
   rw 37 q19 ∷
   rw 38 q16 ∷
   re 40 1 (ℓ "乏主乏") ∷
   rw 39 q7 ∷
   rw 40 q21 ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "串") ∷
   rw 40 q16 ∷
   rw 41 q10 ∷
   rw 0 q22 ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丬乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q23 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "乂") ∷
   rw 9 q2 ∷
   rw⁻ 8 q19 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q24 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 6 q19 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q7 ∷
   rw 6 q12 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q12 ∷
   rw⁻ 3 q18 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丫乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q25 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "乁") ∷
   rw 0 q2 ∷
   rw 1 q26 ∷
   rw 0 q16 ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q27 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q28 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q3 ∷
   rw 9 q29 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乨") ∷
   re 1 3 (ℓ "乧") ∷
   rw 2 q16 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 1079 lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0

-- Bar(SSSKSS;0,3->1) passes factors of X0 CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶1⟩-passes-factors-of-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌") ⟫ʷ ≈ ⟪ (ℓ "丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-Bar⟨SSSKSS03-⟶1⟩-passes-factors-of-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌") (ℓ "丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1646 W
  q32 : Eqn
  q32 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q33 : Eqn
  q33 = sE 1077 lem-Bar⟨SSKSKK03-⟶1⟩-passes-II/IV-units-3-2
  q34 : Eqn
  q34 = wE 1647 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [X0 TOFF302 X0]: 117 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-TOFF302-X0 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌乧丌") ⟫ʷ ≈ ⟪ (ℓ "丌乧丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-TOFF302-X0 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌乧丌") (ℓ "丌乧丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "並乨並") ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q3 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q12 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q13 ∷
   rw⁻ 33 q6 ∷
   rw 32 q13 ∷
   rw⁻ 31 q4 ∷
   rw⁻ 30 q3 ∷
   rw 31 q14 ∷
   re 31 8 (ℓ "乨") ∷
   rw 29 q2 ∷
   rw 30 q31 ∷
   rw 29 q16 ∷
   re 31 1 (ℓ "乏为乏") ∷
   rw 30 q7 ∷
   rw 31 q17 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "丱") ∷
   rw 31 q16 ∷
   rw 32 q18 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q7 ∷
   rw 34 q8 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q8 ∷
   rw 35 q32 ∷
   rw 36 q20 ∷
   rw 37 q32 ∷
   rw 38 q16 ∷
   re 40 1 (ℓ "乏主乏") ∷
   rw 39 q7 ∷
   rw 40 q21 ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "串") ∷
   rw 40 q16 ∷
   rw 41 q10 ∷
   rw 0 q33 ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丬乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q23 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "乂") ∷
   rw 9 q2 ∷
   rw⁻ 8 q32 ∷
   rw 7 q24 ∷
   rw⁻ 6 q32 ∷
   rw 5 q12 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q12 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q18 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丫乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q25 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "乁") ∷
   rw 0 q2 ∷
   rw 1 q34 ∷
   rw 0 q16 ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q27 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q28 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q3 ∷
   rw 9 q29 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乨") ∷
   re 1 3 (ℓ "乧") ∷
   rw 2 q16 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 1078 lem-Bar⟨SSSKSS03-⟶1⟩-passes-II/IV-units-3-2

-- pass [CS01 CS01 CS01 CK01 CS01 CS01 CX03 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CS13 CK31 CS13 CS13] [X0 TOFF302 X0]: 117 steps
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 : ⟪ (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌乧丌") ⟫ʷ ≈ ⟪ (ℓ "丌乧丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK01-CS01-CS01-CX03-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CS13-CK31-CS13-CS13-vs-X0-TOFF302-X0 = derive (ℓ "丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽丌乧丌") (ℓ "丌乧丌丠丠丠两丠丠丰丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丰丽丽丽乔丽丽")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (ℓ "並乨並") ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q6 ∷
   rw 36 q5 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q7 ∷
   rw 38 q8 ∷
   rw 39 q7 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q3 ∷
   rw 39 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q7 ∷
   rw 38 q12 ∷
   rw⁻ 37 q7 ∷
   re 38 3 (ℓ "丽") ∷
   rw 36 q13 ∷
   rw⁻ 35 q6 ∷
   rw 34 q13 ∷
   rw⁻ 33 q4 ∷
   rw⁻ 32 q3 ∷
   rw 33 q14 ∷
   re 33 8 (ℓ "乨") ∷
   rw 31 q2 ∷
   rw 32 q31 ∷
   rw 31 q16 ∷
   re 33 1 (ℓ "乏为乏") ∷
   rw 32 q7 ∷
   rw 33 q17 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "丱") ∷
   rw 33 q16 ∷
   rw 34 q18 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q8 ∷
   rw 37 q32 ∷
   rw 38 q20 ∷
   rw 39 q32 ∷
   rw 40 q16 ∷
   re 42 1 (ℓ "乏主乏") ∷
   rw 41 q7 ∷
   rw 42 q21 ∷
   rw 43 q7 ∷
   re 41 3 (ℓ "串") ∷
   rw 42 q16 ∷
   rw 43 q10 ∷
   rw 0 q35 ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丬乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q23 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "乂") ∷
   rw 9 q2 ∷
   rw⁻ 8 q32 ∷
   rw 7 q24 ∷
   rw⁻ 6 q32 ∷
   rw 5 q12 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q12 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q18 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丫乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q25 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "乁") ∷
   rw 0 q2 ∷
   rw 1 q34 ∷
   rw 0 q16 ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q27 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q28 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q3 ∷
   rw 9 q29 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乨") ∷
   re 1 3 (ℓ "乧") ∷
   rw 2 q16 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 1080 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0

-- Bar(SSKSKK;0,3->2) passes factors of X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0: 1 steps
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗") ⟫ʷ
lem-Bar⟨SSKSKK03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = derive (ℓ "丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌丧丧丫丧丫丫丰乗业乗业义义义乗业义义义义义义丰义义乗义乗乗")
  (rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1 W
  q38 : Eqn
  q38 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q39 : Eqn
  q39 = wE 335 W
  q40 : Eqn
  q40 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q41 : Eqn
  q41 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q42 : Eqn
  q42 = wE 3 W
  q43 : Eqn
  q43 = wE 1294 W
  q44 : Eqn
  q44 = wE 368 W
  q45 : Eqn
  q45 = wE 1721 W
  q46 : Eqn
  q46 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q47 : Eqn
  q47 = sE 1075 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶2⟩-passes-II/IV-units-3-1
  q48 : Eqn
  q48 = wE 1722 W
  q49 : Eqn
  q49 = wE 336 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [X0 TOFF301 X0]: 103 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0 : ⟪ (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌书丌") ⟫ʷ ≈ ⟪ (ℓ "丌书丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-TOFF301-X0 = derive (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌书丌") (ℓ "丌书丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为")
  (rw 32 q37 ∷
   rw 31 q38 ∷
   re 30 1 (ℓ "乏乣乏") ∷
   re 31 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 30 q39 ∷
   rw 33 q37 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q40 ∷
   rw 35 q37 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q40 ∷
   rw 37 q37 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q39 ∷
   rw⁻ 37 q41 ∷
   rw 38 q42 ∷
   rw 37 q41 ∷
   rw 36 q43 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q42 ∷
   rw 34 q40 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 35 q42 ∷
   rw 32 q40 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q42 ∷
   rw 30 q43 ∷
   rw 31 q44 ∷
   re 31 8 (ℓ "乣") ∷
   rw 29 q38 ∷
   rw 30 q45 ∷
   rw⁻ 29 q38 ∷
   rw 32 q37 ∷
   re 30 3 (ℓ "丱") ∷
   rw⁻ 31 q38 ∷
   rw 34 q37 ∷
   re 32 3 (ℓ "丿") ∷
   rw⁻ 33 q46 ∷
   rw 36 q37 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q37 ∷
   re 35 3 (ℓ "乀") ∷
   rw 38 q37 ∷
   re 36 3 (ℓ "丮") ∷
   rw 39 q37 ∷
   re 37 3 (ℓ "乀") ∷
   rw⁻ 38 q38 ∷
   rw 41 q37 ∷
   re 39 3 (ℓ "串") ∷
   rw⁻ 40 q38 ∷
   rw 41 q42 ∷
   rw 0 q47 ∷
   rw 12 q37 ∷
   rw 11 q38 ∷
   re 10 1 (ℓ "乏丬乏") ∷
   rw 12 q42 ∷
   rw 9 q38 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 10 q42 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q42 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q42 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q42 ∷
   rw 4 q46 ∷
   re 3 1 (ℓ "乏丸乏") ∷
   rw 5 q42 ∷
   rw 2 q38 ∷
   re 1 1 (ℓ "乏丫乏") ∷
   rw 3 q42 ∷
   rw 0 q38 ∷
   rw 1 q48 ∷
   rw⁻ 0 q38 ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 1 q39 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q40 ∷
   rw 6 q37 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q40 ∷
   rw 8 q37 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q39 ∷
   rw⁻ 8 q41 ∷
   rw 1 q37 ∷
   rw 2 q49 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q42 ∷
   rw⁻ 4 q40 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q42 ∷
   rw⁻ 6 q40 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q42 ∷
   rw 8 q49 ∷
   rw⁻ 9 q41 ∷
   rw 2 q44 ∷
   re 2 8 (ℓ "乣") ∷
   re 1 3 (ℓ "书") ∷
   rw⁻ 2 q38 ∷
   rw 3 q42 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = sE 1081 lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0

-- Bar(SSSKSS;0,3->2) passes factors of X0 CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12 X0: 1 steps
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : ⟪ (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") ⟫ʷ ≈ ⟪ (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义") ⟫ʷ
lem-Bar⟨SSSKSS03-⟶2⟩-passes-factors-of-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = derive (ℓ "丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌") (ℓ "丌丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丌丧丧丧丫丧丧丰义义义义义义乗业义义义义义义义义义丰义义义乗义义")
  (rw 0 q50 ∷ []) Eq.refl
