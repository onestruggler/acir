{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD639 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D639 (W : Ws) (Sᴰ : SD639) where

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
  lem-pass-X0-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X3-vs-X1-TOFF312-X1 : St 1542
  lem-pass-X0-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X3-vs-X1-TOFF312-X1 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 : St 1543
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : St 1544
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 : St 1545
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = wE 1800 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = wE 1928 W
  q11 : Eqn
  q11 = wE 175 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = sE 1542 lem-pass-X0-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X3-vs-X1-TOFF312-X1
  q14 : Eqn
  q14 = wE 1929 W
  q15 : Eqn
  q15 = wE 1803 W

-- pass [TOFF312] [X0 X1 X3 CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30 X0 X1 X3]: 229 steps
lem-pass-TOFF312-vs-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 : ⟪ (ℓ "乨丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 = derive (ℓ "乨丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞") (ℓ "丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞乨")
  (rw 0 q1 ∷
   rw 40 q2 ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q6 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q6 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q6 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q6 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q6 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q6 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   rw 23 q7 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw 24 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   rw 18 q7 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q6 ∷
   rw 16 q7 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q6 ∷
   re 14 1 (ℓ "乏丹乏") ∷
   rw 16 q6 ∷
   rw 13 q8 ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q9 ∷
   rw 7 q3 ∷
   rw 6 q4 ∷
   rw 5 q5 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw⁻ 4 q5 ∷
   rw 5 q11 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 7 q9 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q9 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 11 q8 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乀") ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q12 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q12 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q12 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乀") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乑") ∷
   rw⁻ 35 q5 ∷
   rw 36 q11 ∷
   rw⁻ 37 q4 ∷
   rw 38 q6 ∷
   rw⁻ 1 q13 ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q5 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q6 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q6 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   rw 18 q7 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q6 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   rw 13 q7 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q6 ∷
   rw 11 q7 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q6 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q6 ∷
   rw 8 q8 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q9 ∷
   rw 3 q9 ∷
   rw 2 q3 ∷
   rw 1 q5 ∷
   rw 0 q4 ∷
   rw 1 q14 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q4 ∷
   rw 2 q11 ∷
   rw⁻ 3 q9 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 5 q8 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q8 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q12 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q12 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q12 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乑") ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q4 ∷
   rw 34 q11 ∷
   rw⁻ 35 q4 ∷
   rw 36 q6 ∷
   rw 35 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1650 W
  q17 : Eqn
  q17 = sE 1544 lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2
  q18 : Eqn
  q18 = wE 1651 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X1 X2]: 3 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘") (ℓ "丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q16 ∷
   rw 0 q17 ∷
   rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1926 W
  q20 : Eqn
  q20 = sE 1545 lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3
  q21 : Eqn
  q21 = wE 1927 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 TOFF312 X1 X2 X3]: 3 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-TOFF312-X1-X2-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞乨丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞乨丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-TOFF312-X1-X2-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞乨丒丘丞") (ℓ "丒丘丞乨丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q19 ∷
   rw 0 q20 ∷
   rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 1543 lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 X2 X3 TOFF312 X1 X2 X3]: 3 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-TOFF312-X1-X2-X3 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丘丞乨丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞乨丒丘丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-X2-X3-TOFF312-X1-X2-X3 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丘丞乨丒丘丞") (ℓ "丒丘丞乨丒丘丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 29 q19 ∷
   rw 0 q22 ∷
   rw 0 q21 ∷ []) Eq.refl
