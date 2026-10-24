{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD635 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D635 (W : Ws) (Sᴰ : SD635) where

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
  lem-pass-TOFF302-vs-X2-TOFF312-X2 : St 1510
  lem-pass-TOFF302-vs-X2-TOFF312-X2 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-III-units-1 : St 1528
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-III-units-1 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 : St 1529
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : St 1530
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 : St 1531
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
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
  q15 = wE 1916 W
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 124 W
  q19 : Eqn
  q19 = sE 1510 lem-pass-TOFF302-vs-X2-TOFF312-X2
  q20 : Eqn
  q20 = wE 1917 W

-- pass [X3 TOFF302 X3] [X2 TOFF312 X2]: 127 steps
lem-pass-X3-TOFF302-X3-vs-X2-TOFF312-X2 : ⟪ (ℓ "丞乧丞丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丞乧丞") ⟫ʷ
lem-pass-X3-TOFF302-X3-vs-X2-TOFF312-X2 = derive (ℓ "丞乧丞丘乨丘") (ℓ "丘乨丘丞乧丞")
  (rw 3 q1 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (ℓ "並乨並") ∷
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
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q12 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q13 ∷
   rw⁻ 4 q6 ∷
   rw 3 q13 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 1 q3 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乨") ∷
   rw⁻ 0 q2 ∷
   rw 1 q15 ∷
   re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q3 ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 7 q7 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 0 q1 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q16 ∷
   rw 4 q6 ∷
   rw 5 q16 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 7 q17 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q3 ∷
   rw 8 q18 ∷
   rw 1 q14 ∷
   re 1 8 (ℓ "乨") ∷
   re 0 3 (ℓ "乧") ∷
   rw 1 q10 ∷
   rw 0 q19 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "並乨並") ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q7 ∷
   rw 9 q12 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q6 ∷
   rw 5 q13 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 3 q3 ∷
   rw 4 q14 ∷
   re 4 8 (ℓ "乨") ∷
   rw 4 q20 ∷
   rw 3 q2 ∷
   re 5 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q5 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q3 ∷
   rw 11 q9 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q16 ∷
   rw 8 q6 ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   rw 11 q17 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q3 ∷
   rw 12 q18 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "乨") ∷
   re 4 3 (ℓ "乧") ∷
   rw 5 q2 ∷
   rw 6 q10 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1884 W
  q22 : Eqn
  q22 = sE 1528 lem-Bar⟨SSSKSS23-⟶0⟩-passes-III-units-1
  q23 : Eqn
  q23 = wE 1885 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 TOFF102 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘习丘") (ℓ "丘习丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q21 ∷
   rw 0 q22 ∷
   rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1912 W
  q25 : Eqn
  q25 = sE 1529 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3
  q26 : Eqn
  q26 = wE 1913 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 CS12 CS12 CS12 CK21 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CK31 CS13 CS13 X1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞") (ℓ "丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q24 ∷
   rw 0 q25 ∷
   rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1914 W
  q28 : Eqn
  q28 = sE 1531 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3
  q29 : Eqn
  q29 = wE 1915 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") (ℓ "丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q27 ∷
   rw 0 q28 ∷
   rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 1 W
  q31 : Eqn
  q31 = wE 173 W
  q32 : Eqn
  q32 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q34 : Eqn
  q34 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q35 : Eqn
  q35 = wE 3 W
  q36 : Eqn
  q36 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q37 : Eqn
  q37 = wE 1634 W
  q38 : Eqn
  q38 = wE 175 W
  q39 : Eqn
  q39 = sE 1530 lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3
  q40 : Eqn
  q40 = wE 1635 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X0 X3]: 207 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞") (ℓ "丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 62 q30 ∷
   rw 61 q31 ∷
   rw 60 q32 ∷
   rw 59 q33 ∷
   rw 58 q33 ∷
   rw 57 q34 ∷
   rw 56 q33 ∷
   rw 55 q34 ∷
   rw 54 q34 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q35 ∷
   rw 52 q34 ∷
   rw 51 q34 ∷
   rw 50 q34 ∷
   rw 49 q34 ∷
   rw 48 q34 ∷
   rw 47 q34 ∷
   rw 46 q36 ∷
   rw 45 q33 ∷
   rw 44 q34 ∷
   rw 43 q34 ∷
   rw 42 q34 ∷
   rw 41 q36 ∷
   rw 40 q33 ∷
   rw 39 q36 ∷
   rw 38 q33 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 39 q35 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q35 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q35 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q35 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q35 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q35 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q35 ∷
   rw 30 q31 ∷
   rw 29 q32 ∷
   rw 30 q37 ∷
   rw 29 q38 ∷
   rw 32 q30 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q30 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q30 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q30 ∷
   re 33 3 (ℓ "乒") ∷
   rw 34 q38 ∷
   rw 35 q38 ∷
   rw 38 q30 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q30 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q30 ∷
   re 38 3 (ℓ "乑") ∷
   rw 41 q30 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q30 ∷
   re 40 3 (ℓ "乑") ∷
   rw 43 q30 ∷
   re 41 3 (ℓ "乑") ∷
   rw 44 q30 ∷
   re 42 3 (ℓ "乓") ∷
   rw⁻ 43 q33 ∷
   rw⁻ 44 q36 ∷
   rw⁻ 45 q33 ∷
   rw⁻ 46 q36 ∷
   rw⁻ 47 q34 ∷
   rw⁻ 48 q34 ∷
   rw⁻ 49 q34 ∷
   rw⁻ 50 q33 ∷
   rw⁻ 51 q36 ∷
   rw⁻ 52 q34 ∷
   rw⁻ 53 q34 ∷
   rw⁻ 54 q34 ∷
   rw⁻ 55 q34 ∷
   rw⁻ 56 q34 ∷
   rw⁻ 57 q34 ∷
   rw 60 q30 ∷
   re 58 3 (ℓ "乓") ∷
   rw⁻ 59 q34 ∷
   rw⁻ 60 q34 ∷
   rw⁻ 61 q33 ∷
   rw⁻ 62 q34 ∷
   rw⁻ 63 q33 ∷
   rw⁻ 64 q33 ∷
   rw 65 q38 ∷
   rw 66 q38 ∷
   rw 69 q30 ∷
   re 67 3 (ℓ "乑") ∷
   rw 70 q30 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q30 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q30 ∷
   re 70 3 (ℓ "乒") ∷
   rw 71 q38 ∷
   rw 72 q35 ∷
   rw 0 q39 ∷
   rw 43 q30 ∷
   rw 42 q31 ∷
   re 41 1 (ℓ "乏久乏") ∷
   rw 43 q35 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q35 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q35 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q35 ∷
   rw 37 q31 ∷
   rw 36 q31 ∷
   rw 35 q33 ∷
   rw 34 q33 ∷
   rw 33 q34 ∷
   rw 32 q33 ∷
   rw 31 q34 ∷
   rw 30 q34 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q35 ∷
   rw 28 q34 ∷
   rw 27 q34 ∷
   rw 26 q34 ∷
   rw 25 q34 ∷
   rw 24 q34 ∷
   rw 23 q34 ∷
   rw 22 q36 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q34 ∷
   rw 18 q34 ∷
   rw 17 q36 ∷
   rw 16 q33 ∷
   rw 15 q36 ∷
   rw 14 q33 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 15 q35 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q35 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q35 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q35 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q35 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q35 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q35 ∷
   rw 6 q31 ∷
   rw 5 q31 ∷
   re 4 1 (ℓ "乏久乏") ∷
   rw 6 q35 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q35 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q35 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw 3 q35 ∷
   rw 0 q31 ∷
   rw 1 q40 ∷
   rw⁻ 0 q32 ∷
   rw 1 q38 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q30 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q30 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 9 q33 ∷
   rw⁻ 10 q36 ∷
   rw⁻ 11 q33 ∷
   rw⁻ 12 q36 ∷
   rw⁻ 13 q34 ∷
   rw⁻ 14 q34 ∷
   rw⁻ 15 q34 ∷
   rw⁻ 16 q33 ∷
   rw⁻ 17 q36 ∷
   rw⁻ 18 q34 ∷
   rw⁻ 19 q34 ∷
   rw⁻ 20 q34 ∷
   rw⁻ 21 q34 ∷
   rw⁻ 22 q34 ∷
   rw⁻ 23 q34 ∷
   rw 26 q30 ∷
   re 24 3 (ℓ "乓") ∷
   rw⁻ 25 q34 ∷
   rw⁻ 26 q34 ∷
   rw⁻ 27 q33 ∷
   rw⁻ 28 q34 ∷
   rw⁻ 29 q33 ∷
   rw⁻ 30 q33 ∷
   rw⁻ 31 q32 ∷
   rw 32 q38 ∷
   rw 33 q35 ∷ []) Eq.refl
