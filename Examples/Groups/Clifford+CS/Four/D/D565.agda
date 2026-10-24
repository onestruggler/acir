{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD565 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D565 (W : Ws) (Sᴰ : SD565) where

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
  lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 : St 983
  lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 : St 984
  lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : St 985
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ : St 986
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩ = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩ : St 987
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩ = pickᴰ 4 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 : St 988
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 = pickᴰ 5 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩ : St 989
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩ = pickᴰ 6 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1 : St 990
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 7 Sᴰ
  lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 : St 991
  lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2 = pickᴰ 8 Sᴰ
  lem-pass-CS12-CS12-CK21-CS12-vs-X2-TOFF312-X2 : St 992
  lem-pass-CS12-CS12-CK21-CS12-vs-X2-TOFF312-X2 = pickᴰ 9 Sᴰ
  lem-pass-CSd12-CKd21-CS12-CS12-vs-X2-TOFF312-X2 : St 993
  lem-pass-CSd12-CKd21-CS12-CS12-vs-X2-TOFF312-X2 = pickᴰ 10 Sᴰ

private
  q1 : Eqn
  q1 = wE 1624 W
  q2 : Eqn
  q2 = sE 991 lem-pass-CK21-CS12-CS12-CKd21-vs-X2-TOFF312-X2
  q3 : Eqn
  q3 = sE 984 lem-pass-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2
  q4 : Eqn
  q4 = sE 992 lem-pass-CS12-CS12-CK21-CS12-vs-X2-TOFF312-X2
  q5 : Eqn
  q5 = wE 1625 W

-- pass [X1 X3 CS12 CS12 CS12 CK21 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CK31 CS13 CS13 X1 X3] [X2 TOFF312 X2]: 6 steps
lem-pass-X1-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X3-vs-X2-TOFF312-X2 : ⟪ (ℓ "丒丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丞丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丒丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丞") ⟫ʷ
lem-pass-X1-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X3-vs-X2-TOFF312-X2 = derive (ℓ "丒丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丞丘乨丘") (ℓ "丘乨丘丒丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丞")
  (rw 0 q1 ∷
   rw 94 q2 ∷
   rw 8 q3 ∷
   rw 4 q4 ∷
   rw 0 q2 ∷
   rw 3 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1626 W
  q7 : Eqn
  q7 = sE 983 lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-vs-X2-TOFF312-X2
  q8 : Eqn
  q8 = sE 993 lem-pass-CSd12-CKd21-CS12-CS12-vs-X2-TOFF312-X2
  q9 : Eqn
  q9 = wE 1627 W

-- pass [X1 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X1 X3] [X2 TOFF312 X2]: 6 steps
lem-pass-X1-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X3-vs-X2-TOFF312-X2 : ⟪ (ℓ "丒丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丞丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丒丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丞") ⟫ʷ
lem-pass-X1-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X3-vs-X2-TOFF312-X2 = derive (ℓ "丒丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丞丘乨丘") (ℓ "丘乨丘丒丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丞")
  (rw 0 q6 ∷
   rw 82 q2 ∷
   rw 8 q7 ∷
   rw 4 q8 ∷
   rw 0 q2 ∷
   rw 3 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1567 W
  q11 : Eqn
  q11 = sE 990 lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1
  q12 : Eqn
  q12 = wE 1568 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 TOFF012 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF012-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF012-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘九丘") (ℓ "丘九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q10 ∷
   rw 0 q11 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1569 W
  q14 : Eqn
  q14 = sE 989 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩
  q15 : Eqn
  q15 = wE 1570 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘") (ℓ "丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q13 ∷
   rw 0 q14 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q19 : Eqn
  q19 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q21 : Eqn
  q21 = wE 30 W
  q22 : Eqn
  q22 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q23 : Eqn
  q23 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 122 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = wE 127 W
  q28 : Eqn
  q28 = wE 7 W
  q29 : Eqn
  q29 = wE 74 W
  q30 : Eqn
  q30 = wE 337 W
  q31 : Eqn
  q31 = wE 1603 W
  q32 : Eqn
  q32 = wE 24 W
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W
  q35 : Eqn
  q35 = sE 988 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3
  q36 : Eqn
  q36 = wE 1604 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 TOFF302 X2 X3]: 135 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF302-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞乧丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞乧丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF302-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞乧丘丞") (ℓ "丘丞乧丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 36 q16 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 34 q18 ∷
   re 33 1 (ℓ "並乨並") ∷
   re 34 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 33 q19 ∷
   rw 34 q20 ∷
   rw 35 q21 ∷
   rw 36 q22 ∷
   rw 37 q21 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q23 ∷
   rw 39 q24 ∷
   rw 40 q23 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q19 ∷
   rw 40 q25 ∷
   rw 41 q26 ∷
   rw 40 q27 ∷
   rw⁻ 39 q19 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q23 ∷
   rw 39 q28 ∷
   rw⁻ 38 q23 ∷
   re 39 3 (ℓ "丽") ∷
   rw 37 q29 ∷
   rw⁻ 36 q22 ∷
   rw 35 q29 ∷
   rw⁻ 34 q20 ∷
   rw⁻ 33 q19 ∷
   rw 34 q30 ∷
   re 34 8 (ℓ "乨") ∷
   rw⁻ 32 q17 ∷
   rw⁻ 31 q18 ∷
   rw 32 q31 ∷
   rw 31 q18 ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q19 ∷
   rw 33 q20 ∷
   rw 34 q21 ∷
   rw 35 q22 ∷
   rw 36 q21 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q23 ∷
   rw 38 q24 ∷
   rw 39 q23 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q19 ∷
   rw 39 q25 ∷
   rw 32 q16 ∷
   rw 33 q19 ∷
   rw 34 q20 ∷
   rw 35 q32 ∷
   rw 36 q22 ∷
   rw 37 q32 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q23 ∷
   rw 39 q33 ∷
   rw 40 q23 ∷
   re 38 3 (ℓ "丽") ∷
   rw 39 q19 ∷
   rw 40 q34 ∷
   rw 33 q30 ∷
   re 33 8 (ℓ "乨") ∷
   re 32 3 (ℓ "乧") ∷
   rw 33 q18 ∷
   rw 34 q26 ∷
   rw 0 q35 ∷
   rw 3 q16 ∷
   rw⁻ 2 q18 ∷
   re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q21 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 8 q23 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q19 ∷
   rw 8 q25 ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   rw⁻ 7 q19 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q23 ∷
   rw 7 q28 ∷
   rw⁻ 6 q23 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q29 ∷
   rw⁻ 4 q22 ∷
   rw 3 q29 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   rw 2 q30 ∷
   re 2 8 (ℓ "乨") ∷
   rw⁻ 0 q18 ∷
   rw 1 q36 ∷
   rw 0 q18 ∷
   rw 1 q17 ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q21 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q23 ∷
   rw 8 q24 ∷
   rw 9 q23 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q19 ∷
   rw 9 q25 ∷
   rw 2 q16 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q32 ∷
   rw 6 q22 ∷
   rw 7 q32 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q23 ∷
   rw 9 q33 ∷
   rw 10 q23 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q19 ∷
   rw 10 q34 ∷
   rw 3 q30 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 3 q18 ∷
   rw 4 q17 ∷
   rw 5 q26 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1605 W
  q38 : Eqn
  q38 = sE 987 lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨SSSSSSKiSSSSSSSSS~23-⟶1⟩
  q39 : Eqn
  q39 = wE 1606 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘") (ℓ "丘丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q37 ∷
   rw 0 q38 ∷
   rw 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1607 W
  q41 : Eqn
  q41 = sE 986 lem-Bar⟨SSSKSS23-⟶0⟩-passes-comm-WBar⟨KiKiSSSKiSSSSSS~23-⟶1⟩
  q42 : Eqn
  q42 = wE 1608 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 S3 S3 S3 CK31 S3 S3 S3 S3 CK31 S3 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘") (ℓ "丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q40 ∷
   rw 0 q41 ∷
   rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 1628 W
  q44 : Eqn
  q44 = sE 985 lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2
  q45 : Eqn
  q45 = wE 1629 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q43 ∷
   rw 0 q44 ∷
   rw 0 q45 ∷ []) Eq.refl
