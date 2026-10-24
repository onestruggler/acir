{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD688 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D688 (W : Ws) (Sᴰ : SD688) where

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
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X2-X3 : St 1827
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X2-X3 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 : St 1828
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ : St 1829
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩ = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 : St 1830
  lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 30 W
  q7 : Eqn
  q7 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 122 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 127 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 74 W
  q15 : Eqn
  q15 = wE 337 W
  q16 : Eqn
  q16 = wE 1603 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 124 W
  q20 : Eqn
  q20 = sE 1828 lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-TOFF302-X2-X3
  q21 : Eqn
  q21 = wE 1604 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 TOFF302 X2 X3]: 135 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF302-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞乧丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞乧丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-TOFF302-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞乧丘丞") (ℓ "丘丞乧丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (ℓ "並乨並") ∷
   re 34 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q6 ∷
   rw 36 q7 ∷
   rw 37 q6 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q8 ∷
   rw 39 q9 ∷
   rw 40 q8 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q4 ∷
   rw 40 q10 ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   rw⁻ 39 q4 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q8 ∷
   rw 39 q13 ∷
   rw⁻ 38 q8 ∷
   re 39 3 (ℓ "丽") ∷
   rw 37 q14 ∷
   rw⁻ 36 q7 ∷
   rw 35 q14 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 33 q4 ∷
   rw 34 q15 ∷
   re 34 8 (ℓ "乨") ∷
   rw⁻ 32 q2 ∷
   rw⁻ 31 q3 ∷
   rw 32 q16 ∷
   rw 31 q3 ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q7 ∷
   rw 36 q6 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q8 ∷
   rw 38 q9 ∷
   rw 39 q8 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q4 ∷
   rw 39 q10 ∷
   rw 32 q1 ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q17 ∷
   rw 36 q7 ∷
   rw 37 q17 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q8 ∷
   rw 39 q18 ∷
   rw 40 q8 ∷
   re 38 3 (ℓ "丽") ∷
   rw 39 q4 ∷
   rw 40 q19 ∷
   rw 33 q15 ∷
   re 33 8 (ℓ "乨") ∷
   re 32 3 (ℓ "乧") ∷
   rw 33 q3 ∷
   rw 34 q11 ∷
   rw 0 q20 ∷
   rw 3 q1 ∷
   rw⁻ 2 q3 ∷
   re 1 1 (ℓ "並乨並") ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q4 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q8 ∷
   rw 7 q13 ∷
   rw⁻ 6 q8 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q14 ∷
   rw⁻ 4 q7 ∷
   rw 3 q14 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q4 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乨") ∷
   rw⁻ 0 q3 ∷
   rw 1 q21 ∷
   rw 0 q3 ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q7 ∷
   rw 6 q6 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 2 q1 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q17 ∷
   rw 6 q7 ∷
   rw 7 q17 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q8 ∷
   rw 9 q18 ∷
   rw 10 q8 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q4 ∷
   rw 10 q19 ∷
   rw 3 q15 ∷
   re 3 8 (ℓ "乨") ∷
   re 2 3 (ℓ "乧") ∷
   rw 3 q3 ∷
   rw 4 q2 ∷
   rw 5 q11 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 1902 W
  q23 : Eqn
  q23 = sE 1827 lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X2-X3
  q24 : Eqn
  q24 = wE 1903 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS12 CS12 CS12 CK21 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CK31 CS13 CS13 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丞") (ℓ "丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q22 ∷
   rw 0 q23 ∷
   rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 1587 W
  q26 : Eqn
  q26 = sE 1830 lem-Bar⟨SSSKSS21-⟶0⟩-passes-factors-of-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3
  q27 : Eqn
  q27 = wE 1588 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X2 X3]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X2-X3 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丞") (ℓ "丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丘丞丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 31 q25 ∷
   rw 0 q26 ∷
   rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 2022 W
  q29 : Eqn
  q29 = sE 1829 lem-Bar⟨SSKSKK23-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~20-⟶1⟩
  q30 : Eqn
  q30 = wE 2023 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘") (ℓ "丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q28 ∷
   rw 0 q29 ∷
   rw 0 q30 ∷ []) Eq.refl
