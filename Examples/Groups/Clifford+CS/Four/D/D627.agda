{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD627 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D627 (W : Ws) (Sᴰ : SD627) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~32-⟶1⟩ : St 1491
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~32-⟶1⟩ = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~32-⟶1⟩ : St 1492
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~32-⟶1⟩ = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-III-units-2 : St 1493
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-III-units-2 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-III-units-1 : St 1494
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-III-units-1 = pickᴰ 3 Sᴰ
  lem-pass-TOFF203-vs-X3-TOFF213-X3 : St 1495
  lem-pass-TOFF203-vs-X3-TOFF213-X3 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 1389 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
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
  q15 = wE 334 W
  q16 : Eqn
  q16 = wE 1888 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 124 W
  q20 : Eqn
  q20 = sE 1495 lem-pass-TOFF203-vs-X3-TOFF213-X3
  q21 : Eqn
  q21 = wE 1889 W
  q22 : Eqn
  q22 = wE 1392 W

-- pass [TOFF213] [X3 TOFF203 X3]: 133 steps
lem-pass-TOFF213-vs-X3-TOFF203-X3 : ⟪ (ℓ "乥丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-TOFF203-X3 = derive (ℓ "乥丞乤丞") (ℓ "丞乤丞乥")
  (rw 0 q1 ∷
   rw 8 q2 ∷
   rw⁻ 7 q3 ∷
   re 6 1 (ℓ "並乥並") ∷
   re 7 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q8 ∷
   rw 12 q9 ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q4 ∷
   rw 13 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q8 ∷
   rw 12 q13 ∷
   rw⁻ 11 q8 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q14 ∷
   rw⁻ 9 q7 ∷
   rw 8 q14 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 6 q4 ∷
   rw 7 q15 ∷
   re 7 8 (ℓ "乥") ∷
   rw⁻ 5 q3 ∷
   rw⁻ 4 q3 ∷
   rw 5 q16 ∷
   re 5 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q8 ∷
   rw 10 q9 ∷
   rw 11 q8 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q4 ∷
   rw 11 q10 ∷
   rw 4 q2 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q17 ∷
   rw 8 q7 ∷
   rw 9 q17 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q8 ∷
   rw 11 q18 ∷
   rw 12 q8 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q4 ∷
   rw 12 q19 ∷
   rw 5 q15 ∷
   re 5 8 (ℓ "乥") ∷
   re 4 3 (ℓ "乤") ∷
   rw 5 q3 ∷
   rw 6 q11 ∷
   rw⁻ 1 q20 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "並乥並") ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
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
   re 2 8 (ℓ "乥") ∷
   rw⁻ 0 q3 ∷
   rw 1 q21 ∷
   rw 0 q3 ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
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
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q17 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q8 ∷
   rw 8 q18 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q3 ∷
   rw 3 q3 ∷
   rw 4 q11 ∷
   rw 3 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1 W
  q24 : Eqn
  q24 = wE 173 W
  q25 : Eqn
  q25 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q26 : Eqn
  q26 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 3 W
  q29 : Eqn
  q29 = wE 196 W
  q30 : Eqn
  q30 = wE 1884 W
  q31 : Eqn
  q31 = wE 175 W
  q32 : Eqn
  q32 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q33 : Eqn
  q33 = wE 56 W
  q34 : Eqn
  q34 = sE 1494 lem-Bar⟨SSSKSS32-⟶0⟩-passes-III-units-1
  q35 : Eqn
  q35 = wE 1885 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 TOFF103 X3]: 155 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乡丞") (ℓ "丞乡丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q23 ∷
   rw 33 q24 ∷
   re 32 1 (ℓ "乏习乏") ∷
   re 33 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 32 q25 ∷
   rw 35 q23 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 34 q26 ∷
   rw 37 q23 ∷
   re 35 3 (ℓ "举") ∷
   rw⁻ 36 q26 ∷
   rw 39 q23 ∷
   re 37 3 (ℓ "中") ∷
   rw⁻ 38 q25 ∷
   rw⁻ 39 q27 ∷
   rw 40 q28 ∷
   rw 39 q27 ∷
   rw 38 q25 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q28 ∷
   rw 36 q26 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 37 q28 ∷
   rw 34 q26 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 35 q28 ∷
   rw 32 q25 ∷
   rw 33 q29 ∷
   re 33 8 (ℓ "习") ∷
   rw 31 q24 ∷
   rw 32 q30 ∷
   rw 31 q31 ∷
   rw 34 q23 ∷
   re 32 3 (ℓ "乔") ∷
   rw 33 q31 ∷
   rw 34 q31 ∷
   rw 37 q23 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q31 ∷
   rw 37 q31 ∷
   re 39 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 38 q32 ∷
   rw 41 q23 ∷
   re 39 3 (ℓ "丽") ∷
   rw⁻ 40 q26 ∷
   rw 43 q23 ∷
   re 41 3 (ℓ "举") ∷
   rw⁻ 42 q26 ∷
   rw 45 q23 ∷
   re 43 3 (ℓ "中") ∷
   rw⁻ 44 q32 ∷
   rw⁻ 45 q27 ∷
   rw 38 q23 ∷
   rw⁻ 39 q32 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q28 ∷
   rw⁻ 41 q26 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q28 ∷
   rw⁻ 43 q26 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q28 ∷
   rw⁻ 45 q32 ∷
   rw⁻ 46 q27 ∷
   rw 39 q33 ∷
   re 39 8 (ℓ "九") ∷
   re 38 3 (ℓ "乞") ∷
   rw 39 q31 ∷
   rw 40 q31 ∷
   rw 43 q23 ∷
   re 41 3 (ℓ "乒") ∷
   rw 42 q31 ∷
   rw 43 q31 ∷
   rw 46 q23 ∷
   re 44 3 (ℓ "乕") ∷
   rw 45 q31 ∷
   rw 46 q28 ∷
   rw 0 q34 ∷
   rw 15 q23 ∷
   rw 14 q24 ∷
   re 13 1 (ℓ "乏么乏") ∷
   rw 15 q28 ∷
   rw 12 q24 ∷
   rw 11 q24 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q28 ∷
   rw 9 q24 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q32 ∷
   rw 10 q23 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q26 ∷
   rw 12 q23 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q26 ∷
   rw 14 q23 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q32 ∷
   rw⁻ 14 q27 ∷
   rw 15 q28 ∷
   rw 14 q27 ∷
   rw 13 q32 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q28 ∷
   rw 11 q26 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q28 ∷
   rw 9 q26 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q28 ∷
   rw 7 q32 ∷
   rw 8 q33 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q24 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q28 ∷
   rw 3 q24 ∷
   rw 2 q24 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q28 ∷
   rw 0 q24 ∷
   rw 1 q35 ∷
   rw 0 q31 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q25 ∷
   rw 4 q23 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q23 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q23 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q23 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q31 ∷
   rw 3 q28 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1886 W
  q37 : Eqn
  q37 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q38 : Eqn
  q38 = wE 142 W
  q39 : Eqn
  q39 = wE 121 W
  q40 : Eqn
  q40 = wE 123 W
  q41 : Eqn
  q41 = wE 125 W
  q42 : Eqn
  q42 = wE 139 W
  q43 : Eqn
  q43 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q44 : Eqn
  q44 = sE 1493 lem-Bar⟨SSKSKK31-⟶0⟩-passes-III-units-2
  q45 : Eqn
  q45 = wE 137 W
  q46 : Eqn
  q46 = wE 118 W
  q47 : Eqn
  q47 = wE 140 W
  q48 : Eqn
  q48 = wE 1887 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF203 X3]: 171 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乤丞") (ℓ "丞乤丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "並乥並") ∷
   re 31 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw 33 q7 ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q8 ∷
   rw 36 q9 ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q4 ∷
   rw 37 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q8 ∷
   rw 36 q13 ∷
   rw⁻ 35 q8 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q14 ∷
   rw⁻ 33 q7 ∷
   rw 32 q14 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 30 q4 ∷
   rw 31 q15 ∷
   re 31 8 (ℓ "乥") ∷
   rw⁻ 29 q3 ∷
   rw 30 q36 ∷
   rw 29 q3 ∷
   rw 30 q37 ∷
   rw 31 q3 ∷
   rw 32 q3 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q8 ∷
   rw 34 q38 ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q3 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 36 q39 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q7 ∷
   rw 40 q6 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q8 ∷
   rw 42 q9 ∷
   rw 43 q8 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q39 ∷
   rw 43 q10 ∷
   rw 36 q2 ∷
   rw 37 q40 ∷
   rw 38 q5 ∷
   rw 39 q17 ∷
   rw 40 q7 ∷
   rw 41 q17 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q8 ∷
   rw 43 q18 ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "丽") ∷
   rw 43 q40 ∷
   rw 44 q19 ∷
   rw 37 q41 ∷
   re 37 8 (ℓ "乢") ∷
   re 36 3 (ℓ "也") ∷
   rw 37 q3 ∷
   rw 38 q3 ∷
   re 40 1 (ℓ "乏么乏") ∷
   rw 39 q8 ∷
   rw 40 q42 ∷
   rw 41 q8 ∷
   re 39 3 (ℓ "乒") ∷
   rw 40 q3 ∷
   rw 41 q3 ∷
   rw 42 q43 ∷
   rw 43 q3 ∷
   rw 44 q11 ∷
   rw 0 q44 ∷
   rw 15 q2 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 13 q43 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw⁻ 12 q8 ∷
   rw 11 q45 ∷
   rw⁻ 10 q8 ∷
   re 11 3 (ℓ "乕") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 8 q3 ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q39 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q39 ∷
   rw 14 q10 ∷
   rw 15 q11 ∷
   rw 14 q12 ∷
   rw 13 q46 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q8 ∷
   rw 13 q13 ∷
   rw⁻ 12 q8 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q14 ∷
   rw⁻ 10 q7 ∷
   rw 9 q14 ∷
   rw⁻ 8 q5 ∷
   rw 7 q46 ∷
   rw 8 q41 ∷
   re 8 8 (ℓ "乢") ∷
   rw⁻ 6 q3 ∷
   rw⁻ 5 q3 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q8 ∷
   rw 5 q47 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (ℓ "乔") ∷
   rw⁻ 3 q3 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 1 q37 ∷
   rw⁻ 0 q3 ∷
   rw 1 q48 ∷
   rw 0 q3 ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
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
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q17 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q8 ∷
   rw 8 q18 ∷
   rw 9 q8 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q3 ∷
   rw 3 q11 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1890 W
  q50 : Eqn
  q50 = sE 1492 lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~32-⟶1⟩
  q51 : Eqn
  q51 = wE 1891 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q49 ∷
   rw 0 q50 ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 1892 W
  q53 : Eqn
  q53 = sE 1491 lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~32-⟶1⟩
  q54 : Eqn
  q54 = wE 1893 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q52 ∷
   rw 0 q53 ∷
   rw 0 q54 ∷ []) Eq.refl
