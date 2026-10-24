{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD587 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D587 (W : Ws) (Sᴰ : SD587) where

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
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3 : St 1026
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : St 1027
  lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 : St 1028
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ : St 1029
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 : St 1030
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3 = pickᴰ 4 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ : St 1031
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩ = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = wE 1656 W
  q2 : Eqn
  q2 = sE 1029 lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩
  q3 : Eqn
  q3 = wE 1657 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 S1 S1 S1 CK10 S1 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-S1-S1-S1-CK10-S1-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-S1-S1-S1-CK10-S1-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = wE 1106 W
  q8 : Eqn
  q8 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = wE 30 W
  q11 : Eqn
  q11 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q12 : Eqn
  q12 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 122 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = wE 127 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 74 W
  q19 : Eqn
  q19 = wE 337 W
  q20 : Eqn
  q20 = wE 1658 W
  q21 : Eqn
  q21 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q22 : Eqn
  q22 = wE 24 W
  q23 : Eqn
  q23 = wE 25 W
  q24 : Eqn
  q24 = wE 124 W
  q25 : Eqn
  q25 = sE 1028 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3
  q26 : Eqn
  q26 = wE 1659 W
  q27 : Eqn
  q27 = wE 317 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 TOFF302 X0 X2 X3]: 145 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞乧丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞乧丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF302-X0-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丘丞乧丌丘丞") (ℓ "丌丘丞乧丌丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 34 q6 ∷
   rw 33 q7 ∷
   re 32 1 (ℓ "並乨並") ∷
   re 33 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 32 q8 ∷
   rw 33 q9 ∷
   rw 34 q10 ∷
   rw 35 q11 ∷
   rw 36 q10 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q12 ∷
   rw 38 q13 ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q8 ∷
   rw 39 q14 ∷
   rw 40 q15 ∷
   rw 39 q16 ∷
   rw⁻ 38 q8 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q12 ∷
   rw 38 q17 ∷
   rw⁻ 37 q12 ∷
   re 38 3 (ℓ "丽") ∷
   rw 36 q18 ∷
   rw⁻ 35 q11 ∷
   rw 34 q18 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q8 ∷
   rw 33 q19 ∷
   re 33 8 (ℓ "乨") ∷
   rw⁻ 31 q5 ∷
   rw⁻ 30 q6 ∷
   rw 29 q7 ∷
   rw 30 q20 ∷
   rw 29 q6 ∷
   rw 30 q21 ∷
   rw 31 q6 ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 33 q8 ∷
   rw 34 q9 ∷
   rw 35 q10 ∷
   rw 36 q11 ∷
   rw 37 q10 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q12 ∷
   rw 39 q13 ∷
   rw 40 q12 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q8 ∷
   rw 40 q14 ∷
   rw 33 q4 ∷
   rw 34 q8 ∷
   rw 35 q9 ∷
   rw 36 q22 ∷
   rw 37 q11 ∷
   rw 38 q22 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q12 ∷
   rw 40 q23 ∷
   rw 41 q12 ∷
   re 39 3 (ℓ "丽") ∷
   rw 40 q8 ∷
   rw 41 q24 ∷
   rw 34 q19 ∷
   re 34 8 (ℓ "乨") ∷
   re 33 3 (ℓ "乧") ∷
   rw 34 q6 ∷
   rw 35 q15 ∷
   rw 0 q25 ∷
   rw 6 q4 ∷
   rw⁻ 5 q6 ∷
   re 4 1 (ℓ "並乨並") ∷
   re 5 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q11 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q12 ∷
   rw 10 q13 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q8 ∷
   rw 11 q14 ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q8 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q12 ∷
   rw 10 q17 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw⁻ 7 q11 ∷
   rw 6 q18 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q8 ∷
   rw 5 q19 ∷
   re 5 8 (ℓ "乨") ∷
   rw⁻ 3 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 1 q21 ∷
   rw⁻ 0 q6 ∷
   rw 1 q26 ∷
   rw 0 q27 ∷
   rw 1 q6 ∷
   rw 2 q5 ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q8 ∷
   rw 10 q14 ∷
   rw 3 q4 ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q12 ∷
   rw 10 q23 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q8 ∷
   rw 11 q24 ∷
   rw 4 q19 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   rw 7 q15 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 1591 W
  q29 : Eqn
  q29 = sE 1026 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3
  q30 : Eqn
  q30 = wE 1592 W

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01] [X2 TOFF123 X2]: 3 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-TOFF123-X2 : ⟪ (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠") ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-TOFF123-X2 = derive (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乢丘") (ℓ "丘乢丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠")
  (rw 74 q28 ∷
   rw 0 q29 ∷
   rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 1031 lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 S1 S1 S1 CK10 S1 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-S1-S1-S1-CK10-S1-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-S1-S1-S1-CK10-S1-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与乆临与临与丠丠丠临与丠丠丠丠丠丠丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q1 ∷
   rw 0 q31 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1030 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X2-X3-TOFF302-X0-X2-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X2 X3 TOFF302 X0 X2 X3]: 145 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞乧丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞乧丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF302-X0-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丘丞乧丌丘丞") (ℓ "丌丘丞乧丌丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   rw⁻ 36 q6 ∷
   rw 35 q7 ∷
   re 34 1 (ℓ "並乨並") ∷
   re 35 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 34 q8 ∷
   rw 35 q9 ∷
   rw 36 q10 ∷
   rw 37 q11 ∷
   rw 38 q10 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q12 ∷
   rw 40 q13 ∷
   rw 41 q12 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q8 ∷
   rw 41 q14 ∷
   rw 42 q15 ∷
   rw 41 q16 ∷
   rw⁻ 40 q8 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q12 ∷
   rw 40 q17 ∷
   rw⁻ 39 q12 ∷
   re 40 3 (ℓ "丽") ∷
   rw 38 q18 ∷
   rw⁻ 37 q11 ∷
   rw 36 q18 ∷
   rw⁻ 35 q9 ∷
   rw⁻ 34 q8 ∷
   rw 35 q19 ∷
   re 35 8 (ℓ "乨") ∷
   rw⁻ 33 q5 ∷
   rw⁻ 32 q6 ∷
   rw 31 q7 ∷
   rw 32 q20 ∷
   rw 31 q6 ∷
   rw 32 q21 ∷
   rw 33 q6 ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 35 q8 ∷
   rw 36 q9 ∷
   rw 37 q10 ∷
   rw 38 q11 ∷
   rw 39 q10 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q12 ∷
   rw 41 q13 ∷
   rw 42 q12 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q8 ∷
   rw 42 q14 ∷
   rw 35 q4 ∷
   rw 36 q8 ∷
   rw 37 q9 ∷
   rw 38 q22 ∷
   rw 39 q11 ∷
   rw 40 q22 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q12 ∷
   rw 42 q23 ∷
   rw 43 q12 ∷
   re 41 3 (ℓ "丽") ∷
   rw 42 q8 ∷
   rw 43 q24 ∷
   rw 36 q19 ∷
   re 36 8 (ℓ "乨") ∷
   re 35 3 (ℓ "乧") ∷
   rw 36 q6 ∷
   rw 37 q15 ∷
   rw 0 q32 ∷
   rw 6 q4 ∷
   rw⁻ 5 q6 ∷
   re 4 1 (ℓ "並乨並") ∷
   re 5 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q11 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q12 ∷
   rw 10 q13 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q8 ∷
   rw 11 q14 ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q8 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q12 ∷
   rw 10 q17 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw⁻ 7 q11 ∷
   rw 6 q18 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q8 ∷
   rw 5 q19 ∷
   re 5 8 (ℓ "乨") ∷
   rw⁻ 3 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 1 q21 ∷
   rw⁻ 0 q6 ∷
   rw 1 q26 ∷
   rw 0 q27 ∷
   rw 1 q6 ∷
   rw 2 q5 ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q8 ∷
   rw 10 q14 ∷
   rw 3 q4 ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q22 ∷
   rw 7 q11 ∷
   rw 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q12 ∷
   rw 10 q23 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q8 ∷
   rw 11 q24 ∷
   rw 4 q19 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 4 q27 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   rw 7 q15 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1660 W
  q34 : Eqn
  q34 = sE 1027 lem-Bar⟨SSKSKK21-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2
  q35 : Eqn
  q35 = wE 1661 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 29 q33 ∷
   rw 0 q34 ∷
   rw 0 q35 ∷ []) Eq.refl
