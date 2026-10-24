{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD008 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D008 (Sᴰ : SD008) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CZ12-CCZ034 : Ws → St 65
  lem-comm-CZ12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CZ13-CCZ024 : Ws → St 67
  lem-comm-CZ13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CZ23-CCZ014 : Ws → St 69
  lem-comm-CZ23-CCZ014 = pickᴰ 2 Sᴰ
  lem-comm-CZ03-CCZ124 : Ws → St 78
  lem-comm-CZ03-CCZ124 = pickᴰ 3 Sᴰ
  lem-comm-CZ02-CCZ134 : Ws → St 134
  lem-comm-CZ02-CCZ134 = pickᴰ 4 Sᴰ
  lem-comm-CZ23-TOFF401 : Ws → St 175
  lem-comm-CZ23-TOFF401 = pickᴰ 5 Sᴰ
  lem-box-tQ-at0410213243 : Ws → St 139
  lem-box-tQ-at0410213243 = pickᴰ 6 Sᴰ
  lem-box-tQ-at04203243 : Ws → St 84
  lem-box-tQ-at04203243 = pickᴰ 7 Sᴰ
  lem-tP-at0410213243 : Ws → St 128
  lem-tP-at0410213243 = pickᴰ 8 Sᴰ
  lem-tP-at04203243 : Ws → St 129
  lem-tP-at04203243 = pickᴰ 9 Sᴰ
  lem-cQ-at02142140 : Ws → St 176
  lem-cQ-at02142140 = pickᴰ 10 Sᴰ
  lem-cQ-at0410233142 : Ws → St 177
  lem-cQ-at0410233142 = pickᴰ 11 Sᴰ
  lem-cQ-at0410233241 : Ws → St 178
  lem-cQ-at0410233241 = pickᴰ 12 Sᴰ
  lem-cQ-at041041 : Ws → St 179
  lem-cQ-at041041 = pickᴰ 13 Sᴰ
  lem-cQ-at0412213043 : Ws → St 180
  lem-cQ-at0412213043 = pickᴰ 14 Sᴰ
  lem-cQ-at04122140 : Ws → St 181
  lem-cQ-at04122140 = pickᴰ 15 Sᴰ
  lem-cQ-at0412233041 : Ws → St 169
  lem-cQ-at0412233041 = pickᴰ 16 Sᴰ
  lem-cQ-at0412233140 : Ws → St 182
  lem-cQ-at0412233140 = pickᴰ 17 Sᴰ
  lem-cQ-at0413203142 : Ws → St 183
  lem-cQ-at0413203142 = pickᴰ 18 Sᴰ
  lem-cQ-at0413203241 : Ws → St 184
  lem-cQ-at0413203241 = pickᴰ 19 Sᴰ
  lem-cQ-at0413213042 : Ws → St 185
  lem-cQ-at0413213042 = pickᴰ 20 Sᴰ
  lem-cQ-at0413213240 : Ws → St 186
  lem-cQ-at0413213240 = pickᴰ 21 Sᴰ
  lem-cQ-at04133140 : Ws → St 187
  lem-cQ-at04133140 = pickᴰ 22 Sᴰ
  lem-cQ-at04233240 : Ws → St 188
  lem-cQ-at04233240 = pickᴰ 23 Sᴰ
  lem-cQ-at0440 : Ws → St 189
  lem-cQ-at0440 = pickᴰ 24 Sᴰ
  lem-tP-at0310213442 : Ws → St 174
  lem-tP-at0310213442 = pickᴰ 25 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 139 (lem-box-tQ-at0410213243 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 128 (lem-tP-at0410213243 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1491 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1492 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 175 (lem-comm-CZ23-TOFF401 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1493 (lit c4)

-- P-box @0410213243: 8 steps
lem-P-box-at0410213243 : Ws → ⟪ (ℓ "亳侍亳") ⟫ʷ ≈ ⟪ (ℓ "侍") ⟫ʷ
lem-P-box-at0410213243 c4 = derive (ℓ "亳侍亳") (ℓ "侍")
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wpE 218 c4
  q8 : Ws → Eqn
  q8 c4 = wlE 1494 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = sE 69 (lem-comm-CZ23-CCZ014 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 169 (lem-cQ-at0412233041 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1495 (lit c4)

-- box-tQ @0412233041: 13 steps
lem-box-tQ-at0412233041 : Ws → ⟪ (ℓ "侚") ⟫ʷ ≈ ⟪ (ℓ "亳五亳五") ⟫ʷ
lem-box-tQ-at0412233041 c4 = derive (ℓ "侚") (ℓ "亳五亳五")
  (re 0 1 (ℓ "亰亳佑亳亰佑") ∷
   re 2 1 (ℓ "亜亞佐亞亜佐") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q7 c4) ∷
   re 5 1 (ℓ "亜亞佐亞亜佐") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wpE 1048 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 1309 c4
  q14 : Ws → Eqn
  q14 c4 = sE 134 (lem-comm-CZ02-CCZ134 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 179 (lem-cQ-at041041 c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 1310 c4

-- box-tQ @041041: 13 steps
lem-box-tQ-at041041 : Ws → ⟪ (ℓ "侏") ⟫ʷ ≈ ⟪ (ℓ "亟京亟京") ⟫ʷ
lem-box-tQ-at041041 c4 = derive (ℓ "侏") (ℓ "亟京亟京")
  (re 0 1 (ℓ "亜亟伉亟亜伉") ∷
   re 2 1 (ℓ "亠亡伂亡亠伂") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q12 c4) ∷
   re 5 1 (ℓ "亠亡伂亡亠伂") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 516 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 1391 c4
  q19 : Ws → Eqn
  q19 c4 = sE 78 (lem-comm-CZ03-CCZ124 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 178 (lem-cQ-at0410233241 c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 1392 c4

-- box-tQ @0410233241: 13 steps
lem-box-tQ-at0410233241 : Ws → ⟪ (ℓ "侑") ⟫ʷ ≈ ⟪ (ℓ "亣亨亣亨") ⟫ʷ
lem-box-tQ-at0410233241 c4 = derive (ℓ "侑") (ℓ "亣亨亣亨")
  (re 0 1 (ℓ "亠亣伃亣亠伃") ∷
   re 2 1 (ℓ "亜亝伂亝亜伂") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q17 c4) ∷
   re 5 1 (ℓ "亜亝伂亝亜伂") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = wpE 315 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 467 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 454 (lit c4)

-- tP @0410233241: 7 steps
lem-tP-at0410233241 : Ws → ⟪ (ℓ "亣享") ⟫ʷ ≈ ⟪ (ℓ "享亣") ⟫ʷ
lem-tP-at0410233241 c4 = derive (ℓ "亣享") (ℓ "享亣")
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = wpE 598 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 465 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 65 (lem-comm-CZ12-CCZ034 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 180 (lem-cQ-at0412213043 c4)
  q29 : Ws → Eqn
  q29 c4 = wlE 466 (lit c4)

-- box-tQ @0412213043: 13 steps
lem-box-tQ-at0412213043 : Ws → ⟪ (ℓ "侘") ⟫ʷ ≈ ⟪ (ℓ "享亠享亠") ⟫ʷ
lem-box-tQ-at0412213043 c4 = derive (ℓ "侘") (ℓ "享亠享亠")
  (re 0 1 (ℓ "亨享佖享亨佖") ∷
   re 2 1 (ℓ "亜亞何亞亜何") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw 2 (q25 c4) ∷
   re 5 1 (ℓ "亜亞何亞亜何") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw 5 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

-- tP @0412213043: 7 steps
lem-tP-at0412213043 : Ws → ⟪ (ℓ "享亣") ⟫ʷ ≈ ⟪ (ℓ "亣享") ⟫ʷ
lem-tP-at0412213043 c4 = derive (ℓ "享亣") (ℓ "亣享")
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = wpE 766 c4
  q31 : Ws → Eqn
  q31 c4 = wlE 1485 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = sE 67 (lem-comm-CZ13-CCZ024 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 186 (lem-cQ-at0413213240 c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 1486 (lit c4)

-- box-tQ @0413213240: 13 steps
lem-box-tQ-at0413213240 : Ws → ⟪ (ℓ "侟") ⟫ʷ ≈ ⟪ (ℓ "亯亜亯亜") ⟫ʷ
lem-box-tQ-at0413213240 c4 = derive (ℓ "侟") (ℓ "亯亜亯亜")
  (re 0 1 (ℓ "京亯來亯京來") ∷
   re 2 1 (ℓ "亰亲使亲亰使") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q30 c4) ∷
   re 5 1 (ℓ "亰亲使亲亰使") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = wpE 767 c4
  q36 : Ws → Eqn
  q36 c4 = sE 188 (lem-cQ-at04233240 c4)

-- box-tQ @04233240: 13 steps
lem-box-tQ-at04233240 : Ws → ⟪ (ℓ "侖") ⟫ʷ ≈ ⟪ (ℓ "亯亜亯亜") ⟫ʷ
lem-box-tQ-at04233240 c4 = derive (ℓ "侖") (ℓ "亯亜亯亜")
  (re 0 1 (ℓ "京亯伧亯京伧") ∷
   re 2 1 (ℓ "亨亩伦亩亨伦") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q35 c4) ∷
   re 5 1 (ℓ "亨亩伦亩亨伦") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q35 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = wpE 733 c4
  q38 : Ws → Eqn
  q38 c4 = sE 189 (lem-cQ-at0440 c4)

-- box-tQ @0440: 13 steps
lem-box-tQ-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "享亠享亠") ⟫ʷ
lem-box-tQ-at0440 c4 = derive (ℓ "侔") (ℓ "享亠享亠")
  (re 0 1 (ℓ "亨享伬享亨伬") ∷
   re 2 1 (ℓ "京亭伦亭京伦") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q37 c4) ∷
   re 5 1 (ℓ "京亭伦亭京伦") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q37 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

-- tP @0440: 7 steps
lem-tP-at0440 : Ws → ⟪ (ℓ "享亣") ⟫ʷ ≈ ⟪ (ℓ "亣享") ⟫ʷ
lem-tP-at0440 c4 = derive (ℓ "享亣") (ℓ "亣享")
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q38 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wlE 1596 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = sE 183 (lem-cQ-at0413203142 c4)

-- box-tQ @0413203142: 13 steps
lem-box-tQ-at0413203142 : Ws → ⟪ (ℓ "侜") ⟫ʷ ≈ ⟪ (ℓ "亣亨亣亨") ⟫ʷ
lem-box-tQ-at0413203142 c4 = derive (ℓ "侜") (ℓ "亣亨亣亨")
  (re 0 1 (ℓ "亠亣侃亣亠侃") ∷
   re 2 1 (ℓ "京亮佺亮京佺") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q39 c4) ∷
   re 5 1 (ℓ "京亮佺亮京佺") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q39 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = wlE 624 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 625 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 175 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = sE 176 (lem-cQ-at02142140 c4)

-- tP @02142140: 7 steps
lem-tP-at02142140 : Ws → ⟪ (ℓ "亪亚") ⟫ʷ ≈ ⟪ (ℓ "亚亪") ⟫ʷ
lem-tP-at02142140 c4 = derive (ℓ "亪亚") (ℓ "亚亪")
  (rw⁻ 0 (q41 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q41 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wpE 211 c4
  q46 : Ws → Eqn
  q46 c4 = sE 185 (lem-cQ-at0413213042 c4)

-- box-tQ @0413213042: 13 steps
lem-box-tQ-at0413213042 : Ws → ⟪ (ℓ "侞") ⟫ʷ ≈ ⟪ (ℓ "亯亜亯亜") ⟫ʷ
lem-box-tQ-at0413213042 c4 = derive (ℓ "侞") (ℓ "亯亜亯亜")
  (re 0 1 (ℓ "京亯佻亯京佻") ∷
   re 2 1 (ℓ "亠亢佺亢亠佺") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q45 c4) ∷
   re 5 1 (ℓ "亠亢佺亢亠佺") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q45 c4) ∷
   rw 0 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q34 c4) ∷ []) Eq.refl

-- tP @0413203142: 7 steps
lem-tP-at0413203142 : Ws → ⟪ (ℓ "亣享") ⟫ʷ ≈ ⟪ (ℓ "享亣") ⟫ʷ
lem-tP-at0413203142 c4 = derive (ℓ "亣享") (ℓ "享亣")
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wlE 1472 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wpE 1321 c4

-- tP @0413213240: 7 steps
lem-tP-at0413213240 : Ws → ⟪ (ℓ "亯亟") ⟫ʷ ≈ ⟪ (ℓ "亟亯") ⟫ʷ
lem-tP-at0413213240 c4 = derive (ℓ "亯亟") (ℓ "亟亯")
  (rw⁻ 0 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 1370 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q51 : Ws → Eqn
  q51 c4 = sE 174 (lem-tP-at0310213442 c4)
  q52 : Ws → Eqn
  q52 c4 = wlE 1192 (lit c4)

-- t-cP @0310213442: 5 steps
lem-t-cP-at0310213442 : Ws → ⟪ (ℓ "亓亐亲亐亲") ⟫ʷ ≈ ⟪ (ℓ "亐亲亐亲亓") ⟫ʷ
lem-t-cP-at0310213442 c4 = derive (ℓ "亓亐亲亐亲") (ℓ "亐亲亐亲亓")
  (rw⁻ 0 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 3 (q51 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = sE 84 (lem-box-tQ-at04203243 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 129 (lem-tP-at04203243 c4)

-- P-box @04203243: 8 steps
lem-P-box-at04203243 : Ws → ⟪ (ℓ "亳侒亳") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-P-box-at04203243 c4 = derive (ℓ "亳侒亳") (ℓ "侒")
  (rw 1 (q53 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wpE 1436 c4
  q56 : Ws → Eqn
  q56 c4 = sE 182 (lem-cQ-at0412233140 c4)

-- box-tQ @0412233140: 13 steps
lem-box-tQ-at0412233140 : Ws → ⟪ (ℓ "供") ⟫ʷ ≈ ⟪ (ℓ "亳五亳五") ⟫ʷ
lem-box-tQ-at0412233140 c4 = derive (ℓ "供") (ℓ "亳五亳五")
  (re 0 1 (ℓ "亰亳佛亳亰佛") ∷
   re 2 1 (ℓ "亨亪佚亪亨佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q55 c4) ∷
   re 5 1 (ℓ "亨亪佚亪亨佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q55 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 1437 c4
  q58 : Ws → Eqn
  q58 c4 = sE 177 (lem-cQ-at0410233142 c4)

-- box-tQ @0410233142: 13 steps
lem-box-tQ-at0410233142 : Ws → ⟪ (ℓ "侐") ⟫ʷ ≈ ⟪ (ℓ "亣亨亣亨") ⟫ʷ
lem-box-tQ-at0410233142 c4 = derive (ℓ "侐") (ℓ "亣亨亣亨")
  (re 0 1 (ℓ "亠亣仹亣亠仹") ∷
   re 2 1 (ℓ "五井仸井五仸") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q57 c4) ∷
   re 5 1 (ℓ "五井仸井五仸") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q57 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

-- tP @0410233142: 7 steps
lem-tP-at0410233142 : Ws → ⟪ (ℓ "亣享") ⟫ʷ ≈ ⟪ (ℓ "享亣") ⟫ʷ
lem-tP-at0410233142 c4 = derive (ℓ "亣享") (ℓ "享亣")
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q58 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wpE 732 c4
  q60 : Ws → Eqn
  q60 c4 = sE 181 (lem-cQ-at04122140 c4)

-- box-tQ @04122140: 13 steps
lem-box-tQ-at04122140 : Ws → ⟪ (ℓ "侙") ⟫ʷ ≈ ⟪ (ℓ "享亠享亠") ⟫ʷ
lem-box-tQ-at04122140 c4 = derive (ℓ "侙") (ℓ "享亠享亠")
  (re 0 1 (ℓ "亨享你享亨你") ∷
   re 2 1 (ℓ "亰亱佚亱亰佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q59 c4) ∷
   re 5 1 (ℓ "亰亱佚亱亰佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q59 c4) ∷
   rw 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 453 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 303 c4

-- tP @0412233140: 7 steps
lem-tP-at0412233140 : Ws → ⟪ (ℓ "亳亗") ⟫ʷ ≈ ⟪ (ℓ "亗亳") ⟫ʷ
lem-tP-at0412233140 c4 = derive (ℓ "亳亗") (ℓ "亗亳")
  (rw⁻ 0 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q61 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wpE 1456 c4
  q64 : Ws → Eqn
  q64 c4 = eqn (ℓ "个亳") (ℓ "亳个") (c₂ (CZ) (Toffᵗ))
  q65 : Ws → Eqn
  q65 c4 = wpE 1457 c4

-- t-cP @04203243: 5 steps
lem-t-cP-at04203243 : Ws → ⟪ (ℓ "亗五亳五亳") ⟫ʷ ≈ ⟪ (ℓ "五亳五亳亗") ⟫ʷ
lem-t-cP-at04203243 c4 = derive (ℓ "亗五亳五亳") (ℓ "五亳五亳亗")
  (rw⁻ 0 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q54 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 756 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 184 (lem-cQ-at0413203241 c4)

-- box-tQ @0413203241: 13 steps
lem-box-tQ-at0413203241 : Ws → ⟪ (ℓ "依") ⟫ʷ ≈ ⟪ (ℓ "亣亨亣亨") ⟫ʷ
lem-box-tQ-at0413203241 c4 = derive (ℓ "依") (ℓ "亣亨亣亨")
  (re 0 1 (ℓ "亠亣侊亣亠侊") ∷
   re 2 1 (ℓ "亰亲侉亲亰侉") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q66 c4) ∷
   re 5 1 (ℓ "亰亲侉亲亰侉") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q66 c4) ∷
   rw 0 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

-- tP @0413203241: 7 steps
lem-tP-at0413203241 : Ws → ⟪ (ℓ "亣享") ⟫ʷ ≈ ⟪ (ℓ "享亣") ⟫ʷ
lem-tP-at0413203241 c4 = derive (ℓ "亣享") (ℓ "享亣")
  (rw⁻ 0 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q22 c4) ∷ []) Eq.refl

-- tP @04122140: 7 steps
lem-tP-at04122140 : Ws → ⟪ (ℓ "享亣") ⟫ʷ ≈ ⟪ (ℓ "亣享") ⟫ʷ
lem-tP-at04122140 c4 = derive (ℓ "享亣") (ℓ "亣享")
  (rw⁻ 0 (q23 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q24 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wpE 1494 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 540 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 302 c4
  q71 : Ws → Eqn
  q71 c4 = wlE 302 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q73 : Ws → Eqn
  q73 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q74 : Ws → Eqn
  q74 c4 = wpE 342 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 1495 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 1496 c4

-- CSdu-box-2 @04203243: 17 steps
lem-CSdu-box-2-at04203243 : Ws → ⟪ (ℓ "举侒") ⟫ʷ ≈ ⟪ (ℓ "侒举") ⟫ʷ
lem-CSdu-box-2-at04203243 c4 = derive (ℓ "举侒") (ℓ "侒举")
  (rw 1 (q53 c4) ∷
   rw 0 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q75 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q76 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = wpE 1497 c4
  q78 : Ws → Eqn
  q78 c4 = wlE 1263 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 1498 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1499 c4

-- Su-box @04203243: 17 steps
lem-Su-box-at04203243 : Ws → ⟪ (ℓ "丢侒") ⟫ʷ ≈ ⟪ (ℓ "侒丢") ⟫ʷ
lem-Su-box-at04203243 c4 = derive (ℓ "丢侒") (ℓ "侒丢")
  (rw 1 (q53 c4) ∷
   rw 0 (q77 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q79 c4) ∷
   rw 2 (q77 c4) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 1503 c4
  q82 : Ws → Eqn
  q82 c4 = sE 187 (lem-cQ-at04133140 c4)

-- box-tQ @04133140: 13 steps
lem-box-tQ-at04133140 : Ws → ⟪ (ℓ "侠") ⟫ʷ ≈ ⟪ (ℓ "亳五亳五") ⟫ʷ
lem-box-tQ-at04133140 c4 = derive (ℓ "侠") (ℓ "亳五亳五")
  (re 0 1 (ℓ "亰亳侀亳亰侀") ∷
   re 2 1 (ℓ "京亮使亮京使") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q81 c4) ∷
   re 5 1 (ℓ "京亮使亮京使") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q81 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl
