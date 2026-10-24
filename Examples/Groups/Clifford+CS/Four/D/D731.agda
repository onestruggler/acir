{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD731 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D731 (W : Ws) (Sᴰ : SD731) where

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
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2260
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 0 Sᴰ
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 1 Sᴰ
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2231
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 2 Sᴰ
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2262
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 3 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : St 2263
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2264
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2265
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2266
  lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2267
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2268
  lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 9 Sᴰ
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2269
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 10 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2270
  lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 189 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 8 W
  q6 : Eqn
  q6 = wE 9 W
  q7 : Eqn
  q7 = wE 10 W
  q8 : Eqn
  q8 = wE 11 W
  q9 : Eqn
  q9 = wE 127 W
  q10 : Eqn
  q10 = wE 118 W
  q11 : Eqn
  q11 = wE 274 W
  q12 : Eqn
  q12 = wE 480 W
  q13 : Eqn
  q13 = wE 481 W
  q14 : Eqn
  q14 = sE 2261 lem-ROT-gad
  q15 : Eqn
  q15 = wE 311 W
  q16 : Eqn
  q16 = wE 123 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 28 W
  q20 : Eqn
  q20 = wE 29 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 322 W
  q23 : Eqn
  q23 = wE 313 W
  q24 : Eqn
  q24 = wE 312 W
  q25 : Eqn
  q25 = wE 31 W

-- ROT-gad @1023: 138 steps
lem-ROT-gad-at1023 : ⟪ (ℓ "两乙九丯九乙丯丈两乙九丯九乙丯") ⟫ʷ ≈ ⟪ (ℓ "与丐丽习举习丑丏") ⟫ʷ
lem-ROT-gad-at1023 = derive (ℓ "两乙九丯九乙丯丈两乙九丯九乙丯") (ℓ "与丐丽习举习丑丏")
  (rw 15 q1 ∷
   re 14 1 (ℓ "乏丩乏") ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (ℓ "丿") ∷
   re 13 1 (ℓ "丶丣丷丣丧") ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   re 14 5 (ℓ "乙") ∷
   re 12 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 12 q10 ∷
   rw 13 q11 ∷
   re 13 8 (ℓ "习") ∷
   re 11 1 (ℓ "乏丩乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丿") ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q7 ∷
   rw 10 q10 ∷
   rw 11 q11 ∷
   re 11 8 (ℓ "习") ∷
   re 9 1 (ℓ "丶丣丷丣丧") ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   re 10 5 (ℓ "乙") ∷
   rw 8 q12 ∷
   rw 7 q13 ∷
   re 6 1 (ℓ "乏丩乏") ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (ℓ "丿") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q5 ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q5 ∷
   rw 5 q7 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   re 5 8 (ℓ "习") ∷
   re 3 1 (ℓ "乏丩乏") ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (ℓ "丿") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   re 3 8 (ℓ "习") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   re 2 5 (ℓ "乙") ∷
   rw 0 q12 ∷
   rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 3 q17 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 3 q16 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   rw 8 q17 ∷
   rw 9 q16 ∷
   rw 10 q21 ∷
   rw 3 q11 ∷
   re 3 8 (ℓ "习") ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q2 ∷
   rw 5 q22 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 5 q16 ∷
   rw 6 q18 ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q19 ∷
   rw 10 q17 ∷
   rw 11 q16 ∷
   rw 12 q21 ∷
   rw 5 q11 ∷
   re 5 8 (ℓ "习") ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 8 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q28 : Eqn
  q28 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q30 : Eqn
  q30 = wE 1 W
  q31 : Eqn
  q31 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q32 : Eqn
  q32 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q34 : Eqn
  q34 = wE 2239 W
  q35 : Eqn
  q35 = wE 175 W
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q38 : Eqn
  q38 = wE 2240 W
  q39 : Eqn
  q39 = sE 2231 lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q40 : Eqn
  q40 = sE 2260 lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q41 : Eqn
  q41 = sE 2262 lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q42 : Eqn
  q42 = wE 2241 W

-- ca-split Gad(t=0, W=(3,), d=SdKdSS, e=-1) 3: 93 steps
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丞三下丈丈中九丮九三三上丈丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丞中九丮九丞丞丮丞丞丮丞丞乑丞丞中丞")
  (rw⁻ 0 q26 ∷
   rw⁻ 1 q27 ∷
   rw⁻ 2 q28 ∷
   rw⁻ 3 q28 ∷
   rw 12 q28 ∷
   rw 11 q29 ∷
   rw 10 q26 ∷
   rw 9 q26 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷
   rw 3 q30 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q35 ∷
   rw 3 q35 ∷
   rw 6 q30 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q35 ∷
   rw 6 q35 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q35 ∷
   rw 9 q35 ∷
   rw 12 q30 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q35 ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丮") ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "乒") ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q30 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q36 ∷
   rw 26 q30 ∷
   rw 25 q31 ∷
   rw 24 q37 ∷
   rw 23 q33 ∷
   rw 22 q33 ∷
   rw 23 q38 ∷
   rw 24 q30 ∷
   re 22 3 (ℓ "丮") ∷
   rw 25 q30 ∷
   re 23 3 (ℓ "丮") ∷
   rw 26 q30 ∷
   re 24 3 (ℓ "乑") ∷
   rw 27 q30 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q35 ∷
   rw 29 q30 ∷
   re 27 3 (ℓ "丮") ∷
   rw 28 q35 ∷
   rw 29 q35 ∷
   rw 32 q30 ∷
   re 30 3 (ℓ "丮") ∷
   rw 31 q35 ∷
   rw 32 q35 ∷
   rw 35 q30 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q35 ∷
   rw 35 q35 ∷
   rw 38 q30 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q35 ∷
   rw 38 q36 ∷
   rw 15 q39 ∷
   rw 14 q39 ∷
   rw 13 q40 ∷
   rw 12 q41 ∷
   rw 26 q30 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q36 ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw 26 q36 ∷
   re 23 1 (ℓ "乏丨乏") ∷
   rw 25 q36 ∷
   re 22 1 (ℓ "乏丨乏") ∷
   rw 24 q36 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q36 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q36 ∷
   re 19 1 (ℓ "乏久乏") ∷
   rw 21 q36 ∷
   re 18 1 (ℓ "乏丨乏") ∷
   rw 20 q36 ∷
   rw 19 q42 ∷
   rw 18 q36 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 2154 W
  q44 : Eqn
  q44 = sE 2268 lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q45 : Eqn
  q45 = wE 2155 W

-- pass [CS32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "义丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞义") ⟫ʷ
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "义丞义乣乊乣丞") (ℓ "丞义乣乊乣丞义")
  (rw 0 q43 ∷
   rw 1 q44 ∷
   rw 5 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 2242 W
  q47 : Eqn
  q47 = sE 2270 lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q48 : Eqn
  q48 = wE 2243 W

-- pass [CSd32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "乊丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞乊") ⟫ʷ
lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "乊丞义乣乊乣丞") (ℓ "丞义乣乊乣丞乊")
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 5 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q50 : Eqn
  q50 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q51 : Eqn
  q51 = wE 56 W
  q52 : Eqn
  q52 = wE 173 W
  q53 : Eqn
  q53 = wE 2016 W
  q54 : Eqn
  q54 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q55 : Eqn
  q55 = eqn (ℓ "丨丞") (ℓ "丞丨") (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q56 : Eqn
  q56 = sE 2263 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02
  q57 : Eqn
  q57 = wE 2017 W

-- pass [X3 TOFF201 CS23 TOFF201 CSd23 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞乣义乣乊丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞乣义乣乊丞") ⟫ʷ
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞乣义乣乊丞乞丧乞丨") (ℓ "乞丧乞丨丞乣义乣乊丞")
  (rw 7 q30 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q37 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q49 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q37 ∷
   rw⁻ 13 q50 ∷
   rw 14 q36 ∷
   rw 13 q50 ∷
   rw 12 q37 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q36 ∷
   rw 10 q49 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q36 ∷
   rw 8 q49 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q36 ∷
   rw 6 q37 ∷
   rw 7 q51 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 5 q35 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q37 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q49 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q37 ∷
   rw⁻ 13 q50 ∷
   rw 6 q30 ∷
   rw⁻ 7 q37 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q36 ∷
   rw⁻ 9 q49 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q36 ∷
   rw⁻ 11 q49 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q36 ∷
   rw⁻ 13 q37 ∷
   rw⁻ 14 q50 ∷
   rw 7 q51 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 7 q35 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw⁻ 8 q54 ∷
   rw 11 q30 ∷
   re 10 1 (ℓ "乏九乏") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q37 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q49 ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q49 ∷
   rw 17 q30 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q37 ∷
   rw⁻ 17 q50 ∷
   rw 18 q36 ∷
   rw 17 q50 ∷
   rw 16 q37 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q36 ∷
   rw 14 q49 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q36 ∷
   rw 12 q49 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q36 ∷
   rw 10 q37 ∷
   rw 11 q51 ∷
   re 11 8 (ℓ "九") ∷
   rw 9 q52 ∷
   rw 10 q53 ∷
   rw 9 q35 ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 10 q37 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q49 ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q49 ∷
   rw 17 q30 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q37 ∷
   rw⁻ 17 q50 ∷
   rw 10 q30 ∷
   rw⁻ 11 q37 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q36 ∷
   rw⁻ 13 q49 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q36 ∷
   rw⁻ 15 q49 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q36 ∷
   rw⁻ 17 q37 ∷
   rw⁻ 18 q50 ∷
   rw 11 q51 ∷
   re 11 8 (ℓ "九") ∷
   re 10 3 (ℓ "乞") ∷
   rw 11 q35 ∷
   rw 12 q35 ∷
   rw 13 q36 ∷
   rw⁻ 12 q55 ∷
   rw 1 q56 ∷
   rw 4 q30 ∷
   rw 3 q52 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q37 ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q37 ∷
   rw⁻ 9 q50 ∷
   rw 10 q36 ∷
   rw 9 q50 ∷
   rw 8 q37 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q36 ∷
   rw 6 q49 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q36 ∷
   rw 4 q49 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q36 ∷
   rw 2 q37 ∷
   rw 3 q51 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q52 ∷
   rw 0 q52 ∷
   rw 1 q57 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q37 ∷
   rw 3 q30 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q49 ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q37 ∷
   rw⁻ 7 q50 ∷
   rw 0 q30 ∷
   rw⁻ 1 q37 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q36 ∷
   rw⁻ 3 q49 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q36 ∷
   rw⁻ 5 q49 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q36 ∷
   rw⁻ 7 q37 ∷
   rw⁻ 8 q50 ∷
   rw 1 q51 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q54 ∷
   rw 6 q30 ∷
   rw 5 q52 ∷
   re 4 1 (ℓ "乏九乏") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q37 ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q37 ∷
   rw⁻ 11 q50 ∷
   rw 12 q36 ∷
   rw 11 q50 ∷
   rw 10 q37 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q36 ∷
   rw 8 q49 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q36 ∷
   rw 6 q49 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q36 ∷
   rw 4 q37 ∷
   rw 5 q51 ∷
   re 5 8 (ℓ "九") ∷
   rw 3 q52 ∷
   rw 2 q52 ∷
   rw 3 q57 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q37 ∷
   rw 5 q30 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q37 ∷
   rw⁻ 9 q50 ∷
   rw 2 q30 ∷
   rw⁻ 3 q37 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q36 ∷
   rw⁻ 5 q49 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q36 ∷
   rw⁻ 7 q49 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q36 ∷
   rw⁻ 9 q37 ∷
   rw⁻ 10 q50 ∷
   rw 3 q51 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw⁻ 3 q55 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q59 : Eqn
  q59 = wE 1689 W
  q60 : Eqn
  q60 = wE 2119 W
  q61 : Eqn
  q61 = sE 2267 lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X3 CS31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (ℓ "丞丽丞丌丽习举习丌") ⟫ʷ ≈ ⟪ (ℓ "丌丽习举习丌丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (ℓ "丞丽丞丌丽习举习丌") (ℓ "丌丽习举习丌丞丽丞")
  (rw 4 q30 ∷
   rw 3 q58 ∷
   rw 2 q52 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q36 ∷
   rw 0 q52 ∷
   rw 1 q59 ∷
   rw⁻ 0 q58 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q60 ∷
   rw 1 q61 ∷
   rw 5 q60 ∷
   rw 9 q30 ∷
   rw 8 q58 ∷
   rw 7 q52 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q36 ∷
   rw 5 q52 ∷
   rw 6 q59 ∷
   rw⁻ 5 q58 ∷
   rw 6 q35 ∷
   rw 9 q30 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q35 ∷
   rw 9 q36 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 1466 W
  q63 : Eqn
  q63 = sE 2269 lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q64 : Eqn
  q64 = wE 1467 W

-- pass [CSd30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "丮丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞丮") ⟫ʷ
lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "丮丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞丮")
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q36 ∷
   rw 1 q62 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q63 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (ℓ "乏丨乏") ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q64 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "丮") ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 1464 W
  q66 : Eqn
  q66 = sE 2265 lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q67 : Eqn
  q67 = wE 1465 W

-- pass [CKd30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乒丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乒") ⟫ʷ
lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乒丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乒")
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q36 ∷
   rw 1 q65 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q66 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (ℓ "乏久乏") ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q67 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "乒") ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 1407 W
  q69 : Eqn
  q69 = sE 2264 lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q70 : Eqn
  q70 = wE 1408 W

-- pass [CK30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乑丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乑") ⟫ʷ
lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乑丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乑")
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q36 ∷
   rw 1 q68 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q69 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q70 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 1462 W
  q72 : Eqn
  q72 = sE 2266 lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q73 : Eqn
  q73 = wE 1463 W

-- pass [CS30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "中丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞中") ⟫ʷ
lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "中丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞中")
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q36 ∷
   rw 1 q71 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q72 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q73 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 2169 W
  q75 : Eqn
  q75 = wE 2170 W

-- pass [X3 CS32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (ℓ "丞义丞丌义乣乊乣丌") ⟫ʷ ≈ ⟪ (ℓ "丌义乣乊乣丌丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (ℓ "丞义丞丌义乣乊乣丌") (ℓ "丌义乣乊乣丌丞义丞")
  (rw 0 q74 ∷
   rw 1 q75 ∷
   rw 1 q44 ∷
   rw 5 q75 ∷
   rw 5 q74 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 2244 W
  q77 : Eqn
  q77 = wE 2245 W

-- pass [X3 CSd32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (ℓ "丞乊丞丌义乣乊乣丌") ⟫ʷ ≈ ⟪ (ℓ "丌义乣乊乣丌丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (ℓ "丞乊丞丌义乣乊乣丌") (ℓ "丌义乣乊乣丌丞乊丞")
  (rw 0 q76 ∷
   rw 1 q77 ∷
   rw 1 q47 ∷
   rw 5 q77 ∷
   rw 5 q76 ∷ []) Eq.refl
