{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD758 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D758 (W : Ws) (Sᴰ : SD758) where

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
  lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : St 2864
  lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = pickᴰ 0 Sᴰ
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : St 2865
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = pickᴰ 1 Sᴰ
  lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : St 2866
  lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = pickᴰ 2 Sᴰ
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : St 2867
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = pickᴰ 3 Sᴰ
  lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2868
  lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 4 Sᴰ
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 5 Sᴰ
  lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : St 2869
  lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = wE 12 W
  q2 : Eqn
  q2 = wE 2535 W
  q3 : Eqn
  q3 = wE 121 W
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
  q11 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q13 : Eqn
  q13 = wE 22 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 23 W
  q16 : Eqn
  q16 = wE 14 W
  q17 : Eqn
  q17 = wE 47 W
  q18 : Eqn
  q18 = wE 48 W
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q24 : Eqn
  q24 = wE 56 W
  q25 : Eqn
  q25 = wE 1609 W
  q26 : Eqn
  q26 = eqn (ℓ "丼丞") (ℓ "丞丼") (low₃-comm ((Swap ↑)) (X))
  q27 : Eqn
  q27 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q28 : Eqn
  q28 = wE 15 W
  q29 : Eqn
  q29 = wE 16 W
  q30 : Eqn
  q30 = wE 46 W
  q31 : Eqn
  q31 = sE 2674 lem-merge3
  q32 : Eqn
  q32 = wE 18 W
  q33 : Eqn
  q33 = wE 19 W
  q34 : Eqn
  q34 = wE 17 W
  q35 : Eqn
  q35 = wE 43 W
  q36 : Eqn
  q36 = wE 20 W
  q37 : Eqn
  q37 = wE 21 W
  q38 : Eqn
  q38 = wE 5 W
  q39 : Eqn
  q39 = wE 24 W
  q40 : Eqn
  q40 = wE 25 W
  q41 : Eqn
  q41 = wE 26 W

-- merge3 @0321: 460 steps
lem-merge3-at0321 : ⟪ (ℓ "也丠也両丒也丠也両丒") ⟫ʷ ≈ ⟪ (ℓ "义乛") ⟫ʷ
lem-merge3-at0321 = derive (ℓ "也丠也両丒也丠也両丒") (ℓ "义乛")
  (rw 10 q1 ∷
   rw 9 q2 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丨") ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   rw 12 q15 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "丼丣丼") ∷
   rw 13 q16 ∷
   rw 10 q17 ∷
   re 9 1 (ℓ "丼丣丼") ∷
   rw 11 q16 ∷
   rw 8 q18 ∷
   rw 7 q12 ∷
   rw 8 q19 ∷
   rw⁻ 9 q20 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q21 ∷
   rw⁻ 13 q22 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q21 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 16 q23 ∷
   rw 9 q24 ∷
   re 9 8 (ℓ "九") ∷
   re 8 3 (ℓ "乞") ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "丧") ∷
   re 5 1 (ℓ "並乢並") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q13 ∷
   rw 12 q14 ∷
   rw 10 q15 ∷
   re 11 5 (ℓ "中") ∷
   re 9 1 (ℓ "丼丣丼") ∷
   rw 11 q16 ∷
   rw 8 q17 ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 9 q16 ∷
   rw 6 q18 ∷
   rw 5 q12 ∷
   rw 6 q19 ∷
   rw⁻ 7 q20 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw⁻ 9 q22 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q21 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q23 ∷
   rw 7 q24 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 4 q2 ∷
   rw 3 q1 ∷
   re 4 3 (ℓ "丨") ∷
   re 2 1 (ℓ "並乢並") ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   rw 7 q15 ∷
   re 8 5 (ℓ "中") ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 8 q16 ∷
   rw 5 q17 ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 6 q16 ∷
   rw 3 q18 ∷
   rw 2 q12 ∷
   rw 3 q19 ∷
   rw⁻ 4 q20 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 11 q23 ∷
   rw 4 q24 ∷
   re 4 8 (ℓ "九") ∷
   re 3 3 (ℓ "乞") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "丧") ∷
   re 0 1 (ℓ "並乢並") ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
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
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   rw 5 q15 ∷
   re 6 5 (ℓ "中") ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 6 q16 ∷
   rw 3 q17 ∷
   re 2 1 (ℓ "丼丣丼") ∷
   rw 4 q16 ∷
   rw 1 q18 ∷
   rw 0 q12 ∷
   rw 1 q19 ∷
   rw⁻ 2 q20 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q21 ∷
   rw⁻ 8 q20 ∷
   rw⁻ 9 q23 ∷
   rw 2 q24 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 11 q19 ∷
   rw 10 q25 ∷
   rw 9 q19 ∷
   re 10 3 (ℓ "丮") ∷
   re 8 1 (ℓ "乏九乏") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 8 q20 ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q22 ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q22 ∷
   rw 15 q19 ∷
   re 13 3 (ℓ "中") ∷
   rw⁻ 14 q20 ∷
   rw⁻ 15 q23 ∷
   rw 16 q21 ∷
   rw 15 q23 ∷
   rw 14 q20 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q21 ∷
   rw 12 q22 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q21 ∷
   rw 8 q20 ∷
   rw 9 q24 ∷
   re 9 8 (ℓ "九") ∷
   rw 7 q19 ∷
   re 8 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q20 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q22 ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q22 ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q20 ∷
   rw⁻ 13 q23 ∷
   rw 14 q21 ∷
   rw 13 q23 ∷
   rw 12 q20 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q21 ∷
   rw 6 q20 ∷
   rw 7 q24 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q25 ∷
   rw 4 q19 ∷
   re 5 3 (ℓ "丮") ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q20 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q22 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q20 ∷
   rw⁻ 10 q23 ∷
   rw 11 q21 ∷
   rw 10 q23 ∷
   rw 9 q20 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 3 q20 ∷
   rw 4 q24 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q19 ∷
   re 3 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q20 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q23 ∷
   rw 9 q21 ∷
   rw 8 q23 ∷
   rw 7 q20 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q21 ∷
   rw 3 q22 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw 1 q20 ∷
   rw 2 q24 ∷
   re 2 8 (ℓ "九") ∷
   rw 12 q1 ∷
   rw⁻ 11 q26 ∷
   re 10 1 (ℓ "乏丼両丼乏") ∷
   rw 13 q13 ∷
   rw 12 q27 ∷
   rw 10 q15 ∷
   re 11 5 (ℓ "丮") ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 16 q11 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q16 ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "个") ∷
   rw 12 q28 ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q29 ∷
   rw 9 q12 ∷
   rw 10 q30 ∷
   re 10 8 (ℓ "九") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q13 ∷
   rw 10 q14 ∷
   rw 8 q15 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q16 ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q28 ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q29 ∷
   rw 7 q12 ∷
   rw 8 q30 ∷
   re 8 8 (ℓ "九") ∷
   rw⁻ 6 q26 ∷
   re 5 1 (ℓ "乏丼両丼乏") ∷
   rw 8 q13 ∷
   rw 7 q27 ∷
   rw 5 q15 ∷
   re 6 5 (ℓ "丮") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 11 q11 ∷
   rw 10 q12 ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 11 q16 ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q28 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q29 ∷
   rw 4 q12 ∷
   rw 5 q30 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 3 q15 ∷
   re 4 5 (ℓ "中") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q16 ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q28 ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q29 ∷
   rw 2 q12 ∷
   rw 3 q30 ∷
   re 3 8 (ℓ "九") ∷
   rw 3 q31 ∷
   rw 2 q32 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q32 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q33 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q16 ∷
   rw 3 q34 ∷
   re 3 5 (ℓ "乙") ∷
   rw 4 q16 ∷
   rw 3 q19 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q21 ∷
   rw 3 q35 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 3 q21 ∷
   rw 0 q36 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q21 ∷
   rw 1 q36 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q37 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q13 ∷
   rw⁻ 7 q14 ∷
   rw 8 q15 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q38 ∷
   rw 2 q4 ∷
   rw 3 q39 ∷
   rw 4 q6 ∷
   rw 5 q39 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 7 q40 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q41 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 464 W
  q43 : Eqn
  q43 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q44 : Eqn
  q44 = wE 1416 W
  q45 : Eqn
  q45 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q46 : Eqn
  q46 = sE 2867 lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩
  q47 : Eqn
  q47 = sE 2869 lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1
  q48 : Eqn
  q48 = sE 2866 lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩
  q49 : Eqn
  q49 = sE 2868 lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q50 : Eqn
  q50 = wE 1417 W
  q51 : Eqn
  q51 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 120 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒九中九丮丒") (ℓ "丒九中九丮丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q19 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q21 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q21 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q21 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q21 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q21 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q21 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q21 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q21 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q21 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q21 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q21 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q21 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q21 ∷
   rw 15 q42 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q21 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q21 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q21 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q21 ∷
   rw 10 q42 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q21 ∷
   rw 8 q42 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q21 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q21 ∷
   rw 5 q43 ∷
   rw 4 q43 ∷
   rw 3 q14 ∷
   rw 2 q43 ∷
   rw 1 q14 ∷
   rw 0 q14 ∷
   rw 1 q44 ∷
   rw⁻ 0 q43 ∷
   rw 3 q19 ∷
   re 1 3 (ℓ "中") ∷
   rw⁻ 2 q45 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q21 ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q48 ∷
   rw 0 q49 ∷
   rw 10 q19 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q21 ∷
   rw 8 q45 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw 6 q43 ∷
   rw 7 q50 ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q43 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q43 ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "乀") ∷
   rw 15 q19 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q51 ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q51 ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q19 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q51 ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q19 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "乀") ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q19 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q19 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q19 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q21 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 2865 lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩
  q53 : Eqn
  q53 = sE 2864 lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 6 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒九中九丮丒") (ℓ "丒九中九丮丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q44 ∷
   rw 3 q52 ∷
   rw 2 q47 ∷
   rw 1 q53 ∷
   rw 0 q49 ∷
   rw 6 q50 ∷ []) Eq.refl

-- L87 merge-p 0123 3: 1 steps
lem-L87-merge-p-0123-3 : ⟪ (ℓ "九中九丮丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丶乙") ⟫ʷ
lem-L87-merge-p-0123-3 = derive (ℓ "九中九丮丞九中九丮丞") (ℓ "丶乙")
  (rw 0 q31 ∷ []) Eq.refl
