{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD725 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D725 (W : Ws) (Sᴰ : SD725) where

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
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 2052
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0 : St 2190
  lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2191
  lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 5 Sᴰ
  lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2192
  lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 6 Sᴰ
  lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2193
  lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2194
  lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : St 2195
  lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = pickᴰ 9 Sᴰ

private
  q1 : Eqn
  q1 = wE 2197 W
  q2 : Eqn
  q2 = sE 2052 lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q3 : Eqn
  q3 = sE 851 lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q4 : Eqn
  q4 = wE 2198 W

-- pass [X2 CK20 X2] [S0 Kd0 S0 S0 TOFF012 CS03 TOFF012 CSd03 Sd0 Sd0 K0 Sd0]: 7 steps
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 : ⟪ (ℓ "丘乄丘丈下丈丈九中九丮三三上三") ⟫ʷ ≈ ⟪ (ℓ "丈下丈丈九中九丮三三上三丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 = derive (ℓ "丘乄丘丈下丈丈九中九丮三三上三") (ℓ "丈下丈丈九中九丮三三上三丘乄丘")
  (rw 0 q1 ∷
   rw 16 q2 ∷
   rw 13 q3 ∷
   rw 10 q3 ∷
   rw 7 q2 ∷
   rw 4 q3 ∷
   rw 8 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 2199 W
  q6 : Eqn
  q6 = sE 2058 lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q7 : Eqn
  q7 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q8 : Eqn
  q8 = wE 2200 W

-- pass [X1 CSd10 X1] [Sd0 K0 S0 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 Sd0 Kd0 S0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 : ⟪ (ℓ "丒両丒三上丈丈上九中九丮下三三下丈") ⟫ʷ ≈ ⟪ (ℓ "三上丈丈上九中九丮下三三下丈丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 = derive (ℓ "丒両丒三上丈丈上九中九丮下三三下丈") (ℓ "三上丈丈上九中九丮下三三下丈丒両丒")
  (rw 0 q5 ∷
   rw 11 q6 ∷
   rw 8 q6 ∷
   rw 5 q7 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1459 W
  q10 : Eqn
  q10 = sE 2190 lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0
  q11 : Eqn
  q11 = wE 2201 W
  q12 : Eqn
  q12 = wE 2202 W
  q13 : Eqn
  q13 = wE 1461 W

-- CA CK20 Gad(t=0, W=(), d=KSSK, e=1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : ⟪ (ℓ "乄上丈丈上九中九丮下三三下") ⟫ʷ ≈ ⟪ (ℓ "丈丈上上上九中九丮下下下三三乄") ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = derive (ℓ "乄上丈丈上九中九丮下三三下") (ℓ "丈丈上上上九中九丮下下下三三乄")
  (rw 0 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   rw 9 q12 ∷
   rw 14 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 2203 W
  q15 : Eqn
  q15 = wE 2204 W

-- pass [X1 CSd10 X1] [Sd0 K0 Sd0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 S0 Kd0 S0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 : ⟪ (ℓ "丒両丒三上三上上九中九丮下下丈下丈") ⟫ʷ ≈ ⟪ (ℓ "三上三上上九中九丮下下丈下丈丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 = derive (ℓ "丒両丒三上三上上九中九丮下下丈下丈") (ℓ "三上三上上九中九丮下下丈下丈丒両丒")
  (rw 0 q14 ∷
   rw 11 q6 ∷
   rw 8 q7 ∷
   rw 5 q7 ∷
   rw 9 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 1812 W
  q19 : Eqn
  q19 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q20 : Eqn
  q20 = wE 175 W
  q21 : Eqn
  q21 = sE 2194 lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q22 : Eqn
  q22 = eqn (ℓ "三丒") (ℓ "丒三") (low₁-comm ((S • S • S)) (X))
  q23 : Eqn
  q23 = wE 1813 W
  q24 : Eqn
  q24 = wE 1732 W
  q25 : Eqn
  q25 = wE 173 W
  q26 : Eqn
  q26 = wE 1814 W

-- CA CSd30 Gad(t=0, W=(1,), d=1, e=1): 25 steps
lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (ℓ "丮丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒三九中九丮丈丒丮") ⟫ʷ
lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (ℓ "丮丒九中九丮丒") (ℓ "丒三九中九丮丈丒丮")
  (rw 1 q16 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw⁻ 0 q19 ∷
   rw 1 q20 ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q20 ∷
   rw 4 q17 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷
   rw 6 q24 ∷
   rw 7 q22 ∷
   rw 12 q16 ∷
   rw 11 q25 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q17 ∷
   rw 9 q25 ∷
   rw 8 q19 ∷
   rw 9 q26 ∷
   rw 10 q16 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q17 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1815 W
  q28 : Eqn
  q28 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q29 : Eqn
  q29 = sE 2195 lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1
  q30 : Eqn
  q30 = eqn (ℓ "丈丒") (ℓ "丒丈") (low₁-comm (S) (X))
  q31 : Eqn
  q31 = wE 1728 W
  q32 : Eqn
  q32 = wE 1727 W
  q33 : Eqn
  q33 = wE 1816 W

-- CA CS30 Gad(t=0, W=(1,), d=Sd, e=1): 25 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : ⟪ (ℓ "中丒三九中九丮丈丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒中") ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = derive (ℓ "中丒三九中九丮丈丒") (ℓ "丒九中九丮丒中")
  (rw 1 q16 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q17 ∷
   rw 1 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q20 ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q20 ∷
   rw 4 q17 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 5 q32 ∷
   rw 5 q30 ∷
   rw 10 q16 ∷
   rw 9 q25 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q17 ∷
   rw 7 q25 ∷
   rw 6 q28 ∷
   rw 7 q33 ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q17 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 2205 W
  q35 : Eqn
  q35 = wE 2206 W

-- pass [CK10] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "临丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒临") ⟫ʷ
lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "临丒九中九丮丒") (ℓ "丒九中九丮丒临")
  (rw 0 q34 ∷
   rw 1 q6 ∷
   rw 5 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 2191 lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1

-- CCZ(1,2,3) passes split Gad(t=0, W=(1,), d=1, e=1): 1 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乜丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乜") ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (ℓ "乜丒九中九丮丒") (ℓ "丒九中九丮丒乜")
  (rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 2207 W
  q38 : Eqn
  q38 = sE 2193 lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q39 : Eqn
  q39 = sE 2192 lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q40 : Eqn
  q40 = wE 2208 W

-- pass [TOFF312] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 5 steps
lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "乨丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒乨") ⟫ʷ
lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "乨丒九中九丮丒") (ℓ "丒九中九丮丒乨")
  (rw 0 q37 ∷
   rw 2 q38 ∷
   rw 1 q36 ∷
   rw 0 q39 ∷
   rw 6 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 2209 W
  q42 : Eqn
  q42 = wE 2210 W

-- pass [X1 CSd10 X1] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (ℓ "丒両丒下九中九丮上") ⟫ʷ ≈ ⟪ (ℓ "下九中九丮上丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (ℓ "丒両丒下九中九丮上") (ℓ "下九中九丮上丒両丒")
  (rw 0 q41 ∷
   rw 7 q7 ∷
   rw 4 q6 ∷
   rw 1 q7 ∷
   rw 5 q42 ∷ []) Eq.refl
