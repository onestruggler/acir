{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD724 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D724 (W : Ws) (Sᴰ : SD724) where

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
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 3 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2045
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 8 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 9 Sᴰ
  lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS : St 2184
  lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS = pickᴰ 10 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 : St 2185
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 = pickᴰ 11 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 : St 2186
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 = pickᴰ 12 Sᴰ
  lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 : St 2187
  lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 = pickᴰ 13 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 : St 2188
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 = pickᴰ 14 Sᴰ
  lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- : St 2189
  lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = wE 1534 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 173 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 1665 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = sE 2045 lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q11 : Eqn
  q11 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q12 : Eqn
  q12 = wE 1666 W

-- pass [X3 CK31 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 41 steps
lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乔丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乔丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乔丞")
  (rw 0 q1 ∷
   rw 7 q2 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q7 ∷
   rw 0 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q3 ∷
   rw 4 q9 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "乔") ∷
   rw 6 q9 ∷
   rw 7 q7 ∷
   rw 4 q10 ∷
   rw 15 q2 ∷
   rw 14 q3 ∷
   rw 13 q11 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 11 q7 ∷
   rw 8 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 11 q3 ∷
   rw 12 q9 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "乔") ∷
   rw 14 q9 ∷
   rw 15 q7 ∷
   rw 12 q1 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q15 : Eqn
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 76 W
  q18 : Eqn
  q18 = wE 2063 W
  q19 : Eqn
  q19 = wE 29 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = wE 2061 W
  q22 : Eqn
  q22 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q23 : Eqn
  q23 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q24 : Eqn
  q24 = wE 2062 W

-- pass [X3 CSd30 X3] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 83 steps
lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (ℓ "丞丮丞丘下中九丮九上丘") ⟫ʷ ≈ ⟪ (ℓ "丘下中九丮九上丘丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = derive (ℓ "丞丮丞丘下中九丮九上丘") (ℓ "丘下中九丮九上丘丞丮丞")
  (rw 4 q13 ∷
   rw⁻ 3 q14 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q16 ∷
   rw 2 q17 ∷
   rw⁻ 1 q16 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 0 q15 ∷
   rw 1 q18 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q16 ∷
   rw 3 q19 ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q15 ∷
   rw 4 q20 ∷
   rw 5 q2 ∷
   rw 4 q4 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   rw 1 q6 ∷
   rw 2 q21 ∷
   rw⁻ 1 q4 ∷
   rw 2 q9 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q9 ∷
   rw 5 q9 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q9 ∷
   rw 11 q7 ∷
   rw 8 q22 ∷
   rw 5 q23 ∷
   rw 2 q22 ∷
   rw 16 q2 ∷
   rw 15 q11 ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q7 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q7 ∷
   rw 9 q6 ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q7 ∷
   rw 6 q6 ∷
   rw 7 q24 ∷
   rw⁻ 6 q11 ∷
   rw 7 q9 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q9 ∷
   rw 10 q7 ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q15 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q16 ∷
   rw 9 q17 ∷
   rw⁻ 8 q16 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 8 q18 ∷
   rw 7 q14 ∷
   rw 8 q15 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q16 ∷
   rw 10 q19 ∷
   rw 11 q16 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q15 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 1701 W
  q26 : Eqn
  q26 = sE 2184 lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS
  q27 : Eqn
  q27 = wE 387 W
  q28 : Eqn
  q28 = wE 25 W
  q29 : Eqn
  q29 = wE 275 W
  q30 : Eqn
  q30 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q31 : Eqn
  q31 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q32 : Eqn
  q32 = wE 327 W
  q33 : Eqn
  q33 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q34 : Eqn
  q34 = wE 315 W
  q35 : Eqn
  q35 = sE 2189 lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13-
  q36 : Eqn
  q36 = wE 1702 W

-- conjF X0 CS03 CS03 CK30 CS03 CX32 CS: 143 steps
lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS : ⟪ (ℓ "丳丢丒丣丢丒丌中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌") ⟫ʷ ≈ ⟪ (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丳丢丒丣丢丒") ⟫ʷ
lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS = derive (ℓ "丳丢丒丣丢丒丌中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌") (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丳丢丒丣丢丒")
  (rw 0 q25 ∷
   rw 2 q26 ∷
   rw 1 q27 ∷
   rw 81 q13 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 0 q16 ∷
   rw 1 q28 ∷
   rw 2 q16 ∷
   re 0 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 1 q16 ∷
   rw 2 q28 ∷
   rw 3 q16 ∷
   re 1 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 2 q16 ∷
   rw 3 q29 ∷
   rw 4 q16 ∷
   re 2 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q16 ∷
   rw 4 q28 ∷
   rw 5 q16 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 6 q28 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 9 q31 ∷
   rw 10 q28 ∷
   rw 11 q28 ∷
   rw 12 q28 ∷
   rw 13 q28 ∷
   rw 14 q28 ∷
   rw 15 q28 ∷
   rw 16 q30 ∷
   rw 17 q28 ∷
   rw 18 q28 ∷
   rw 19 q29 ∷
   rw 20 q28 ∷
   rw 21 q32 ∷
   rw 22 q28 ∷
   rw 23 q28 ∷
   rw 24 q28 ∷
   rw 25 q31 ∷
   rw 26 q29 ∷
   rw 27 q28 ∷
   rw 28 q28 ∷
   rw 29 q28 ∷
   rw 30 q28 ∷
   rw 31 q28 ∷
   rw 32 q28 ∷
   rw 33 q30 ∷
   rw 34 q28 ∷
   rw 35 q28 ∷
   rw 36 q28 ∷
   rw 37 q28 ∷
   rw 38 q28 ∷
   rw 39 q28 ∷
   rw 40 q28 ∷
   rw 41 q28 ∷
   rw 42 q28 ∷
   rw 43 q28 ∷
   rw 44 q28 ∷
   rw 45 q28 ∷
   rw 46 q28 ∷
   rw 47 q28 ∷
   rw 48 q28 ∷
   rw 49 q28 ∷
   rw 50 q28 ∷
   rw 51 q28 ∷
   rw 52 q31 ∷
   rw 53 q31 ∷
   rw 54 q31 ∷
   rw 55 q31 ∷
   rw 56 q29 ∷
   rw 57 q28 ∷
   rw 58 q28 ∷
   rw 59 q28 ∷
   rw 60 q28 ∷
   rw 61 q28 ∷
   rw 62 q28 ∷
   rw 63 q28 ∷
   rw 64 q28 ∷
   rw 65 q28 ∷
   rw 66 q30 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 67 q16 ∷
   rw 68 q28 ∷
   rw 69 q16 ∷
   re 67 3 (ℓ "丽") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 68 q16 ∷
   rw 69 q28 ∷
   rw 70 q16 ∷
   re 68 3 (ℓ "丽") ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 69 q16 ∷
   rw 70 q28 ∷
   rw 71 q16 ∷
   re 69 3 (ℓ "丽") ∷
   rw 70 q33 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 71 q16 ∷
   rw 72 q29 ∷
   rw 73 q16 ∷
   re 71 3 (ℓ "乔") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 72 q16 ∷
   rw 73 q28 ∷
   rw 74 q16 ∷
   re 72 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 73 q16 ∷
   rw 74 q28 ∷
   rw 75 q16 ∷
   re 73 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 74 q16 ∷
   rw 75 q28 ∷
   rw 76 q16 ∷
   re 74 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 75 q16 ∷
   rw 76 q28 ∷
   rw 77 q16 ∷
   re 75 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q16 ∷
   rw 77 q28 ∷
   rw 78 q16 ∷
   re 76 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 77 q16 ∷
   rw 78 q28 ∷
   rw 79 q16 ∷
   re 77 3 (ℓ "丽") ∷
   rw 78 q34 ∷
   rw 79 q32 ∷
   rw 80 q20 ∷
   rw 0 q35 ∷
   rw 80 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 2175 W
  q38 : Eqn
  q38 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q39 : Eqn
  q39 = wE 2176 W

-- pass [X2 CK20 X2] [Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0]: 3 steps
lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 : ⟪ (ℓ "丘乄丘下下中九丮九上上") ⟫ʷ ≈ ⟪ (ℓ "下下中九丮九上上丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 = derive (ℓ "丘乄丘下下中九丮九上上") (ℓ "下下中九丮九上上丘乄丘")
  (rw 0 q37 ∷
   rw 2 q38 ∷
   rw 6 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 2177 W
  q41 : Eqn
  q41 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q42 : Eqn
  q42 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q43 : Eqn
  q43 = wE 2178 W

-- pass [X2 CKd20 X2] [S0 S0 Kd0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 K0 Sd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 : ⟪ (ℓ "丘久丘丈丈下丈中九丮九三上三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈中九丮九三上三三丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 = derive (ℓ "丘久丘丈丈下丈中九丮九三上三三") (ℓ "丈丈下丈中九丮九三上三三丘久丘")
  (rw 0 q40 ∷
   rw 16 q38 ∷
   rw 13 q38 ∷
   rw 10 q41 ∷
   rw 7 q38 ∷
   rw 4 q42 ∷
   rw 8 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 2179 W
  q45 : Eqn
  q45 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q46 : Eqn
  q46 = wE 2180 W

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 S0]: 79 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乒丞三下丈丈下中九丮九上三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈下中九丮九上三三上丈丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = derive (ℓ "丞乒丞三下丈丈下中九丮九上三三上丈") (ℓ "三下丈丈下中九丮九上三三上丈丞乒丞")
  (rw 8 q2 ∷
   rw 7 q4 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q7 ∷
   rw 0 q6 ∷
   rw 1 q44 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw 5 q9 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q9 ∷
   rw 20 q7 ∷
   rw 17 q23 ∷
   rw 14 q23 ∷
   rw 11 q45 ∷
   rw 8 q23 ∷
   rw 5 q22 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q11 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw 24 q11 ∷
   rw 23 q6 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw 24 q7 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q7 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   re 16 1 (ℓ "乏丨乏") ∷
   rw 18 q7 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q7 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q7 ∷
   rw 9 q6 ∷
   rw 10 q46 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 13 q3 ∷
   rw 14 q9 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乒") ∷
   rw 16 q9 ∷
   rw 17 q7 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 2181 W
  q48 : Eqn
  q48 = wE 2182 W

-- pass [X2 CKd20 X2] [Sd0 K0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 Kd0 S0]: 7 steps
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 : ⟪ (ℓ "丘久丘三上丈丈中九丮九三三下丈") ⟫ʷ ≈ ⟪ (ℓ "三上丈丈中九丮九三三下丈丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 = derive (ℓ "丘久丘三上丈丈中九丮九三三下丈") (ℓ "三上丈丈中九丮九三三下丈丘久丘")
  (rw 0 q47 ∷
   rw 16 q38 ∷
   rw 13 q42 ∷
   rw 10 q42 ∷
   rw 7 q38 ∷
   rw 4 q41 ∷
   rw 8 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1709 W
  q50 : Eqn
  q50 = sE 2187 lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0
  q51 : Eqn
  q51 = wE 2183 W
  q52 : Eqn
  q52 = wE 2184 W
  q53 : Eqn
  q53 = wE 1711 W

-- CA CKd30 Gad(t=0, W=(), d=KSSKd, e=1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "乒上丈丈下九中九丮上三三下") ⟫ʷ ≈ ⟪ (ℓ "丈丈下九中九丮上三三乒") ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "乒上丈丈下九中九丮上三三下") (ℓ "丈丈下九中九丮上三三乒")
  (rw 1 q2 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q7 ∷
   rw 1 q49 ∷
   rw⁻ 0 q4 ∷
   rw 1 q9 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   rw 1 q50 ∷
   rw 0 q51 ∷
   rw 7 q52 ∷
   rw 14 q2 ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q7 ∷
   rw 11 q6 ∷
   rw 10 q4 ∷
   rw 11 q53 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乒") ∷
   rw 11 q7 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 2185 W
  q55 : Eqn
  q55 = sE 2058 lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q56 : Eqn
  q56 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q57 : Eqn
  q57 = wE 2186 W

-- pass [X1 CK10 X1] [S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0]: 7 steps
lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 : ⟪ (ℓ "丒临丒丈下九中九丮上三") ⟫ʷ ≈ ⟪ (ℓ "丈下九中九丮上三丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 = derive (ℓ "丒临丒丈下九中九丮上三") (ℓ "丈下九中九丮上三丒临丒")
  (rw 0 q54 ∷
   rw 14 q55 ∷
   rw 11 q56 ∷
   rw 8 q56 ∷
   rw 5 q55 ∷
   rw 2 q56 ∷
   rw 6 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 2187 W
  q59 : Eqn
  q59 = wE 2188 W

-- pass [X1 CSd10 X1] [Kd0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 K0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 : ⟪ (ℓ "丒両丒下丈下九中九丮上三上") ⟫ʷ ≈ ⟪ (ℓ "下丈下九中九丮上三上丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 = derive (ℓ "丒両丒下丈下九中九丮上三上") (ℓ "下丈下九中九丮上三上丒両丒")
  (rw 0 q58 ∷
   rw 9 q55 ∷
   rw 6 q56 ∷
   rw 3 q56 ∷
   rw 7 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2185 lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0
  q61 : Eqn
  q61 = wE 2189 W
  q62 : Eqn
  q62 = wE 2190 W

-- CA CKd20 Gad(t=0, W=(), d=SKdSKd, e=1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ : ⟪ (ℓ "久丈下丈下九中九丮上三上三") ⟫ʷ ≈ ⟪ (ℓ "三上上上上九中九丮下下下下丈久") ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ = derive (ℓ "久丈下丈下九中九丮上三上三") (ℓ "三上上上上九中九丮下下下下丈久")
  (rw 0 q49 ∷
   rw 1 q60 ∷
   rw 0 q61 ∷
   rw 9 q62 ∷
   rw 14 q53 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 2191 W
  q64 : Eqn
  q64 = sE 913 lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q65 : Eqn
  q65 = wE 2192 W

-- pass [X1 CSd10 X1] [S0 Kd0 S0 Kd0 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 K0 Sd0 K0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 : ⟪ (ℓ "丒両丒丈下丈下三九中九丮丈上三上三") ⟫ʷ ≈ ⟪ (ℓ "丈下丈下三九中九丮丈上三上三丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 = derive (ℓ "丒両丒丈下丈下三九中九丮丈上三上三") (ℓ "丈下丈下三九中九丮丈上三上三丒両丒")
  (rw 0 q63 ∷
   rw 11 q64 ∷
   rw 8 q55 ∷
   rw 5 q64 ∷
   rw 9 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 1459 W
  q67 : Eqn
  q67 = sE 2186 lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0
  q68 : Eqn
  q68 = wE 2193 W
  q69 : Eqn
  q69 = wE 2194 W
  q70 : Eqn
  q70 = wE 1461 W

-- CA CK20 Gad(t=0, W=(), d=SSKdSKdSd, e=1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ : ⟪ (ℓ "乄丈丈下丈下三九中九丮丈上三上三三") ⟫ʷ ≈ ⟪ (ℓ "三下丈下下九中九丮上上三上丈乄") ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ = derive (ℓ "乄丈丈下丈下三九中九丮丈上三上三三") (ℓ "三下丈下下九中九丮上上三上丈乄")
  (rw 0 q66 ∷
   rw 1 q67 ∷
   rw 0 q68 ∷
   rw 9 q69 ∷
   rw 14 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 2188 lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0
  q72 : Eqn
  q72 = wE 2195 W
  q73 : Eqn
  q73 = wE 2196 W

-- CA CK30 Gad(t=0, W=(), d=SdKdSKdKd, e=1): 23 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ : ⟪ (ℓ "乑三下丈下下九中九丮上上三上丈") ⟫ʷ ≈ ⟪ (ℓ "丈下丈丈九中九丮三三上三乑") ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ = derive (ℓ "乑三下丈下下九中九丮上上三上丈") (ℓ "丈下丈丈九中九丮三三上三乑")
  (rw 1 q2 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q7 ∷
   rw 1 q66 ∷
   rw⁻ 0 q11 ∷
   rw 1 q9 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   rw 1 q71 ∷
   rw 0 q72 ∷
   rw 8 q73 ∷
   rw 16 q2 ∷
   rw 15 q6 ∷
   re 14 1 (ℓ "乏久乏") ∷
   rw 16 q7 ∷
   rw 13 q6 ∷
   rw 12 q11 ∷
   rw 13 q70 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q7 ∷ []) Eq.refl
