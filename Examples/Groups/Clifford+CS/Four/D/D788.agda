{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD788 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D788 (W : Ws) (Sᴰ : SD788) where

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
  lem-b2g-0100R1 : St 3487
  lem-b2g-0100R1 = pickᴰ 0 Sᴰ
  lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS : St 3491
  lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS = pickᴰ 1 Sᴰ
  lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : St 3489
  lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 2 Sᴰ
  lem-Hc-passes-copies-X0-CS03-CS03-CK30-CS03-CX32-CS-ᵖinv : St 3492
  lem-Hc-passes-copies-X0-CS03-CS03-CK30-CS03-CX32-CS-ᵖinv = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = sE 3487 lem-b2g-0100R1
  q2 : Eqn
  q2 = wE 225 W
  q3 : Eqn
  q3 = wE 1732 W
  q4 : Eqn
  q4 = wE 116 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 1357 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 45 W
  q9 : Eqn
  q9 = wE 231 W
  q10 : Eqn
  q10 = wE 54 W
  q11 : Eqn
  q11 = wE 1726 W
  q12 : Eqn
  q12 = wE 871 W
  q13 : Eqn
  q13 = wE 2580 W
  q14 : Eqn
  q14 = wE 1510 W
  q15 : Eqn
  q15 = wE 2578 W
  q16 : Eqn
  q16 = wE 1376 W
  q17 : Eqn
  q17 = wE 1377 W
  q18 : Eqn
  q18 = wE 1378 W
  q19 : Eqn
  q19 = wE 2579 W
  q20 : Eqn
  q20 = sE 3489 lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩
  q21 : Eqn
  q21 = sE 3492 lem-Hc-passes-copies-X0-CS03-CS03-CK30-CS03-CX32-CS-ᵖinv
  q22 : Eqn
  q22 = sE 3491 lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS
  q23 : Eqn
  q23 = sE 3489 lem-Pm-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩
  q24 : Eqn
  q24 = wE 390 W
  q25 : Eqn
  q25 = wE 389 W
  q26 : Eqn
  q26 = wE 2583 W
  q27 : Eqn
  q27 = wE 2582 W
  q28 : Eqn
  q28 = wE 2581 W
  q29 : Eqn
  q29 = wE 1380 W
  q30 : Eqn
  q30 = wE 1379 W
  q31 : Eqn
  q31 = wE 1381 W
  q32 : Eqn
  q32 = wE 1509 W
  q33 : Eqn
  q33 = wE 2487 W
  q34 : Eqn
  q34 = wE 1339 W
  q35 : Eqn
  q35 = wE 227 W
  q36 : Eqn
  q36 = wE 1358 W
  q37 : Eqn
  q37 = wE 1342 W
  q38 : Eqn
  q38 = wE 1846 W
  q39 : Eqn
  q39 = wE 1728 W
  q40 : Eqn
  q40 = sE 3487 lem-b2g-0100R1

-- shift 0000R0 0100R1 X0 CS03 CS03 CK30 CS03 CX32 CS: 230 steps
lem-shift-0000R0-0100R1-X0-CS03-CS03-CK30-CS03-CX32-CS : ⟪ (ℓ "丈上中九丮九下三丒与丐丽习举习丑丏丒丌中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌") ⟫ʷ ≈ ⟪ (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丈上中九丮九下三丒与丐丽习举习丑丏丒") ⟫ʷ
lem-shift-0000R0-0100R1-X0-CS03-CS03-CK30-CS03-CX32-CS = derive (ℓ "丈上中九丮九下三丒与丐丽习举习丑丏丒丌中中乑中乖丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧临丧丧丧且乄丧丧丧丧丧丧乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧乖中中中业乑中中中中中中与临丌") (ℓ "丠丠两丠丰丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乇丽丽丽业乔丽丽丽丽丽丽丰丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业业乔丽丽丽丽丽丽丽丽丽丰丠丠丠丈两丠丠丠丠丠丠且乇丈上中九丮九下三丒与丐丽习举习丑丏丒")
  (rw 8 q1 ∷
   rw 20 q2 ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q5 ∷
   rw 24 q6 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q5 ∷
   re 24 3 (ℓ "丮") ∷
   rw 25 q7 ∷
   rw 24 q8 ∷
   rw 25 q5 ∷
   rw 26 q9 ∷
   rw 27 q5 ∷
   re 25 3 (ℓ "丮") ∷
   rw 28 q5 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q2 ∷
   rw 30 q12 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "丮") ∷
   rw 35 q7 ∷
   rw 34 q8 ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "丮") ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q7 ∷
   rw 36 q8 ∷
   rw 37 q10 ∷
   rw 38 q11 ∷
   rw 39 q12 ∷
   rw 40 q12 ∷
   rw 41 q2 ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   rw 45 q6 ∷
   rw 46 q5 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q5 ∷
   re 45 3 (ℓ "丮") ∷
   rw 46 q7 ∷
   rw 45 q8 ∷
   rw 46 q5 ∷
   rw 47 q9 ∷
   rw 48 q5 ∷
   re 46 3 (ℓ "丮") ∷
   rw 49 q5 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q7 ∷
   rw 47 q8 ∷
   rw 48 q10 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q2 ∷
   rw 52 q2 ∷
   rw 53 q13 ∷
   rw 54 q14 ∷
   rw 55 q15 ∷
   rw 56 q15 ∷
   rw 57 q16 ∷
   rw 58 q17 ∷
   rw 59 q18 ∷
   rw 60 q17 ∷
   rw 61 q13 ∷
   rw 62 q13 ∷
   rw 63 q19 ∷
   rw 64 q15 ∷
   rw 65 q2 ∷
   rw 66 q12 ∷
   rw 67 q13 ∷
   rw 68 q14 ∷
   rw 69 q15 ∷
   rw 70 q15 ∷
   rw 71 q16 ∷
   rw 72 q17 ∷
   rw 73 q18 ∷
   rw 74 q17 ∷
   rw 75 q13 ∷
   rw 76 q13 ∷
   rw 77 q19 ∷
   rw 78 q15 ∷
   rw 79 q12 ∷
   rw 80 q12 ∷
   rw 81 q2 ∷
   rw 82 q13 ∷
   rw 83 q14 ∷
   rw 84 q15 ∷
   rw 85 q15 ∷
   rw 86 q16 ∷
   rw 87 q17 ∷
   rw 88 q18 ∷
   rw 89 q17 ∷
   rw 90 q13 ∷
   rw 91 q13 ∷
   rw 92 q19 ∷
   rw 93 q15 ∷
   rw 94 q12 ∷
   rw 95 q2 ∷
   rw 0 q20 ∷
   rw⁻ 6 q21 ∷
   rw 0 q22 ∷
   rw⁻ 80 q23 ∷
   rw 175 q24 ∷
   rw 174 q25 ∷
   rw 173 q26 ∷
   rw 172 q27 ∷
   rw 171 q28 ∷
   rw 170 q28 ∷
   rw 169 q29 ∷
   rw 168 q30 ∷
   rw 167 q29 ∷
   rw 166 q31 ∷
   rw 165 q26 ∷
   rw 164 q26 ∷
   rw 163 q32 ∷
   rw 162 q28 ∷
   rw 161 q24 ∷
   rw 160 q25 ∷
   rw 159 q25 ∷
   rw 158 q26 ∷
   rw 157 q27 ∷
   rw 156 q28 ∷
   rw 155 q28 ∷
   rw 154 q29 ∷
   rw 153 q30 ∷
   rw 152 q29 ∷
   rw 151 q31 ∷
   rw 150 q26 ∷
   rw 149 q26 ∷
   rw 148 q32 ∷
   rw 147 q28 ∷
   rw 146 q25 ∷
   rw 145 q24 ∷
   rw 144 q26 ∷
   rw 143 q27 ∷
   rw 142 q28 ∷
   rw 141 q28 ∷
   rw 140 q29 ∷
   rw 139 q30 ∷
   rw 138 q29 ∷
   rw 137 q31 ∷
   rw 136 q26 ∷
   rw 135 q26 ∷
   rw 134 q32 ∷
   rw 133 q28 ∷
   rw 132 q24 ∷
   rw 131 q24 ∷
   rw 130 q25 ∷
   rw 129 q33 ∷
   rw 128 q34 ∷
   rw 127 q35 ∷
   rw 128 q5 ∷
   re 127 1 (ℓ "乏丧乏") ∷
   rw 129 q7 ∷
   re 126 1 (ℓ "乏丨乏") ∷
   rw 128 q7 ∷
   rw 127 q36 ∷
   rw 126 q7 ∷
   rw 125 q35 ∷
   rw 126 q5 ∷
   re 125 1 (ℓ "乏丨乏") ∷
   rw 127 q7 ∷
   re 124 1 (ℓ "乏丧乏") ∷
   rw 126 q7 ∷
   rw 125 q37 ∷
   rw 124 q7 ∷
   rw 123 q38 ∷
   rw 122 q39 ∷
   rw 121 q24 ∷
   rw 120 q25 ∷
   rw 119 q25 ∷
   rw 118 q33 ∷
   rw 117 q34 ∷
   rw 116 q35 ∷
   rw 117 q5 ∷
   re 116 1 (ℓ "乏丧乏") ∷
   rw 118 q7 ∷
   re 115 1 (ℓ "乏丨乏") ∷
   rw 117 q7 ∷
   rw 116 q36 ∷
   rw 115 q7 ∷
   rw 114 q35 ∷
   rw 115 q5 ∷
   re 114 1 (ℓ "乏丨乏") ∷
   rw 116 q7 ∷
   re 113 1 (ℓ "乏丧乏") ∷
   rw 115 q7 ∷
   rw 114 q37 ∷
   rw 113 q7 ∷
   rw 112 q38 ∷
   rw 111 q39 ∷
   rw 110 q25 ∷
   rw 109 q24 ∷
   rw 108 q33 ∷
   rw 107 q34 ∷
   rw 106 q35 ∷
   rw 107 q5 ∷
   re 106 1 (ℓ "乏丧乏") ∷
   rw 108 q7 ∷
   re 105 1 (ℓ "乏丨乏") ∷
   rw 107 q7 ∷
   rw 106 q36 ∷
   rw 105 q7 ∷
   rw 104 q35 ∷
   rw 105 q5 ∷
   re 104 1 (ℓ "乏丨乏") ∷
   rw 106 q7 ∷
   re 103 1 (ℓ "乏丧乏") ∷
   rw 105 q7 ∷
   rw 104 q37 ∷
   rw 103 q7 ∷
   rw 102 q38 ∷
   rw 101 q39 ∷
   rw 100 q24 ∷
   rw⁻ 88 q40 ∷ []) Eq.refl
