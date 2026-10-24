{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD596 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D596 (W : Ws) (Sᴰ : SD596) where

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
  lem-comm-CCZ123-CSd03 : St 10
  lem-comm-CCZ123-CSd03 = pickᴰ 0 Sᴰ
  lem-comm-CCZ123-CS03 : St 54
  lem-comm-CCZ123-CS03 = pickᴰ 1 Sᴰ
  lem-pass-CCZ012-vs-CZ01 : St 886
  lem-pass-CCZ012-vs-CZ01 = pickᴰ 2 Sᴰ
  lem-pass-CS02-vs-X2-TOFF012-X2 : St 1089
  lem-pass-CS02-vs-X2-TOFF012-X2 = pickᴰ 3 Sᴰ
  lem-pass-CSd02-vs-X2-TOFF012-X2 : St 1090
  lem-pass-CSd02-vs-X2-TOFF012-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 : St 1091
  lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 6 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 7 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 8 Sᴰ
  lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 : St 1094
  lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 = pickᴰ 9 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 10 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 12 Sᴰ
  lem-pass-TOFF102-vs-S0 : St 1097
  lem-pass-TOFF102-vs-S0 = pickᴰ 13 Sᴰ
  lem-pass-TOFF102-vs-Sd0 : St 1098
  lem-pass-TOFF102-vs-Sd0 = pickᴰ 14 Sᴰ
  lem-pass-TOFF102-vs-X2-TOFF012-X2 : St 1099
  lem-pass-TOFF102-vs-X2-TOFF012-X2 = pickᴰ 15 Sᴰ
  lem-pass-CS03-vs-S1 : St 663
  lem-pass-CS03-vs-S1 = pickᴰ 16 Sᴰ
  lem-pass-CS03-vs-Sd1 : St 1100
  lem-pass-CS03-vs-Sd1 = pickᴰ 17 Sᴰ
  lem-pass-CSd03-vs-CS01 : St 858
  lem-pass-CSd03-vs-CS01 = pickᴰ 18 Sᴰ
  lem-pass-CSd03-vs-CSd01 : St 859
  lem-pass-CSd03-vs-CSd01 = pickᴰ 19 Sᴰ
  lem-pass-CSd03-vs-S1 : St 664
  lem-pass-CSd03-vs-S1 = pickᴰ 20 Sᴰ
  lem-pass-CSd03-vs-Sd1 : St 1101
  lem-pass-CSd03-vs-Sd1 = pickᴰ 21 Sᴰ
  lem-pass-TOFF012-vs-S1 : St 1102
  lem-pass-TOFF012-vs-S1 = pickᴰ 22 Sᴰ
  lem-pass-TOFF012-vs-Sd1 : St 1103
  lem-pass-TOFF012-vs-Sd1 = pickᴰ 23 Sᴰ
  lem-pass-TOFF012-vs-X2-TOFF102-X2 : St 1104
  lem-pass-TOFF012-vs-X2-TOFF102-X2 = pickᴰ 24 Sᴰ
  lem-B≡F : St 1105
  lem-B≡F = pickᴰ 25 Sᴰ
  lem-CCZ123-passes-T : St 1106
  lem-CCZ123-passes-T = pickᴰ 26 Sᴰ
  lem-pass-CCZ012-vs-CCZ013 : St 1107
  lem-pass-CCZ012-vs-CCZ013 = pickᴰ 27 Sᴰ
  lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 : St 1108
  lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 28 Sᴰ
  lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 : St 1109
  lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 29 Sᴰ
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 : St 1110
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 30 Sᴰ
  lem-pass-TOFF013-vs-X2-TOFF012-X2 : St 1111
  lem-pass-TOFF013-vs-X2-TOFF012-X2 = pickᴰ 31 Sᴰ
  lem-pass-CS03-vs-TOFF013-CS02-TOFF013-CSd02 : St 1112
  lem-pass-CS03-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 32 Sᴰ
  lem-pass-CSd03-vs-TOFF013-CS02-TOFF013-CSd02 : St 1113
  lem-pass-CSd03-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 33 Sᴰ
  lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03 : St 1114
  lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-CS02-vs-CS03-TOFF012-CSd03-TOFF012 : St 1115
  lem-pass-CS02-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 35 Sᴰ
  lem-pass-CSd02-vs-CS03-TOFF012-CSd03-TOFF012 : St 1116
  lem-pass-CSd02-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 36 Sᴰ
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1117
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 37 Sᴰ
  lem-pass-TOFF012-vs-CCZ123 : St 1118
  lem-pass-TOFF012-vs-CCZ123 = pickᴰ 38 Sᴰ
  lem-pass-TOFF012-vs-CS13 : St 1119
  lem-pass-TOFF012-vs-CS13 = pickᴰ 39 Sᴰ
  lem-pass-TOFF012-vs-CSd13 : St 1120
  lem-pass-TOFF012-vs-CSd13 = pickᴰ 40 Sᴰ
  lem-pass-TOFF013-vs-CS12 : St 1121
  lem-pass-TOFF013-vs-CS12 = pickᴰ 41 Sᴰ
  lem-pass-TOFF013-vs-CSd12 : St 1122
  lem-pass-TOFF013-vs-CSd12 = pickᴰ 42 Sᴰ
  lem-pass-TOFF013-vs-X1-X2-TOFF012-X1-X2 : St 1123
  lem-pass-TOFF013-vs-X1-X2-TOFF012-X1-X2 = pickᴰ 43 Sᴰ
  lem-pass-TOFF102-vs-CS03 : St 1124
  lem-pass-TOFF102-vs-CS03 = pickᴰ 44 Sᴰ
  lem-pass-TOFF102-vs-CSd03 : St 1125
  lem-pass-TOFF102-vs-CSd03 = pickᴰ 45 Sᴰ
  lem-pass-TOFF103-vs-CS02 : St 1126
  lem-pass-TOFF103-vs-CS02 = pickᴰ 46 Sᴰ
  lem-pass-TOFF103-vs-CSd02 : St 1127
  lem-pass-TOFF103-vs-CSd02 = pickᴰ 47 Sᴰ
  lem-pass-TOFF123-vs-CS03 : St 1128
  lem-pass-TOFF123-vs-CS03 = pickᴰ 48 Sᴰ
  lem-pass-CCZ012-vs-CCZ023 : St 1129
  lem-pass-CCZ012-vs-CCZ023 = pickᴰ 49 Sᴰ
  lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 : St 1130
  lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 50 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 51 Sᴰ
  lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 : St 1132
  lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 52 Sᴰ
  lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 : St 1133
  lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 53 Sᴰ
  lem-pass-TOFF123-vs-CSd03 : St 1134
  lem-pass-TOFF123-vs-CSd03 = pickᴰ 54 Sᴰ
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1135
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 55 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1136
  lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 56 Sᴰ
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1137
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 57 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1138
  lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 58 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 1139
  lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 59 Sᴰ
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1140
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 60 Sᴰ
  lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1141
  lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 61 Sᴰ
  lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 1142
  lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 62 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 63 Sᴰ
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1144
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 64 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1145
  lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 65 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 66 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 1147
  lem-pass-X2-CK20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 67 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 1148
  lem-pass-X2-CK21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 68 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 1149
  lem-pass-X2-CKd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 69 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 1150
  lem-pass-X2-CKd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 70 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 1151
  lem-pass-X2-CSd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 71 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 1152
  lem-pass-X2-CSd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 72 Sᴰ

private
  q1 : Eqn
  q1 = sE 1106 lem-CCZ123-passes-T
  q2 : Eqn
  q2 = sE 54 lem-comm-CCZ123-CS03
  q3 : Eqn
  q3 = sE 10 lem-comm-CCZ123-CSd03

-- CCZ123 passes PP3: 4 steps
lem-CCZ123-passes-PP3 : ⟪ (ℓ "乜九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮乜") ⟫ʷ
lem-CCZ123-passes-PP3 = derive (ℓ "乜九中九丮") (ℓ "九中九丮乜")
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q1 ∷
   rw 3 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 1105 lem-B≡F
  q5 : Eqn
  q5 = wE 1725 W

-- ROT=[c,F]: 3 steps
lem-ROT≡cF : ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿") ⟫ʷ ≈ ⟪ (ℓ "临乛丵乛") ⟫ʷ
lem-ROT≡cF = derive (ℓ "临乙习丿习乙丿与临乙习丿习乙丿") (ℓ "临乛丵乛")
  (rw 1 q4 ∷
   rw 4 q4 ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 56 W
  q13 : Eqn
  q13 = wE 1441 W
  q14 : Eqn
  q14 = eqn (ℓ "丢乏") (ℓ "乏丢") (low-comm (CZ) (Swap))
  q15 : Eqn
  q15 = wE 43 W
  q16 : Eqn
  q16 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 53 W
  q18 : Eqn
  q18 = wE 1339 W
  q19 : Eqn
  q19 = sE 886 lem-pass-CCZ012-vs-CZ01
  q20 : Eqn
  q20 = sE 1107 lem-pass-CCZ012-vs-CCZ013
  q21 : Eqn
  q21 = wE 54 W
  q22 : Eqn
  q22 = wE 1442 W
  q23 : Eqn
  q23 = wE 175 W
  q24 : Eqn
  q24 = wE 55 W

-- pass [TOFF012] [X3 TOFF013 X3]: 118 steps
lem-pass-TOFF012-vs-X3-TOFF013-X3 : ⟪ (ℓ "九丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞九") ⟫ʷ
lem-pass-TOFF012-vs-X3-TOFF013-X3 = derive (ℓ "九丞乞丞") (ℓ "丞乞丞九")
  (rw 4 q6 ∷
   rw 3 q7 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q8 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q9 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q9 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q11 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q11 ∷
   rw 4 q9 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q11 ∷
   rw 2 q8 ∷
   rw 3 q12 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q7 ∷
   rw 2 q13 ∷
   rw⁻ 1 q8 ∷
   rw⁻ 2 q14 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q9 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q9 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q6 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q11 ∷
   rw⁻ 7 q9 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q11 ∷
   rw 4 q15 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw⁻ 4 q16 ∷
   rw 5 q11 ∷
   rw 0 q17 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q6 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q9 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q9 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q11 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q11 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q11 ∷
   rw 3 q15 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q14 ∷
   rw 0 q8 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q8 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q9 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q9 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q6 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q11 ∷
   rw⁻ 4 q9 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q11 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q11 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q12 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q23 ∷
   rw 3 q11 ∷
   rw 3 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 1108 lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CS02]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS02 : ⟪ (ℓ "九中九丮丧") ⟫ʷ ≈ ⟪ (ℓ "丧九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS02 = derive (ℓ "九中九丮丧") (ℓ "丧九中九丮")
  (rw⁻ 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 1109 lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CSd02]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd02 : ⟪ (ℓ "九中九丮丨") ⟫ʷ ≈ ⟪ (ℓ "丨九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd02 = derive (ℓ "九中九丮丨") (ℓ "丨九中九丮")
  (rw⁻ 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = sE 1090 lem-pass-CSd02-vs-X2-TOFF012-X2
  q28 : Eqn
  q28 = sE 1111 lem-pass-TOFF013-vs-X2-TOFF012-X2
  q29 : Eqn
  q29 = sE 1089 lem-pass-CS02-vs-X2-TOFF012-X2

-- pass [TOFF013 CS02 TOFF013 CSd02] [X2 TOFF012 X2]: 4 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X2-TOFF012-X2 : ⟪ (ℓ "乞丧乞丨丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X2-TOFF012-X2 = derive (ℓ "乞丧乞丨丘九丘") (ℓ "丘九丘乞丧乞丨")
  (rw 3 q27 ∷
   rw 2 q28 ∷
   rw 1 q29 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 1110 lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [S0]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 : ⟪ (ℓ "九中九丮丈") ⟫ʷ ≈ ⟪ (ℓ "丈九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 = derive (ℓ "九中九丮丈") (ℓ "丈九中九丮")
  (rw⁻ 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 1113 lem-pass-CSd03-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [CSd03]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CSd03 : ⟪ (ℓ "乞丧乞丨丮") ⟫ʷ ≈ ⟪ (ℓ "丮乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CSd03 = derive (ℓ "乞丧乞丨丮") (ℓ "丮乞丧乞丨")
  (rw⁻ 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1114 lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [Sd0]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 : ⟪ (ℓ "九中九丮三") ⟫ʷ ≈ ⟪ (ℓ "三九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 = derive (ℓ "九中九丮三") (ℓ "三九中九丮")
  (rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1112 lem-pass-CS03-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [CS03]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CS03 : ⟪ (ℓ "乞丧乞丨中") ⟫ʷ ≈ ⟪ (ℓ "中乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CS03 = derive (ℓ "乞丧乞丨中") (ℓ "中乞丧乞丨")
  (rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1094 lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2
  q35 : Eqn
  q35 = sE 1123 lem-pass-TOFF013-vs-X1-X2-TOFF012-X1-X2
  q36 : Eqn
  q36 = sE 1091 lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2

-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X2 TOFF012 X1 X2]: 4 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-TOFF012-X1-X2 : ⟪ (ℓ "乞丧乞丨丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-TOFF012-X1-X2 = derive (ℓ "乞丧乞丨丒丘九丒丘") (ℓ "丒丘九丒丘乞丧乞丨")
  (rw 3 q34 ∷
   rw 2 q35 ∷
   rw 1 q36 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 1121 lem-pass-TOFF013-vs-CS12

-- pass [CS12] [TOFF013]: 1 steps
lem-pass-CS12-vs-TOFF013 : ⟪ (ℓ "丶乞") ⟫ʷ ≈ ⟪ (ℓ "乞丶") ⟫ʷ
lem-pass-CS12-vs-TOFF013 = derive (ℓ "丶乞") (ℓ "乞丶")
  (rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 1122 lem-pass-TOFF013-vs-CSd12

-- pass [CSd12] [TOFF013]: 1 steps
lem-pass-CSd12-vs-TOFF013 : ⟪ (ℓ "丷乞") ⟫ʷ ≈ ⟪ (ℓ "乞丷") ⟫ʷ
lem-pass-CSd12-vs-TOFF013 = derive (ℓ "丷乞") (ℓ "乞丷")
  (rw⁻ 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 1099 lem-pass-TOFF102-vs-X2-TOFF012-X2
  q40 : Eqn
  q40 = sE 1097 lem-pass-TOFF102-vs-S0
  q41 : Eqn
  q41 = sE 1125 lem-pass-TOFF102-vs-CSd03
  q42 : Eqn
  q42 = sE 1098 lem-pass-TOFF102-vs-Sd0
  q43 : Eqn
  q43 = sE 1124 lem-pass-TOFF102-vs-CS03

-- pass [TOFF102] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 6 steps
lem-pass-TOFF102-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (ℓ "习丘九丘丈丮丘九丘三中") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丈丮丘九丘三中习") ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (ℓ "习丘九丘丈丮丘九丘三中") (ℓ "丘九丘丈丮丘九丘三中习")
  (rw 0 q39 ∷
   rw 3 q40 ∷
   rw 4 q41 ∷
   rw 5 q39 ∷
   rw 8 q42 ∷
   rw 9 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 1119 lem-pass-TOFF012-vs-CS13

-- pass [CS13] [TOFF012]: 1 steps
lem-pass-CS13-vs-TOFF012 : ⟪ (ℓ "丽九") ⟫ʷ ≈ ⟪ (ℓ "九丽") ⟫ʷ
lem-pass-CS13-vs-TOFF012 = derive (ℓ "丽九") (ℓ "九丽")
  (rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 1120 lem-pass-TOFF012-vs-CSd13

-- pass [CSd13] [TOFF012]: 1 steps
lem-pass-CSd13-vs-TOFF012 : ⟪ (ℓ "举九") ⟫ʷ ≈ ⟪ (ℓ "九举") ⟫ʷ
lem-pass-CSd13-vs-TOFF012 = derive (ℓ "举九") (ℓ "九举")
  (rw⁻ 0 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1726 W
  q47 : Eqn
  q47 = wE 1727 W
  q48 : Eqn
  q48 = sE 1110 lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03
  q49 : Eqn
  q49 = wE 1728 W

-- spell Gad(t=0, W=(), d=1, e=1) -> Gad(t=0, W=(), d=Sd, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ : ⟪ (ℓ "九中九丮") ⟫ʷ ≈ ⟪ (ℓ "三九中九丮丈") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ = derive (ℓ "九中九丮") (ℓ "三九中九丮丈")
  (rw 0 q46 ∷
   rw 6 q46 ∷
   rw 1 q47 ∷
   rw 1 q48 ∷
   rw 5 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1729 W
  q51 : Eqn
  q51 = wE 1730 W

-- spell Gad(t=0, W=(), d=SSKdSd, e=1) -> Gad(t=0, W=(), d=SSKdSS, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSS-e≡1⟩ : ⟪ (ℓ "丈丈下三九中九丮丈上三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈丈九中九丮三三上三三") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSS-e≡1⟩ = derive (ℓ "丈丈下三九中九丮丈上三三") (ℓ "丈丈下丈丈九中九丮三三上三三")
  (rw 0 q50 ∷
   rw 10 q51 ∷
   rw 5 q47 ∷
   rw 5 q48 ∷
   rw 9 q49 ∷ []) Eq.refl

-- pass [TOFF102] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 6 steps
lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (ℓ "习丈丮丘九丘三中丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丈丮丘九丘三中丘九丘习") ⟫ʷ
lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (ℓ "习丈丮丘九丘三中丘九丘") (ℓ "丈丮丘九丘三中丘九丘习")
  (rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q39 ∷
   rw 5 q42 ∷
   rw 6 q43 ∷
   rw 7 q39 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 1124 lem-pass-TOFF102-vs-CS03
  q53 : Eqn
  q53 = sE 663 lem-pass-CS03-vs-S1
  q54 : Eqn
  q54 = sE 1095 lem-pass-CSd13-vs-CS03
  q55 : Eqn
  q55 = sE 1100 lem-pass-CS03-vs-Sd1
  q56 : Eqn
  q56 = sE 1092 lem-pass-CS13-vs-CS03

-- pass [CS03] [TOFF102 S1 CSd13 TOFF102 Sd1 CS13]: 6 steps
lem-pass-CS03-vs-TOFF102-S1-CSd13-TOFF102-Sd1-CS13 : ⟪ (ℓ "中习与举习丏丽") ⟫ʷ ≈ ⟪ (ℓ "习与举习丏丽中") ⟫ʷ
lem-pass-CS03-vs-TOFF102-S1-CSd13-TOFF102-Sd1-CS13 = derive (ℓ "中习与举习丏丽") (ℓ "习与举习丏丽中")
  (rw⁻ 0 q52 ∷
   rw 1 q53 ∷
   rw⁻ 2 q54 ∷
   rw⁻ 3 q52 ∷
   rw 4 q55 ∷
   rw⁻ 5 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 1128 lem-pass-TOFF123-vs-CS03

-- pass [CS03] [TOFF123]: 1 steps
lem-pass-CS03-vs-TOFF123 : ⟪ (ℓ "中乢") ⟫ʷ ≈ ⟪ (ℓ "乢中") ⟫ʷ
lem-pass-CS03-vs-TOFF123 = derive (ℓ "中乢") (ℓ "乢中")
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 1126 lem-pass-TOFF103-vs-CS02

-- pass [CS02] [TOFF103]: 1 steps
lem-pass-CS02-vs-TOFF103 : ⟪ (ℓ "丧乡") ⟫ʷ ≈ ⟪ (ℓ "乡丧") ⟫ʷ
lem-pass-CS02-vs-TOFF103 = derive (ℓ "丧乡") (ℓ "乡丧")
  (rw⁻ 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 1127 lem-pass-TOFF103-vs-CSd02

-- pass [CSd02] [TOFF103]: 1 steps
lem-pass-CSd02-vs-TOFF103 : ⟪ (ℓ "丨乡") ⟫ʷ ≈ ⟪ (ℓ "乡丨") ⟫ʷ
lem-pass-CSd02-vs-TOFF103 = derive (ℓ "丨乡") (ℓ "乡丨")
  (rw⁻ 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 1115 lem-pass-CS02-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CS02]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 : ⟪ (ℓ "中九丮九丧") ⟫ʷ ≈ ⟪ (ℓ "丧中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 = derive (ℓ "中九丮九丧") (ℓ "丧中九丮九")
  (rw⁻ 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 1116 lem-pass-CSd02-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CSd02]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 : ⟪ (ℓ "中九丮九丨") ⟫ʷ ≈ ⟪ (ℓ "丨中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 = derive (ℓ "中九丮九丨") (ℓ "丨中九丮九")
  (rw⁻ 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1118 lem-pass-TOFF012-vs-CCZ123

-- pass [CCZ123] [TOFF012]: 1 steps
lem-pass-CCZ123-vs-TOFF012 : ⟪ (ℓ "乜九") ⟫ʷ ≈ ⟪ (ℓ "九乜") ⟫ʷ
lem-pass-CCZ123-vs-TOFF012 = derive (ℓ "乜九") (ℓ "九乜")
  (rw⁻ 0 q62 ∷ []) Eq.refl

-- pass [TOFF102] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-TOFF102-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (ℓ "习中丘九丘丮丘九丘") ⟫ʷ ≈ ⟪ (ℓ "中丘九丘丮丘九丘习") ⟫ʷ
lem-pass-TOFF102-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (ℓ "习中丘九丘丮丘九丘") (ℓ "中丘九丘丮丘九丘习")
  (rw 0 q43 ∷
   rw 1 q39 ∷
   rw 4 q41 ∷
   rw 5 q39 ∷ []) Eq.refl

-- pass [TOFF102] [X2 TOFF012 X2 CS03 X2 TOFF012 X2 CSd03]: 4 steps
lem-pass-TOFF102-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : ⟪ (ℓ "习丘九丘中丘九丘丮") ⟫ʷ ≈ ⟪ (ℓ "丘九丘中丘九丘丮习") ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = derive (ℓ "习丘九丘中丘九丘丮") (ℓ "丘九丘中丘九丘丮习")
  (rw 0 q39 ∷
   rw 3 q43 ∷
   rw 4 q39 ∷
   rw 7 q41 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1347 W
  q64 : Eqn
  q64 = wE 1731 W
  q65 : Eqn
  q65 = eqn (ℓ "下乜") (ℓ "乜下") (low₁-comm ((K • iI)) (CCZ))
  q66 : Eqn
  q66 = wE 119 W
  q67 : Eqn
  q67 = sE 1129 lem-pass-CCZ012-vs-CCZ023
  q68 : Eqn
  q68 = wE 271 W
  q69 : Eqn
  q69 = eqn (ℓ "上乜") (ℓ "乜上") (low₁-comm (K) (CCZ))
  q70 : Eqn
  q70 = wE 118 W
  q71 : Eqn
  q71 = wE 1450 W

-- pass [TOFF102] [CCZ023]: 13 steps
lem-pass-TOFF102-vs-CCZ023 : ⟪ (ℓ "习乛") ⟫ʷ ≈ ⟪ (ℓ "乛习") ⟫ʷ
lem-pass-TOFF102-vs-CCZ023 = derive (ℓ "习乛") (ℓ "乛习")
  (rw 0 q63 ∷
   re 3 1 (ℓ "並乜並") ∷
   rw 2 q64 ∷
   rw 3 q65 ∷
   rw 4 q66 ∷
   re 2 3 (ℓ "乛") ∷
   rw 1 q67 ∷
   re 1 1 (ℓ "並乜並") ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q70 ∷
   re 0 3 (ℓ "乛") ∷
   rw 1 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1732 W
  q73 : Eqn
  q73 = wE 1733 W
  q74 : Eqn
  q74 = wE 1734 W

-- spell Gad(t=0, W=(), d=1, e=1) -> Gad(t=0, W=(), d=S, e=1): 7 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ : ⟪ (ℓ "九中九丮") ⟫ʷ ≈ ⟪ (ℓ "丈九中九丮三") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ = derive (ℓ "九中九丮") (ℓ "丈九中九丮三")
  (rw 0 q72 ∷
   rw 6 q72 ∷
   rw 1 q73 ∷
   rw 3 q48 ∷
   rw 2 q48 ∷
   rw 1 q48 ∷
   rw 5 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1735 W
  q76 : Eqn
  q76 = wE 1736 W
  q77 : Eqn
  q77 = wE 1737 W
  q78 : Eqn
  q78 = wE 1738 W
  q79 : Eqn
  q79 = wE 1739 W
  q80 : Eqn
  q80 = wE 1740 W
  q81 : Eqn
  q81 = wE 1741 W

-- spell Gad(t=0, W=(), d=SK, e=1) -> Gad(t=0, W=(), d=SKdSd, e=1): 65 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ : ⟪ (ℓ "丈上九中九丮下三") ⟫ʷ ≈ ⟪ (ℓ "丈下三九中九丮丈上三") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ = derive (ℓ "丈上九中九丮下三") (ℓ "丈下三九中九丮丈上三")
  (rw 0 q75 ∷
   rw 10 q76 ∷
   rw 3 q77 ∷
   rw 6 q78 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q11 ∷
   rw 7 q10 ∷
   rw 8 q79 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q10 ∷
   rw 9 q11 ∷
   rw 8 q78 ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q11 ∷
   rw 9 q10 ∷
   rw 10 q80 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丮") ∷
   rw⁻ 10 q10 ∷
   rw 11 q11 ∷
   rw 5 q78 ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q11 ∷
   rw 6 q10 ∷
   rw 7 q79 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q10 ∷
   rw 8 q11 ∷
   rw 7 q78 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q11 ∷
   rw 8 q10 ∷
   rw 9 q80 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丮") ∷
   rw⁻ 9 q10 ∷
   rw 10 q11 ∷
   rw 4 q78 ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q11 ∷
   rw 5 q10 ∷
   rw 6 q79 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q10 ∷
   rw 7 q11 ∷
   rw 6 q78 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q11 ∷
   rw 7 q10 ∷
   rw 8 q80 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丮") ∷
   rw⁻ 8 q10 ∷
   rw 9 q11 ∷
   rw 3 q48 ∷
   rw 7 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 1742 W
  q83 : Eqn
  q83 = wE 1743 W
  q84 : Eqn
  q84 = wE 1744 W
  q85 : Eqn
  q85 = wE 1745 W

-- spell Gad(t=0, W=(), d=SK, e=1) -> Gad(t=0, W=(), d=SKSS, e=1): 6 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKSS-e≡1⟩ : ⟪ (ℓ "丈上九中九丮下三") ⟫ʷ ≈ ⟪ (ℓ "丈上丈丈九中九丮三三下三") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKSS-e≡1⟩ = derive (ℓ "丈上九中九丮下三") (ℓ "丈上丈丈九中九丮三三下三")
  (rw 0 q82 ∷
   rw 10 q83 ∷
   rw 4 q84 ∷
   rw 5 q48 ∷
   rw 4 q48 ∷
   rw 8 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 1746 W
  q87 : Eqn
  q87 = wE 1747 W

-- spell Gad(t=0, W=(), d=KdSd, e=1) -> Gad(t=0, W=(), d=KdSS, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSS-e≡1⟩ : ⟪ (ℓ "下三九中九丮丈上") ⟫ʷ ≈ ⟪ (ℓ "下丈丈九中九丮三三上") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KdSS-e≡1⟩ = derive (ℓ "下三九中九丮丈上") (ℓ "下丈丈九中九丮三三上")
  (rw 0 q86 ∷
   rw 8 q87 ∷
   rw 3 q47 ∷
   rw 3 q48 ∷
   rw 7 q49 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = sE 1117 lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [S0]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S0 : ⟪ (ℓ "中九丮九丈") ⟫ʷ ≈ ⟪ (ℓ "丈中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S0 = derive (ℓ "中九丮九丈") (ℓ "丈中九丮九")
  (rw⁻ 0 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = sE 1130 lem-pass-S0-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [S0]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-S0 : ⟪ (ℓ "乞丧乞丨丈") ⟫ʷ ≈ ⟪ (ℓ "丈乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-S0 = derive (ℓ "乞丧乞丨丈") (ℓ "丈乞丧乞丨")
  (rw⁻ 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 1132 lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [TOFF023 CS01 TOFF023 CSd01] [S0]: 1 steps
lem-pass-TOFF023-CS01-TOFF023-CSd01-vs-S0 : ⟪ (ℓ "也丠也両丈") ⟫ʷ ≈ ⟪ (ℓ "丈也丠也両") ⟫ʷ
lem-pass-TOFF023-CS01-TOFF023-CSd01-vs-S0 = derive (ℓ "也丠也両丈") (ℓ "丈也丠也両")
  (rw⁻ 0 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = sE 1133 lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [TOFF023 CS01 TOFF023 CSd01] [CSd03]: 1 steps
lem-pass-TOFF023-CS01-TOFF023-CSd01-vs-CSd03 : ⟪ (ℓ "也丠也両丮") ⟫ʷ ≈ ⟪ (ℓ "丮也丠也両") ⟫ʷ
lem-pass-TOFF023-CS01-TOFF023-CSd01-vs-CSd03 = derive (ℓ "也丠也両丮") (ℓ "丮也丠也両")
  (rw⁻ 0 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 1464 W
  q93 : Eqn
  q93 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q94 : Eqn
  q94 = wE 1465 W

-- pass [CKd30] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 23 steps
lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "乒丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞乒") ⟫ʷ
lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "乒丞中九丮九丞") (ℓ "丞中九丮九丞乒")
  (rw 2 q6 ∷
   rw 1 q7 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q11 ∷
   rw 1 q92 ∷
   rw 0 q23 ∷
   rw 1 q23 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q23 ∷
   rw 4 q11 ∷
   rw 1 q93 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏久乏") ∷
   rw 8 q11 ∷
   rw 5 q7 ∷
   rw 6 q94 ∷
   rw 5 q23 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "乒") ∷
   rw 7 q11 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 1462 W
  q96 : Eqn
  q96 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q97 : Eqn
  q97 = wE 1463 W

-- pass [CS20] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丧丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丧") ⟫ʷ
lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丧丘中九丮九丘") (ℓ "丘中九丮九丘丧")
  (rw 0 q95 ∷
   rw 1 q96 ∷
   rw 5 q97 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 1466 W
  q99 : Eqn
  q99 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q100 : Eqn
  q100 = wE 1467 W

-- pass [CSd20] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丨丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丨") ⟫ʷ
lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丨丘中九丮九丘") (ℓ "丘中九丮九丘丨")
  (rw 0 q98 ∷
   rw 1 q99 ∷
   rw 5 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 1359 W
  q102 : Eqn
  q102 = wE 1360 W
  q103 : Eqn
  q103 = wE 1361 W

-- pass [CS03] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 26 steps
lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (ℓ "中丘习丘丽丘习丘举") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丽丘习丘举中") ⟫ʷ
lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = derive (ℓ "中丘习丘丽丘习丘举") (ℓ "丘习丘丽丘习丘举中")
  (rw 1 q101 ∷
   rw 2 q6 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q11 ∷
   rw 1 q102 ∷
   rw⁻ 0 q9 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q11 ∷
   rw⁻ 1 q52 ∷
   rw 0 q103 ∷
   rw⁻ 3 q56 ∷
   rw 5 q101 ∷
   rw 6 q6 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q11 ∷
   rw 5 q102 ∷
   rw⁻ 4 q9 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q11 ∷
   rw⁻ 5 q52 ∷
   rw 4 q103 ∷
   rw⁻ 7 q54 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 1104 lem-pass-TOFF012-vs-X2-TOFF102-X2
  q105 : Eqn
  q105 = sE 1119 lem-pass-TOFF012-vs-CS13
  q106 : Eqn
  q106 = sE 1120 lem-pass-TOFF012-vs-CSd13

-- pass [TOFF012] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 4 steps
lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (ℓ "九丘习丘丽丘习丘举") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丽丘习丘举九") ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = derive (ℓ "九丘习丘丽丘习丘举") (ℓ "丘习丘丽丘习丘举九")
  (rw 0 q104 ∷
   rw 3 q105 ∷
   rw 4 q104 ∷
   rw 7 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = wE 1748 W
  q108 : Eqn
  q108 = sE 1125 lem-pass-TOFF102-vs-CSd03
  q109 : Eqn
  q109 = sE 1093 lem-pass-CS13-vs-CSd03
  q110 : Eqn
  q110 = sE 1096 lem-pass-CSd13-vs-CSd03

-- pass [CSd03] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 26 steps
lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (ℓ "丮丘习丘丽丘习丘举") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丽丘习丘举丮") ⟫ʷ
lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = derive (ℓ "丮丘习丘丽丘习丘举") (ℓ "丘习丘丽丘习丘举丮")
  (rw 1 q101 ∷
   rw 2 q6 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q11 ∷
   rw 1 q107 ∷
   rw⁻ 0 q9 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q11 ∷
   rw⁻ 1 q108 ∷
   rw 0 q103 ∷
   rw⁻ 3 q109 ∷
   rw 5 q101 ∷
   rw 6 q6 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q11 ∷
   rw 5 q107 ∷
   rw⁻ 4 q9 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q11 ∷
   rw⁻ 5 q108 ∷
   rw 4 q103 ∷
   rw⁻ 7 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = wE 5 W
  q112 : Eqn
  q112 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q113 : Eqn
  q113 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q114 : Eqn
  q114 = wE 7 W
  q115 : Eqn
  q115 = wE 1493 W
  q116 : Eqn
  q116 = wE 27 W
  q117 : Eqn
  q117 = wE 31 W
  q118 : Eqn
  q118 = wE 1490 W

-- pass [X2 CS20 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘丧丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘丧丘丞中九丮九丞") (ℓ "丞中九丮九丞丘丧丘")
  (rw 4 q111 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q114 ∷
   rw⁻ 0 q113 ∷
   rw 1 q115 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q116 ∷
   rw 3 q113 ∷
   rw 4 q117 ∷
   rw 1 q118 ∷
   rw 1 q96 ∷
   rw 5 q118 ∷
   rw 9 q111 ∷
   rw⁻ 8 q112 ∷
   rw⁻ 7 q113 ∷
   rw 6 q114 ∷
   rw⁻ 5 q113 ∷
   rw 6 q115 ∷
   rw 5 q112 ∷
   rw 6 q113 ∷
   rw 7 q116 ∷
   rw 8 q113 ∷
   rw 9 q117 ∷ []) Eq.refl

private
  q119 : Eqn
  q119 = wE 76 W
  q120 : Eqn
  q120 = wE 1499 W
  q121 : Eqn
  q121 = wE 29 W
  q122 : Eqn
  q122 = wE 1482 W

-- pass [X2 CSd20 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘丨丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘丨丘丞中九丮九丞") (ℓ "丞中九丮九丞丘丨丘")
  (rw 4 q111 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q119 ∷
   rw⁻ 0 q113 ∷
   rw 1 q120 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q121 ∷
   rw 3 q113 ∷
   rw 4 q117 ∷
   rw 1 q122 ∷
   rw 1 q99 ∷
   rw 5 q122 ∷
   rw 9 q111 ∷
   rw⁻ 8 q112 ∷
   rw⁻ 7 q113 ∷
   rw 6 q119 ∷
   rw⁻ 5 q113 ∷
   rw 6 q120 ∷
   rw 5 q112 ∷
   rw 6 q113 ∷
   rw 7 q121 ∷
   rw 8 q113 ∷
   rw 9 q117 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = wE 1474 W
  q124 : Eqn
  q124 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q125 : Eqn
  q125 = sE 1141 lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q126 : Eqn
  q126 = wE 1475 W

-- pass [CS21] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丶丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丶丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丶")
  (rw 0 q123 ∷
   rw 9 q124 ∷
   rw 1 q125 ∷
   rw 7 q126 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q127 : Eqn
  q127 = wE 1476 W
  q128 : Eqn
  q128 = sE 1136 lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q129 : Eqn
  q129 = wE 1477 W

-- pass [CK21] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "乇丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "乇丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞乇")
  (rw 0 q127 ∷
   rw 9 q124 ∷
   rw 1 q128 ∷
   rw 7 q129 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

-- pass [CS03] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 28 steps
lem-pass-CS03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (ℓ "中丘习丘与举丘习丘丏丽") ⟫ʷ ≈ ⟪ (ℓ "丘习丘与举丘习丘丏丽中") ⟫ʷ
lem-pass-CS03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (ℓ "中丘习丘与举丘习丘丏丽") (ℓ "丘习丘与举丘习丘丏丽中")
  (rw 1 q101 ∷
   rw 2 q6 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q11 ∷
   rw 1 q102 ∷
   rw⁻ 0 q9 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q11 ∷
   rw⁻ 1 q52 ∷
   rw 0 q103 ∷
   rw 3 q53 ∷
   rw⁻ 4 q54 ∷
   rw 6 q101 ∷
   rw 7 q6 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q11 ∷
   rw 6 q102 ∷
   rw⁻ 5 q9 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q11 ∷
   rw⁻ 6 q52 ∷
   rw 5 q103 ∷
   rw 8 q55 ∷
   rw⁻ 9 q56 ∷ []) Eq.refl

private
  q130 : Eqn
  q130 = sE 1102 lem-pass-TOFF012-vs-S1
  q131 : Eqn
  q131 = sE 1103 lem-pass-TOFF012-vs-Sd1

-- pass [TOFF012] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 6 steps
lem-pass-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (ℓ "九丘习丘与举丘习丘丏丽") ⟫ʷ ≈ ⟪ (ℓ "丘习丘与举丘习丘丏丽九") ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (ℓ "九丘习丘与举丘习丘丏丽") (ℓ "丘习丘与举丘习丘丏丽九")
  (rw 0 q104 ∷
   rw 3 q130 ∷
   rw 4 q106 ∷
   rw 5 q104 ∷
   rw 8 q131 ∷
   rw 9 q105 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = sE 664 lem-pass-CSd03-vs-S1
  q133 : Eqn
  q133 = sE 1101 lem-pass-CSd03-vs-Sd1

-- pass [CSd03] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 28 steps
lem-pass-CSd03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (ℓ "丮丘习丘与举丘习丘丏丽") ⟫ʷ ≈ ⟪ (ℓ "丘习丘与举丘习丘丏丽丮") ⟫ʷ
lem-pass-CSd03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (ℓ "丮丘习丘与举丘习丘丏丽") (ℓ "丘习丘与举丘习丘丏丽丮")
  (rw 1 q101 ∷
   rw 2 q6 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q11 ∷
   rw 1 q107 ∷
   rw⁻ 0 q9 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q11 ∷
   rw⁻ 1 q108 ∷
   rw 0 q103 ∷
   rw 3 q132 ∷
   rw⁻ 4 q110 ∷
   rw 6 q101 ∷
   rw 7 q6 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 7 q11 ∷
   rw 6 q107 ∷
   rw⁻ 5 q9 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q11 ∷
   rw⁻ 6 q108 ∷
   rw 5 q103 ∷
   rw 8 q133 ∷
   rw⁻ 9 q109 ∷ []) Eq.refl

private
  q134 : Eqn
  q134 = wE 1478 W
  q135 : Eqn
  q135 = sE 1138 lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q136 : Eqn
  q136 = wE 1479 W

-- pass [CKd21] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "么丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "么丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞么")
  (rw 0 q134 ∷
   rw 9 q124 ∷
   rw 1 q135 ∷
   rw 7 q136 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q137 : Eqn
  q137 = wE 1480 W
  q138 : Eqn
  q138 = sE 1145 lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q139 : Eqn
  q139 = wE 1481 W

-- pass [CSd21] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丷丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丷") ⟫ʷ
lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丷丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丷")
  (rw 0 q137 ∷
   rw 9 q124 ∷
   rw 1 q138 ∷
   rw 7 q139 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

-- pass [CSd03] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丮习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丮习丽习举") (ℓ "习丽习举丮")
  (rw⁻ 0 q108 ∷
   rw⁻ 1 q109 ∷
   rw⁻ 2 q108 ∷
   rw⁻ 3 q110 ∷ []) Eq.refl

private
  q140 : Eqn
  q140 = sE 1134 lem-pass-TOFF123-vs-CSd03
  q141 : Eqn
  q141 = sE 858 lem-pass-CSd03-vs-CS01
  q142 : Eqn
  q142 = sE 859 lem-pass-CSd03-vs-CSd01

-- pass [CSd03] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-CSd03-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (ℓ "丮乢丠乢両") ⟫ʷ ≈ ⟪ (ℓ "乢丠乢両丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF123-CS01-TOFF123-CSd01 = derive (ℓ "丮乢丠乢両") (ℓ "乢丠乢両丮")
  (rw⁻ 0 q140 ∷
   rw 1 q141 ∷
   rw⁻ 2 q140 ∷
   rw 3 q142 ∷ []) Eq.refl

private
  q143 : Eqn
  q143 = wE 1368 W
  q144 : Eqn
  q144 = sE 63 lem-pass-CS13-vs-S0
  q145 : Eqn
  q145 = sE 64 lem-pass-CSd13-vs-S0

-- pass [S0 CSd03] [TOFF102 CS13 TOFF102 CSd13]: 8 steps
lem-pass-S0-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丈丮习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丈丮") ⟫ʷ
lem-pass-S0-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丈丮习丽习举") (ℓ "习丽习举丈丮")
  (rw⁻ 1 q108 ∷
   rw 0 q143 ∷
   rw⁻ 2 q109 ∷
   rw⁻ 1 q144 ∷
   rw⁻ 3 q108 ∷
   rw 2 q143 ∷
   rw⁻ 4 q110 ∷
   rw⁻ 3 q145 ∷ []) Eq.refl

private
  q146 : Eqn
  q146 = sE 1142 lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3

-- pass [CS21] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "丶丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "丶丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞丶")
  (rw 0 q123 ∷
   rw 9 q124 ∷
   rw 1 q146 ∷
   rw 7 q126 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q147 : Eqn
  q147 = sE 1139 lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3

-- pass [CS20] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "丧丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "丧丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞丧")
  (rw 0 q95 ∷
   rw 9 q124 ∷
   rw 1 q147 ∷
   rw 7 q97 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q148 : Eqn
  q148 = wE 1407 W
  q149 : Eqn
  q149 = sE 1147 lem-pass-X2-CK20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q150 : Eqn
  q150 = wE 1408 W

-- pass [CK20] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "乄丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乄") ⟫ʷ
lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "乄丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乄")
  (rw 0 q148 ∷
   rw 9 q124 ∷
   rw 1 q149 ∷
   rw 7 q150 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q151 : Eqn
  q151 = sE 1149 lem-pass-X2-CKd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3

-- pass [CKd20] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "久丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "久丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞久")
  (rw 0 q92 ∷
   rw 9 q124 ∷
   rw 1 q151 ∷
   rw 7 q94 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q152 : Eqn
  q152 = sE 1151 lem-pass-X2-CSd20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3

-- pass [CSd20] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "丨丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "丨丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞丨")
  (rw 0 q98 ∷
   rw 9 q124 ∷
   rw 1 q152 ∷
   rw 7 q100 ∷
   rw⁻ 6 q124 ∷ []) Eq.refl

private
  q153 : Eqn
  q153 = sE 1144 lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0

-- pass [CSd21] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 3 steps
lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "丷丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘丷") ⟫ʷ
lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "丷丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘丷")
  (rw 0 q137 ∷
   rw 1 q153 ∷
   rw 9 q139 ∷ []) Eq.refl

private
  q154 : Eqn
  q154 = sE 1137 lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0

-- pass [CKd21] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 3 steps
lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "么丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘么") ⟫ʷ
lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "么丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘么")
  (rw 0 q134 ∷
   rw 1 q154 ∷
   rw 9 q136 ∷ []) Eq.refl

private
  q155 : Eqn
  q155 = sE 1135 lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0

-- pass [CK21] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 3 steps
lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "乇丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘乇") ⟫ʷ
lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "乇丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘乇")
  (rw 0 q127 ∷
   rw 1 q155 ∷
   rw 9 q129 ∷ []) Eq.refl

private
  q156 : Eqn
  q156 = sE 1140 lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0

-- pass [CS21] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 3 steps
lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "丶丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘丶") ⟫ʷ
lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "丶丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘丶")
  (rw 0 q123 ∷
   rw 1 q156 ∷
   rw 9 q126 ∷ []) Eq.refl

private
  q157 : Eqn
  q157 = sE 1152 lem-pass-X2-CSd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3

-- pass [CSd21] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丷丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丷") ⟫ʷ
lem-pass-CSd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丷丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丷")
  (rw 0 q137 ∷
   rw 13 q124 ∷
   rw 1 q157 ∷
   rw 11 q139 ∷
   rw⁻ 10 q124 ∷ []) Eq.refl

private
  q158 : Eqn
  q158 = sE 1150 lem-pass-X2-CKd21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3

-- pass [CKd21] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "么丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "么丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞么")
  (rw 0 q134 ∷
   rw 13 q124 ∷
   rw 1 q158 ∷
   rw 11 q136 ∷
   rw⁻ 10 q124 ∷ []) Eq.refl

private
  q159 : Eqn
  q159 = sE 1148 lem-pass-X2-CK21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3

-- pass [CK21] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "乇丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "乇丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞乇")
  (rw 0 q127 ∷
   rw 13 q124 ∷
   rw 1 q159 ∷
   rw 11 q129 ∷
   rw⁻ 10 q124 ∷ []) Eq.refl
