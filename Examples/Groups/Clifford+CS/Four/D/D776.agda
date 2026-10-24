{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD776 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D776 (W : Ws) (Sᴰ : SD776) where

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
  lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : St 3355
  lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 225 W
  q2 : Eqn
  q2 = wE 871 W
  q3 : Eqn
  q3 = wE 1732 W
  q4 : Eqn
  q4 = wE 116 W
  q5 : Eqn
  q5 = wE 45 W
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 1357 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 231 W
  q10 : Eqn
  q10 = wE 54 W
  q11 : Eqn
  q11 = wE 1726 W
  q12 : Eqn
  q12 = wE 2578 W
  q13 : Eqn
  q13 = wE 2579 W
  q14 : Eqn
  q14 = wE 1376 W
  q15 : Eqn
  q15 = wE 1377 W
  q16 : Eqn
  q16 = wE 1378 W
  q17 : Eqn
  q17 = wE 1510 W
  q18 : Eqn
  q18 = wE 2580 W
  q19 : Eqn
  q19 = sE 3355 lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3
  q20 : Eqn
  q20 = wE 390 W
  q21 : Eqn
  q21 = wE 389 W
  q22 : Eqn
  q22 = wE 2487 W
  q23 : Eqn
  q23 = wE 1339 W
  q24 : Eqn
  q24 = wE 227 W
  q25 : Eqn
  q25 = wE 1358 W
  q26 : Eqn
  q26 = wE 1342 W
  q27 : Eqn
  q27 = wE 1846 W
  q28 : Eqn
  q28 = wE 1728 W
  q29 : Eqn
  q29 = wE 2581 W
  q30 : Eqn
  q30 = wE 1509 W
  q31 : Eqn
  q31 = wE 1379 W
  q32 : Eqn
  q32 = wE 1380 W
  q33 : Eqn
  q33 = wE 1381 W
  q34 : Eqn
  q34 = wE 2582 W
  q35 : Eqn
  q35 = wE 2583 W

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X3 X2 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X3 X2 X2 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X2 X3 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X3 X3 X2 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3 X2 X2 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3 X3 X2 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X3 X2 X2 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X2 X3 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 X3]: 337 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X3-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X2-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3 : ⟪ (ℓ "与丐习丽习举丑丏丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞丞丘与丐丽习举习丑丏丞丘丘与丐丽习举习丑丏丘丞与丐丽习举习丑丏丞丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞丞丘与丐丽习举习丑丏丞丘丘与丐丽习举习丑丏丘丞与丐丽习举习丑丏丞丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞与丐习丽习举丑丏") ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X3-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X2-X2-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3-X3-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3-X2-X2-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X2-X3-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-X3 = derive (ℓ "与丐习丽习举丑丏丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞丞丘与丐丽习举习丑丏丞丘丘与丐丽习举习丑丏丘丞与丐丽习举习丑丏丞丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞") (ℓ "丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞丞丘与丐丽习举习丑丏丞丘丘与丐丽习举习丑丏丘丞与丐丽习举习丑丏丞丞丘丈上九中九丮下三丞丘丘丈上九中九丮下三丘丞丈上九中九丮下三丞与丐习丽习举丑丏")
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q8 ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丮") ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q2 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q5 ∷
   rw 16 q6 ∷
   rw 17 q7 ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "丮") ∷
   rw 18 q8 ∷
   rw 17 q5 ∷
   rw 18 q6 ∷
   rw 19 q9 ∷
   rw 20 q6 ∷
   re 18 3 (ℓ "丮") ∷
   rw 21 q6 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q8 ∷
   rw 19 q10 ∷
   rw 20 q11 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q5 ∷
   rw 26 q6 ∷
   rw 27 q7 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "丮") ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "丮") ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q8 ∷
   rw 29 q10 ∷
   rw 30 q11 ∷
   rw 31 q1 ∷
   rw 32 q1 ∷
   rw 33 q2 ∷
   rw 34 q12 ∷
   rw 35 q13 ∷
   rw 36 q14 ∷
   rw 37 q15 ∷
   rw 38 q16 ∷
   rw 39 q15 ∷
   rw 40 q17 ∷
   rw 41 q18 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   rw 44 q2 ∷
   rw 45 q12 ∷
   rw 46 q13 ∷
   rw 47 q14 ∷
   rw 48 q15 ∷
   rw 49 q16 ∷
   rw 50 q15 ∷
   rw 51 q17 ∷
   rw 52 q18 ∷
   rw 53 q2 ∷
   rw 54 q1 ∷
   rw 55 q12 ∷
   rw 56 q13 ∷
   rw 57 q14 ∷
   rw 58 q15 ∷
   rw 59 q16 ∷
   rw 60 q15 ∷
   rw 61 q17 ∷
   rw 62 q18 ∷
   rw 63 q1 ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   rw 66 q3 ∷
   rw 67 q4 ∷
   rw 68 q5 ∷
   rw 69 q6 ∷
   rw 70 q7 ∷
   rw 71 q6 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q6 ∷
   re 70 3 (ℓ "丮") ∷
   rw 71 q8 ∷
   rw 70 q5 ∷
   rw 71 q6 ∷
   rw 72 q9 ∷
   rw 73 q6 ∷
   re 71 3 (ℓ "丮") ∷
   rw 74 q6 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q8 ∷
   rw 72 q10 ∷
   rw 73 q11 ∷
   rw 74 q1 ∷
   rw 75 q2 ∷
   rw 76 q2 ∷
   rw 77 q3 ∷
   rw 78 q4 ∷
   rw 79 q5 ∷
   rw 80 q6 ∷
   rw 81 q7 ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "丮") ∷
   rw 82 q8 ∷
   rw 81 q5 ∷
   rw 82 q6 ∷
   rw 83 q9 ∷
   rw 84 q6 ∷
   re 82 3 (ℓ "丮") ∷
   rw 85 q6 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q8 ∷
   rw 83 q10 ∷
   rw 84 q11 ∷
   rw 85 q2 ∷
   rw 86 q1 ∷
   rw 87 q3 ∷
   rw 88 q4 ∷
   rw 89 q5 ∷
   rw 90 q6 ∷
   rw 91 q7 ∷
   rw 92 q6 ∷
   re 90 3 (ℓ "中") ∷
   rw 93 q6 ∷
   re 91 3 (ℓ "丮") ∷
   rw 92 q8 ∷
   rw 91 q5 ∷
   rw 92 q6 ∷
   rw 93 q9 ∷
   rw 94 q6 ∷
   re 92 3 (ℓ "丮") ∷
   rw 95 q6 ∷
   re 93 3 (ℓ "中") ∷
   rw 94 q8 ∷
   rw 93 q10 ∷
   rw 94 q11 ∷
   rw 95 q1 ∷
   rw⁻ 96 q19 ∷
   rw 199 q20 ∷
   rw 198 q21 ∷
   rw 197 q22 ∷
   rw 196 q23 ∷
   rw 195 q24 ∷
   rw 196 q6 ∷
   re 195 1 (ℓ "乏丧乏") ∷
   rw 197 q8 ∷
   re 194 1 (ℓ "乏丨乏") ∷
   rw 196 q8 ∷
   rw 195 q25 ∷
   rw 194 q8 ∷
   rw 193 q24 ∷
   rw 194 q6 ∷
   re 193 1 (ℓ "乏丨乏") ∷
   rw 195 q8 ∷
   re 192 1 (ℓ "乏丧乏") ∷
   rw 194 q8 ∷
   rw 193 q26 ∷
   rw 192 q8 ∷
   rw 191 q27 ∷
   rw 190 q28 ∷
   rw 189 q20 ∷
   rw 188 q21 ∷
   rw 187 q21 ∷
   rw 186 q22 ∷
   rw 185 q23 ∷
   rw 184 q24 ∷
   rw 185 q6 ∷
   re 184 1 (ℓ "乏丧乏") ∷
   rw 186 q8 ∷
   re 183 1 (ℓ "乏丨乏") ∷
   rw 185 q8 ∷
   rw 184 q25 ∷
   rw 183 q8 ∷
   rw 182 q24 ∷
   rw 183 q6 ∷
   re 182 1 (ℓ "乏丨乏") ∷
   rw 184 q8 ∷
   re 181 1 (ℓ "乏丧乏") ∷
   rw 183 q8 ∷
   rw 182 q26 ∷
   rw 181 q8 ∷
   rw 180 q27 ∷
   rw 179 q28 ∷
   rw 178 q21 ∷
   rw 177 q20 ∷
   rw 176 q22 ∷
   rw 175 q23 ∷
   rw 174 q24 ∷
   rw 175 q6 ∷
   re 174 1 (ℓ "乏丧乏") ∷
   rw 176 q8 ∷
   re 173 1 (ℓ "乏丨乏") ∷
   rw 175 q8 ∷
   rw 174 q25 ∷
   rw 173 q8 ∷
   rw 172 q24 ∷
   rw 173 q6 ∷
   re 172 1 (ℓ "乏丨乏") ∷
   rw 174 q8 ∷
   re 171 1 (ℓ "乏丧乏") ∷
   rw 173 q8 ∷
   rw 172 q26 ∷
   rw 171 q8 ∷
   rw 170 q27 ∷
   rw 169 q28 ∷
   rw 168 q20 ∷
   rw 167 q20 ∷
   rw 166 q21 ∷
   rw 165 q29 ∷
   rw 164 q30 ∷
   rw 163 q31 ∷
   rw 162 q32 ∷
   rw 161 q33 ∷
   rw 160 q32 ∷
   rw 159 q34 ∷
   rw 158 q35 ∷
   rw 157 q20 ∷
   rw 156 q21 ∷
   rw 155 q21 ∷
   rw 154 q29 ∷
   rw 153 q30 ∷
   rw 152 q31 ∷
   rw 151 q32 ∷
   rw 150 q33 ∷
   rw 149 q32 ∷
   rw 148 q34 ∷
   rw 147 q35 ∷
   rw 146 q21 ∷
   rw 145 q20 ∷
   rw 144 q29 ∷
   rw 143 q30 ∷
   rw 142 q31 ∷
   rw 141 q32 ∷
   rw 140 q33 ∷
   rw 139 q32 ∷
   rw 138 q34 ∷
   rw 137 q35 ∷
   rw 136 q20 ∷
   rw 135 q20 ∷
   rw 134 q21 ∷
   rw 133 q22 ∷
   rw 132 q23 ∷
   rw 131 q24 ∷
   rw 132 q6 ∷
   re 131 1 (ℓ "乏丧乏") ∷
   rw 133 q8 ∷
   re 130 1 (ℓ "乏丨乏") ∷
   rw 132 q8 ∷
   rw 131 q25 ∷
   rw 130 q8 ∷
   rw 129 q24 ∷
   rw 130 q6 ∷
   re 129 1 (ℓ "乏丨乏") ∷
   rw 131 q8 ∷
   re 128 1 (ℓ "乏丧乏") ∷
   rw 130 q8 ∷
   rw 129 q26 ∷
   rw 128 q8 ∷
   rw 127 q27 ∷
   rw 126 q28 ∷
   rw 125 q20 ∷
   rw 124 q21 ∷
   rw 123 q21 ∷
   rw 122 q22 ∷
   rw 121 q23 ∷
   rw 120 q24 ∷
   rw 121 q6 ∷
   re 120 1 (ℓ "乏丧乏") ∷
   rw 122 q8 ∷
   re 119 1 (ℓ "乏丨乏") ∷
   rw 121 q8 ∷
   rw 120 q25 ∷
   rw 119 q8 ∷
   rw 118 q24 ∷
   rw 119 q6 ∷
   re 118 1 (ℓ "乏丨乏") ∷
   rw 120 q8 ∷
   re 117 1 (ℓ "乏丧乏") ∷
   rw 119 q8 ∷
   rw 118 q26 ∷
   rw 117 q8 ∷
   rw 116 q27 ∷
   rw 115 q28 ∷
   rw 114 q21 ∷
   rw 113 q20 ∷
   rw 112 q22 ∷
   rw 111 q23 ∷
   rw 110 q24 ∷
   rw 111 q6 ∷
   re 110 1 (ℓ "乏丧乏") ∷
   rw 112 q8 ∷
   re 109 1 (ℓ "乏丨乏") ∷
   rw 111 q8 ∷
   rw 110 q25 ∷
   rw 109 q8 ∷
   rw 108 q24 ∷
   rw 109 q6 ∷
   re 108 1 (ℓ "乏丨乏") ∷
   rw 110 q8 ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw 109 q8 ∷
   rw 108 q26 ∷
   rw 107 q8 ∷
   rw 106 q27 ∷
   rw 105 q28 ∷
   rw 104 q20 ∷ []) Eq.refl
