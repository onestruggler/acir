{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD622 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D622 (W : Ws) (Sᴰ : SD622) where

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
  lem-pass-CS03-vs-X3-TOFF013-X3 : St 1426
  lem-pass-CS03-vs-X3-TOFF013-X3 = pickᴰ 0 Sᴰ
  lem-pass-CSd03-vs-X3-TOFF013-X3 : St 1427
  lem-pass-CSd03-vs-X3-TOFF013-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 4 Sᴰ
  lem-pass-CS13-vs-Sd0 : St 1428
  lem-pass-CS13-vs-Sd0 = pickᴰ 5 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 6 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 7 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 8 Sᴰ
  lem-pass-CSd13-vs-Sd0 : St 1429
  lem-pass-CSd13-vs-Sd0 = pickᴰ 9 Sᴰ
  lem-pass-CS03-vs-CS01 : St 1430
  lem-pass-CS03-vs-CS01 = pickᴰ 10 Sᴰ
  lem-pass-CS03-vs-CSd01 : St 1431
  lem-pass-CS03-vs-CSd01 = pickᴰ 11 Sᴰ
  lem-ROT≡cF : St 1425
  lem-ROT≡cF = pickᴰ 12 Sᴰ
  lem-pass-CS03-vs-TOFF123 : St 1432
  lem-pass-CS03-vs-TOFF123 = pickᴰ 13 Sᴰ
  lem-pass-CS12-vs-TOFF013 : St 1433
  lem-pass-CS12-vs-TOFF013 = pickᴰ 14 Sᴰ
  lem-pass-CS13-vs-TOFF012 : St 1434
  lem-pass-CS13-vs-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-CSd12-vs-TOFF013 : St 1435
  lem-pass-CSd12-vs-TOFF013 = pickᴰ 16 Sᴰ
  lem-pass-CSd13-vs-TOFF012 : St 1436
  lem-pass-CSd13-vs-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-TOFF012-vs-X3-TOFF013-X3 : St 1437
  lem-pass-TOFF012-vs-X3-TOFF013-X3 = pickᴰ 18 Sᴰ

private
  q1 : Eqn
  q1 = sE 1425 lem-ROT≡cF
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q8 : Eqn
  q8 = wE 30 W
  q9 : Eqn
  q9 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 26 W
  q15 : Eqn
  q15 = wE 1880 W
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q19 : Eqn
  q19 = sE 1425 lem-ROT≡cF

-- SW23-ROT: 111 steps
lem-SW23-ROT : ⟪ (ℓ "乏临乙习丿习乙丿与临乙习丿习乙丿乏") ⟫ʷ ≈ ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿") ⟫ʷ
lem-SW23-ROT = derive (ℓ "乏临乙习丿习乙丿与临乙习丿习乙丿乏") (ℓ "临乙习丿习乙丿与临乙习丿习乙丿")
  (rw 1 q1 ∷
   rw 4 q2 ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   rw⁻ 0 q3 ∷
   rw 1 q4 ∷
   rw 4 q5 ∷
   rw⁻ 3 q6 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q7 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q10 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q6 ∷
   rw 7 q12 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q13 ∷
   rw⁻ 4 q9 ∷
   rw 3 q13 ∷
   rw⁻ 2 q7 ∷
   rw 3 q14 ∷
   re 3 5 (ℓ "乜") ∷
   rw⁻ 1 q6 ∷
   rw 2 q15 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q8 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q10 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q5 ∷
   rw 2 q7 ∷
   rw 3 q16 ∷
   rw 4 q9 ∷
   rw 5 q16 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q14 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q11 ∷
   rw⁻ 2 q18 ∷
   rw 3 q4 ∷
   rw 6 q5 ∷
   rw⁻ 5 q6 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q7 ∷
   rw 5 q8 ∷
   rw 6 q9 ∷
   rw 7 q8 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q11 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q9 ∷
   rw 5 q13 ∷
   rw⁻ 4 q7 ∷
   rw 5 q14 ∷
   re 5 5 (ℓ "乜") ∷
   rw⁻ 3 q6 ∷
   rw 4 q15 ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q7 ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q8 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q10 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q5 ∷
   rw 4 q7 ∷
   rw 5 q16 ∷
   rw 6 q9 ∷
   rw 7 q16 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q14 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q11 ∷
   rw⁻ 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 1427 lem-pass-CSd03-vs-X3-TOFF013-X3
  q21 : Eqn
  q21 = sE 1437 lem-pass-TOFF012-vs-X3-TOFF013-X3
  q22 : Eqn
  q22 = sE 1426 lem-pass-CS03-vs-X3-TOFF013-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF013 X3]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3 : ⟪ (ℓ "九中九丮丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3 = derive (ℓ "九中九丮丞乞丞") (ℓ "丞乞丞九中九丮")
  (rw 3 q20 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q21 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 173 W
  q24 : Eqn
  q24 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q26 : Eqn
  q26 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q27 : Eqn
  q27 = wE 56 W
  q28 : Eqn
  q28 = wE 1362 W
  q29 : Eqn
  q29 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q30 : Eqn
  q30 = wE 1382 W
  q31 : Eqn
  q31 = sE 1433 lem-pass-CS12-vs-TOFF013
  q32 : Eqn
  q32 = wE 1364 W
  q33 : Eqn
  q33 = wE 175 W

-- pass [CS12] [X3 TOFF013 X3]: 122 steps
lem-pass-CS12-vs-X3-TOFF013-X3 : ⟪ (ℓ "丶丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丶") ⟫ʷ
lem-pass-CS12-vs-X3-TOFF013-X3 = derive (ℓ "丶丞乞丞") (ℓ "丞乞丞丶")
  (rw 4 q2 ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 10 q4 ∷
   rw 9 q26 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q4 ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q4 ∷
   rw 4 q25 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q4 ∷
   rw 2 q24 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q23 ∷
   rw 2 q28 ∷
   rw⁻ 1 q29 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q2 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q25 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q4 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q25 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q26 ∷
   rw 9 q4 ∷
   rw 8 q26 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw 3 q25 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw 1 q24 ∷
   rw 2 q27 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q29 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q25 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q26 ∷
   rw 1 q2 ∷
   rw⁻ 2 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw⁻ 4 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw⁻ 6 q25 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q27 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q33 ∷
   rw 3 q4 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1881 W
  q35 : Eqn
  q35 = sE 1435 lem-pass-CSd12-vs-TOFF013

-- pass [CSd12] [X3 TOFF013 X3]: 122 steps
lem-pass-CSd12-vs-X3-TOFF013-X3 : ⟪ (ℓ "丷丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丷") ⟫ʷ
lem-pass-CSd12-vs-X3-TOFF013-X3 = derive (ℓ "丷丞乞丞") (ℓ "丞乞丞丷")
  (rw 4 q2 ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 10 q4 ∷
   rw 9 q26 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q4 ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q4 ∷
   rw 4 q25 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q4 ∷
   rw 2 q24 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q23 ∷
   rw 2 q28 ∷
   rw⁻ 1 q29 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q2 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q25 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q4 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q25 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q26 ∷
   rw 9 q4 ∷
   rw 8 q26 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw 3 q25 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw 1 q24 ∷
   rw 2 q27 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q29 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q25 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q26 ∷
   rw 1 q2 ∷
   rw⁻ 2 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw⁻ 4 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q4 ∷
   rw⁻ 6 q25 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q27 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q33 ∷
   rw 3 q4 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 1434 lem-pass-CS13-vs-TOFF012
  q37 : Eqn
  q37 = sE 63 lem-pass-CS13-vs-S0
  q38 : Eqn
  q38 = sE 1093 lem-pass-CS13-vs-CSd03
  q39 : Eqn
  q39 = sE 1428 lem-pass-CS13-vs-Sd0
  q40 : Eqn
  q40 = sE 1092 lem-pass-CS13-vs-CS03

-- pass [CS13] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 28 steps
lem-pass-CS13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (ℓ "丽丘九丘丈丮丘九丘三中") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丈丮丘九丘三中丽") ⟫ʷ
lem-pass-CS13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (ℓ "丽丘九丘丈丮丘九丘三中") (ℓ "丘九丘丈丮丘九丘三中丽")
  (rw 1 q28 ∷
   rw 2 q2 ∷
   rw 1 q29 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q4 ∷
   rw 1 q30 ∷
   rw⁻ 0 q29 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q4 ∷
   rw 1 q36 ∷
   rw 0 q32 ∷
   rw 3 q37 ∷
   rw 4 q38 ∷
   rw 6 q28 ∷
   rw 7 q2 ∷
   rw 6 q29 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q4 ∷
   rw 6 q30 ∷
   rw⁻ 5 q29 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q4 ∷
   rw 6 q36 ∷
   rw 5 q32 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 1436 lem-pass-CSd13-vs-TOFF012
  q42 : Eqn
  q42 = sE 64 lem-pass-CSd13-vs-S0
  q43 : Eqn
  q43 = sE 1096 lem-pass-CSd13-vs-CSd03
  q44 : Eqn
  q44 = sE 1429 lem-pass-CSd13-vs-Sd0
  q45 : Eqn
  q45 = sE 1095 lem-pass-CSd13-vs-CS03

-- pass [CSd13] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 28 steps
lem-pass-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (ℓ "举丘九丘丈丮丘九丘三中") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丈丮丘九丘三中举") ⟫ʷ
lem-pass-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (ℓ "举丘九丘丈丮丘九丘三中") (ℓ "丘九丘丈丮丘九丘三中举")
  (rw 1 q28 ∷
   rw 2 q2 ∷
   rw 1 q29 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q4 ∷
   rw 1 q34 ∷
   rw⁻ 0 q29 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q4 ∷
   rw 1 q41 ∷
   rw 0 q32 ∷
   rw 3 q42 ∷
   rw 4 q43 ∷
   rw 6 q28 ∷
   rw 7 q2 ∷
   rw 6 q29 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q4 ∷
   rw 6 q34 ∷
   rw⁻ 5 q29 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw 7 q4 ∷
   rw 6 q41 ∷
   rw 5 q32 ∷
   rw 8 q44 ∷
   rw 9 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q47 : Eqn
  q47 = wE 458 W
  q48 : Eqn
  q48 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q49 : Eqn
  q49 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q50 : Eqn
  q50 = wE 65 W
  q51 : Eqn
  q51 = eqn (ℓ "丳义") (ℓ "义丳") (low-comm (CX₁₀) (CS))
  q52 : Eqn
  q52 = wE 48 W
  q53 : Eqn
  q53 = wE 1386 W

-- pass [CS12] [X1 X3 TOFF013 X1 X3]: 142 steps
lem-pass-CS12-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "丶丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞丶") ⟫ʷ
lem-pass-CS12-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "丶丒丞乞丒丞") (ℓ "丒丞乞丒丞丶")
  (rw 6 q2 ∷
   rw 5 q23 ∷
   rw 4 q46 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 11 q4 ∷
   rw 10 q26 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q24 ∷
   rw 4 q27 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q23 ∷
   rw 1 q46 ∷
   rw 2 q47 ∷
   rw⁻ 1 q48 ∷
   rw⁻ 2 q29 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乐") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q24 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q25 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q24 ∷
   rw⁻ 11 q26 ∷
   rw 4 q2 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q25 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q26 ∷
   rw 5 q27 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw 5 q4 ∷
   rw⁻ 0 q49 ∷
   rw 1 q30 ∷
   re 3 1 (ℓ "乏丼丳丼乏") ∷
   rw 2 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q50 ∷
   rw⁻ 4 q51 ∷
   rw 5 q52 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q4 ∷
   re 2 5 (ℓ "乐") ∷
   rw 3 q31 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 11 q4 ∷
   rw 10 q26 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q24 ∷
   rw 4 q27 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q4 ∷
   rw 1 q29 ∷
   rw 0 q48 ∷
   rw 1 q53 ∷
   rw⁻ 0 q46 ∷
   rw 1 q33 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q2 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q25 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q46 ∷
   rw 4 q33 ∷
   rw 5 q4 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))
  q55 : Eqn
  q55 = wE 84 W
  q56 : Eqn
  q56 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q57 : Eqn
  q57 = wE 47 W

-- pass [CSd12] [X1 X3 TOFF013 X1 X3]: 142 steps
lem-pass-CSd12-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "丷丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞丷") ⟫ʷ
lem-pass-CSd12-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "丷丒丞乞丒丞") (ℓ "丒丞乞丒丞丷")
  (rw 6 q2 ∷
   rw 5 q23 ∷
   rw 4 q46 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 11 q4 ∷
   rw 10 q26 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q24 ∷
   rw 4 q27 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q23 ∷
   rw 1 q46 ∷
   rw 2 q47 ∷
   rw⁻ 1 q48 ∷
   rw⁻ 2 q29 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乐") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 4 q24 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q25 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q24 ∷
   rw⁻ 11 q26 ∷
   rw 4 q2 ∷
   rw⁻ 5 q24 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q25 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q26 ∷
   rw 5 q27 ∷
   re 5 8 (ℓ "九") ∷
   re 4 3 (ℓ "乞") ∷
   rw 5 q4 ∷
   rw⁻ 0 q54 ∷
   rw 1 q34 ∷
   re 3 1 (ℓ "乏丼丳丼乏") ∷
   rw 2 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw 3 q55 ∷
   rw⁻ 4 q56 ∷
   rw 5 q57 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   re 2 5 (ℓ "乐") ∷
   rw 3 q35 ∷
   rw 4 q2 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q25 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q25 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 11 q4 ∷
   rw 10 q26 ∷
   rw 9 q24 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   rw 7 q25 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q4 ∷
   rw 3 q24 ∷
   rw 4 q27 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q4 ∷
   rw 1 q29 ∷
   rw 0 q48 ∷
   rw 1 q53 ∷
   rw⁻ 0 q46 ∷
   rw 1 q33 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q25 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q25 ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q26 ∷
   rw 2 q2 ∷
   rw⁻ 3 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw⁻ 5 q25 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q4 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q26 ∷
   rw 3 q27 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q46 ∷
   rw 4 q33 ∷
   rw 5 q4 ∷ []) Eq.refl

-- pass [CS13] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 28 steps
lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (ℓ "丽丈丮丘九丘三中丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丈丮丘九丘三中丘九丘丽") ⟫ʷ
lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (ℓ "丽丈丮丘九丘三中丘九丘") (ℓ "丈丮丘九丘三中丘九丘丽")
  (rw 0 q37 ∷
   rw 1 q38 ∷
   rw 3 q28 ∷
   rw 4 q2 ∷
   rw 3 q29 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q4 ∷
   rw 3 q30 ∷
   rw⁻ 2 q29 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q4 ∷
   rw 3 q36 ∷
   rw 2 q32 ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   rw 8 q28 ∷
   rw 9 q2 ∷
   rw 8 q29 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q4 ∷
   rw 8 q30 ∷
   rw⁻ 7 q29 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q4 ∷
   rw 8 q36 ∷
   rw 7 q32 ∷ []) Eq.refl

-- pass [CSd13] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 28 steps
lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (ℓ "举丈丮丘九丘三中丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丈丮丘九丘三中丘九丘举") ⟫ʷ
lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (ℓ "举丈丮丘九丘三中丘九丘") (ℓ "丈丮丘九丘三中丘九丘举")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 3 q28 ∷
   rw 4 q2 ∷
   rw 3 q29 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q4 ∷
   rw 3 q34 ∷
   rw⁻ 2 q29 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw 4 q4 ∷
   rw 3 q41 ∷
   rw 2 q32 ∷
   rw 5 q44 ∷
   rw 6 q45 ∷
   rw 8 q28 ∷
   rw 9 q2 ∷
   rw 8 q29 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q4 ∷
   rw 8 q34 ∷
   rw⁻ 7 q29 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw 9 q4 ∷
   rw 8 q41 ∷
   rw 7 q32 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 1373 W
  q59 : Eqn
  q59 = wE 113 W
  q60 : Eqn
  q60 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q61 : Eqn
  q61 = wE 114 W
  q62 : Eqn
  q62 = sE 1432 lem-pass-CS03-vs-TOFF123
  q63 : Eqn
  q63 = wE 1375 W
  q64 : Eqn
  q64 = sE 1430 lem-pass-CS03-vs-CS01
  q65 : Eqn
  q65 = sE 1431 lem-pass-CS03-vs-CSd01

-- pass [CS03] [X3 TOFF123 X3 CS01 X3 TOFF123 X3 CSd01]: 26 steps
lem-pass-CS03-vs-X3-TOFF123-X3-CS01-X3-TOFF123-X3-CSd01 : ⟪ (ℓ "中丞乢丞丠丞乢丞両") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丠丞乢丞両中") ⟫ʷ
lem-pass-CS03-vs-X3-TOFF123-X3-CS01-X3-TOFF123-X3-CSd01 = derive (ℓ "中丞乢丞丠丞乢丞両") (ℓ "丞乢丞丠丞乢丞両中")
  (rw 1 q58 ∷
   re 0 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乓") ∷
   rw 3 q59 ∷
   rw 2 q60 ∷
   rw 1 q61 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q4 ∷
   re 1 5 (ℓ "中") ∷
   rw 1 q62 ∷
   rw 0 q63 ∷
   rw 3 q64 ∷
   rw 5 q58 ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "乓") ∷
   rw 7 q59 ∷
   rw 6 q60 ∷
   rw 5 q61 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 4 q4 ∷
   re 5 5 (ℓ "中") ∷
   rw 5 q62 ∷
   rw 4 q63 ∷
   rw 7 q65 ∷ []) Eq.refl

-- pass [CS03] [X3 TOFF123 X3]: 12 steps
lem-pass-CS03-vs-X3-TOFF123-X3 : ⟪ (ℓ "中丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞中") ⟫ʷ
lem-pass-CS03-vs-X3-TOFF123-X3 = derive (ℓ "中丞乢丞") (ℓ "丞乢丞中")
  (rw 1 q58 ∷
   re 0 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乓") ∷
   rw 3 q59 ∷
   rw 2 q60 ∷
   rw 1 q61 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q4 ∷
   re 1 5 (ℓ "中") ∷
   rw 1 q62 ∷
   rw 0 q63 ∷ []) Eq.refl
