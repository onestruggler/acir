{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD712 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D712 (W : Ws) (Sᴰ : SD712) where

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
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03 : St 2031
  lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2032
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 2 Sᴰ
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 : St 2026
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 : St 2033
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 : St 2035
  lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 = pickᴰ 6 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2036
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2037
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2039
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 : St 2040
  lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 = pickᴰ 11 Sᴰ
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 : St 2041
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 = pickᴰ 12 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2042
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 13 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2043
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 14 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1815 W
  q4 : Eqn
  q4 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 175 W
  q6 : Eqn
  q6 = sE 2040 lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0
  q7 : Eqn
  q7 = wE 2093 W
  q8 : Eqn
  q8 = wE 2094 W
  q9 : Eqn
  q9 = wE 173 W
  q10 : Eqn
  q10 = wE 1816 W

-- CA CS30 Gad(t=0, W=(), d=K, e=1): 23 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ : ⟪ (ℓ "中上九中九丮下") ⟫ʷ ≈ ⟪ (ℓ "丈上九中九丮下三中") ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ = derive (ℓ "中上九中九丮下") (ℓ "丈上九中九丮下三中")
  (rw 1 q1 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw⁻ 0 q4 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q6 ∷
   rw 0 q7 ∷
   rw 6 q8 ∷
   rw 12 q1 ∷
   rw 11 q9 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   rw 9 q9 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1709 W
  q12 : Eqn
  q12 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q13 : Eqn
  q13 = sE 2035 lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0
  q14 : Eqn
  q14 = wE 2095 W
  q15 : Eqn
  q15 = wE 2096 W
  q16 : Eqn
  q16 = wE 1711 W

-- CA CKd30 Gad(t=0, W=(), d=SK, e=1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (ℓ "乒丈上九中九丮下三") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈乒") ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (ℓ "乒丈上九中九丮下三") (ℓ "三下三九中九丮丈上丈乒")
  (rw 1 q1 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q2 ∷
   rw 1 q11 ∷
   rw⁻ 0 q12 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 7 q15 ∷
   rw 14 q1 ∷
   rw 13 q9 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q2 ∷
   rw 11 q9 ∷
   rw 10 q12 ∷
   rw 11 q16 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乒") ∷
   rw 11 q2 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 2041 lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0
  q18 : Eqn
  q18 = wE 2097 W
  q19 : Eqn
  q19 = wE 2098 W

-- CA CS30 Gad(t=0, W=(), d=SdKdSd, e=1): 23 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (ℓ "中三下三九中九丮丈上丈") ⟫ʷ ≈ ⟪ (ℓ "下三九中九丮丈上中") ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (ℓ "中三下三九中九丮丈上丈") (ℓ "下三九中九丮丈上中")
  (rw 1 q1 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw⁻ 0 q4 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q17 ∷
   rw 0 q18 ∷
   rw 6 q19 ∷
   rw 12 q1 ∷
   rw 11 q9 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   rw 9 q9 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 45 W
  q21 : Eqn
  q21 = wE 1357 W
  q22 : Eqn
  q22 = wE 231 W
  q23 : Eqn
  q23 = wE 225 W
  q24 : Eqn
  q24 = sE 2043 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q25 : Eqn
  q25 = wE 390 W
  q26 : Eqn
  q26 = wE 227 W
  q27 : Eqn
  q27 = wE 1358 W
  q28 : Eqn
  q28 = wE 1342 W

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF012 CS03 TOFF012 CSd03] ^-1: 69 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 : ⟪ (ℓ "中九丮九丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中九丮九") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 = derive (ℓ "中九丮九丞中九丮九丞") (ℓ "丞中九丮九丞中九丮九")
  (rw 10 q20 ∷
   rw 11 q1 ∷
   rw 12 q21 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q2 ∷
   rw 12 q20 ∷
   rw 13 q1 ∷
   rw 14 q22 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丮") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q2 ∷
   rw 14 q23 ∷
   rw 15 q20 ∷
   rw 16 q1 ∷
   rw 17 q21 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丮") ∷
   rw 18 q2 ∷
   rw 17 q20 ∷
   rw 18 q1 ∷
   rw 19 q22 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丮") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q2 ∷
   rw 19 q23 ∷
   rw⁻ 10 q24 ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q2 ∷
   rw 8 q27 ∷
   rw 7 q2 ∷
   rw 6 q26 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw 6 q28 ∷
   rw 5 q2 ∷
   rw 4 q25 ∷
   rw 3 q26 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q2 ∷
   rw 3 q27 ∷
   rw 2 q2 ∷
   rw 1 q26 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q28 ∷
   rw 0 q2 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1462 W
  q30 : Eqn
  q30 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q31 : Eqn
  q31 = wE 1463 W

-- pass [CS30] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 23 steps
lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "中丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中") ⟫ʷ
lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "中丞中九丮九丞") (ℓ "丞中九丮九丞中")
  (rw 2 q1 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q29 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q30 ∷
   rw 9 q1 ∷
   rw 8 q9 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q31 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q2 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q33 : Eqn
  q33 = sE 2032 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 5 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞中九丮九丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞中九丮九丞丘习丽习举丘") (ℓ "丘习丽习举丘丞中九丮九丞")
  (rw⁻ 5 q32 ∷
   rw 12 q23 ∷
   rw 1 q33 ∷
   rw⁻ 0 q32 ∷
   rw 1 q25 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 5 W
  q35 : Eqn
  q35 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q36 : Eqn
  q36 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q37 : Eqn
  q37 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q38 : Eqn
  q38 = wE 76 W
  q39 : Eqn
  q39 = wE 2063 W
  q40 : Eqn
  q40 = wE 29 W
  q41 : Eqn
  q41 = wE 31 W
  q42 : Eqn
  q42 = wE 1482 W
  q43 : Eqn
  q43 = sE 2042 lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X3 CSd30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞丮丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞丮丞丘习丽习举丘") (ℓ "丘习丽习举丘丞丮丞")
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q37 ∷
   rw 2 q38 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 0 q36 ∷
   rw 1 q39 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q37 ∷
   rw 3 q40 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q42 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q43 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q42 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw⁻ 8 q37 ∷
   rw 7 q38 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 5 q36 ∷
   rw 6 q39 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q37 ∷
   rw 8 q40 ∷
   rw 9 q37 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 137 W
  q45 : Eqn
  q45 = wE 1677 W
  q46 : Eqn
  q46 = wE 139 W
  q47 : Eqn
  q47 = wE 1485 W
  q48 : Eqn
  q48 = sE 2037 lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X3 CKd30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞乒丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞乒丞丘习丽习举丘") (ℓ "丘习丽习举丘丞乒丞")
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw⁻ 3 q37 ∷
   rw 2 q44 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 0 q36 ∷
   rw 1 q45 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q37 ∷
   rw 3 q46 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q47 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q48 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏久乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q47 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乒") ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (ℓ "乏久乏") ∷
   rw⁻ 8 q37 ∷
   rw 7 q44 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (ℓ "乕") ∷
   rw⁻ 5 q36 ∷
   rw 6 q45 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (ℓ "乏么乏") ∷
   rw 7 q37 ∷
   rw 8 q46 ∷
   rw 9 q37 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 140 W
  q50 : Eqn
  q50 = wE 1412 W
  q51 : Eqn
  q51 = wE 142 W
  q52 : Eqn
  q52 = wE 1413 W
  q53 : Eqn
  q53 = sE 2036 lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X3 CK30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞乑丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞乑丞丘习丽习举丘") (ℓ "丘习丽习举丘丞乑丞")
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q37 ∷
   rw 2 q49 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (ℓ "乔") ∷
   rw⁻ 0 q36 ∷
   rw 1 q50 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q37 ∷
   rw 3 q51 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q52 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q53 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q52 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q37 ∷
   rw 7 q49 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (ℓ "乔") ∷
   rw⁻ 5 q36 ∷
   rw 6 q50 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q37 ∷
   rw 8 q51 ∷
   rw 9 q37 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 7 W
  q55 : Eqn
  q55 = wE 2064 W
  q56 : Eqn
  q56 = wE 27 W
  q57 : Eqn
  q57 = wE 1490 W
  q58 : Eqn
  q58 = sE 2039 lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X3 CS30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞中丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞中丞丘习丽习举丘") (ℓ "丘习丽习举丘丞中丞")
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q37 ∷
   rw 2 q54 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 0 q36 ∷
   rw 1 q55 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q37 ∷
   rw 3 q56 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q57 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q58 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q57 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q37 ∷
   rw 7 q54 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 5 q36 ∷
   rw 6 q55 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q37 ∷
   rw 8 q56 ∷
   rw 9 q37 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q60 : Eqn
  q60 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q61 : Eqn
  q61 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q62 : Eqn
  q62 = wE 196 W
  q63 : Eqn
  q63 = wE 1778 W
  q64 : Eqn
  q64 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q65 : Eqn
  q65 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))
  q66 : Eqn
  q66 = sE 2033 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12
  q67 : Eqn
  q67 = wE 1777 W

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF103 CS12 TOFF103 CSd12]: 249 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丞九中九丮丞乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丞九中九丮丞") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丞九中九丮丞乡丶乡丷") (ℓ "乡丶乡丷丞九中九丮丞")
  (rw 7 q1 ∷
   re 6 1 (ℓ "乏习乏") ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 6 q59 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q60 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q59 ∷
   rw⁻ 13 q61 ∷
   rw 14 q2 ∷
   rw 13 q61 ∷
   rw 12 q59 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   rw 10 q60 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q2 ∷
   rw 8 q60 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q2 ∷
   rw 6 q59 ∷
   rw 7 q62 ∷
   re 7 8 (ℓ "习") ∷
   rw 5 q9 ∷
   rw 6 q63 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 6 q59 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q60 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q59 ∷
   rw⁻ 13 q61 ∷
   rw 6 q1 ∷
   rw⁻ 7 q59 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw⁻ 9 q60 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q2 ∷
   rw⁻ 11 q60 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q2 ∷
   rw⁻ 13 q59 ∷
   rw⁻ 14 q61 ∷
   rw 7 q62 ∷
   re 7 8 (ℓ "习") ∷
   re 6 3 (ℓ "乡") ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q64 ∷
   rw 11 q1 ∷
   re 10 1 (ℓ "乏习乏") ∷
   re 11 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 10 q59 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q60 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q60 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q59 ∷
   rw⁻ 17 q61 ∷
   rw 18 q2 ∷
   rw 17 q61 ∷
   rw 16 q59 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q2 ∷
   rw 14 q60 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q2 ∷
   rw 12 q60 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 10 q59 ∷
   rw 11 q62 ∷
   re 11 8 (ℓ "习") ∷
   rw 9 q9 ∷
   rw 10 q63 ∷
   rw 9 q5 ∷
   re 11 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 10 q59 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q60 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q60 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q59 ∷
   rw⁻ 17 q61 ∷
   rw 10 q1 ∷
   rw⁻ 11 q59 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q2 ∷
   rw⁻ 13 q60 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q2 ∷
   rw⁻ 15 q60 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q2 ∷
   rw⁻ 17 q59 ∷
   rw⁻ 18 q61 ∷
   rw 11 q62 ∷
   re 11 8 (ℓ "习") ∷
   re 10 3 (ℓ "乡") ∷
   rw 11 q5 ∷
   rw 12 q5 ∷
   rw 13 q2 ∷
   rw⁻ 12 q65 ∷
   rw 1 q66 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q59 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q59 ∷
   rw⁻ 9 q61 ∷
   rw 10 q2 ∷
   rw 9 q61 ∷
   rw 8 q59 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   rw 6 q60 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q2 ∷
   rw 4 q60 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 2 q59 ∷
   rw 3 q62 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q67 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q59 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q60 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q59 ∷
   rw⁻ 7 q61 ∷
   rw 0 q1 ∷
   rw⁻ 1 q59 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q2 ∷
   rw⁻ 3 q60 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q2 ∷
   rw⁻ 5 q60 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw⁻ 7 q59 ∷
   rw⁻ 8 q61 ∷
   rw 1 q62 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 1 q5 ∷
   rw 2 q2 ∷
   rw⁻ 1 q64 ∷
   rw 6 q1 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q59 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q59 ∷
   rw⁻ 11 q61 ∷
   rw 12 q2 ∷
   rw 11 q61 ∷
   rw 10 q59 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q2 ∷
   rw 8 q60 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q2 ∷
   rw 6 q60 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q2 ∷
   rw 4 q59 ∷
   rw 5 q62 ∷
   re 5 8 (ℓ "习") ∷
   rw 3 q9 ∷
   rw 2 q9 ∷
   rw 3 q67 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q59 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q59 ∷
   rw⁻ 9 q61 ∷
   rw 2 q1 ∷
   rw⁻ 3 q59 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   rw⁻ 5 q60 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q2 ∷
   rw⁻ 7 q60 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw⁻ 9 q59 ∷
   rw⁻ 10 q61 ∷
   rw 3 q62 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw⁻ 3 q65 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 2026 lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03
  q69 : Eqn
  q69 = sE 2031 lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03

-- MBi a0: 2 steps
lem-MBi-a0 : ⟪ (ℓ "乚丮九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮乚丮") ⟫ʷ
lem-MBi-a0 = derive (ℓ "乚丮九中九丮") (ℓ "九中九丮乚丮")
  (rw 1 q68 ∷
   rw 0 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 2099 W
  q71 : Eqn
  q71 = wE 2100 W
  q72 : Eqn
  q72 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q73 : Eqn
  q73 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q74 : Eqn
  q74 = wE 2101 W

-- ca-split Gad(t=0, W=(), d=SK, e=-1) 2: 5 steps
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : ⟪ (ℓ "丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丧乄中九丮九久丨") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = derive (ℓ "丈上中九丮九下三") (ℓ "丧乄中九丮九久丨")
  (rw 0 q70 ∷
   rw 12 q71 ∷
   rw 5 q72 ∷
   rw 2 q73 ∷
   rw 6 q74 ∷ []) Eq.refl
