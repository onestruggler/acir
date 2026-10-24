{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD544 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D544 (W : Ws) (Sᴰ : SD544) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ012-vs-CZ01 : St 886
  lem-pass-CCZ012-vs-CZ01 = pickᴰ 0 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 1 Sᴰ
  lem-pass-CS23-vs-CS01 : St 151
  lem-pass-CS23-vs-CS01 = pickᴰ 2 Sᴰ
  lem-pass-CCZ012-vs-CSd02 : St 887
  lem-pass-CCZ012-vs-CSd02 = pickᴰ 3 Sᴰ
  lem-pass-CCZ012-vs-CZ02 : St 872
  lem-pass-CCZ012-vs-CZ02 = pickᴰ 4 Sᴰ
  lem-pass-Sd1-vs-CS13 : St 888
  lem-pass-Sd1-vs-CS13 = pickᴰ 5 Sᴰ
  lem-pass-Sd1-vs-CSd13 : St 889
  lem-pass-Sd1-vs-CSd13 = pickᴰ 6 Sᴰ
  lem-pass-CS23-vs-CS02 : St 890
  lem-pass-CS23-vs-CS02 = pickᴰ 7 Sᴰ
  lem-pass-CS23-vs-CSd01 : St 152
  lem-pass-CS23-vs-CSd01 = pickᴰ 8 Sᴰ
  lem-pass-CS23-vs-CSd02 : St 891
  lem-pass-CS23-vs-CSd02 = pickᴰ 9 Sᴰ
  lem-pass-CS02-vs-CSd23 : St 892
  lem-pass-CS02-vs-CSd23 = pickᴰ 10 Sᴰ
  lem-pass-CS02-vs-CZ01 : St 893
  lem-pass-CS02-vs-CZ01 = pickᴰ 11 Sᴰ
  lem-pass-CSd02-vs-CSd23 : St 894
  lem-pass-CSd02-vs-CSd23 = pickᴰ 12 Sᴰ
  lem-pass-CSd02-vs-CZ01 : St 895
  lem-pass-CSd02-vs-CZ01 = pickᴰ 13 Sᴰ
  lem-pass-CCZ012-vs-CS01 : St 896
  lem-pass-CCZ012-vs-CS01 = pickᴰ 14 Sᴰ
  lem-pass-CCZ012-vs-CSd01 : St 897
  lem-pass-CCZ012-vs-CSd01 = pickᴰ 15 Sᴰ
  lem-pass-CS23-vs-S2 : St 898
  lem-pass-CS23-vs-S2 = pickᴰ 16 Sᴰ
  lem-pass-CS23-vs-Sd2 : St 899
  lem-pass-CS23-vs-Sd2 = pickᴰ 17 Sᴰ
  lem-pass-S2-vs-CSd23 : St 900
  lem-pass-S2-vs-CSd23 = pickᴰ 18 Sᴰ
  lem-pass-Sd2-vs-CSd23 : St 901
  lem-pass-Sd2-vs-CSd23 = pickᴰ 19 Sᴰ
  lem-pass-CCZ012-vs-CS03 : St 822
  lem-pass-CCZ012-vs-CS03 = pickᴰ 20 Sᴰ
  lem-pass-CCZ012-vs-CS13 : St 829
  lem-pass-CCZ012-vs-CS13 = pickᴰ 21 Sᴰ
  lem-pass-CCZ012-vs-CS23 : St 902
  lem-pass-CCZ012-vs-CS23 = pickᴰ 22 Sᴰ
  lem-pass-CCZ013-vs-CS23 : St 903
  lem-pass-CCZ013-vs-CS23 = pickᴰ 23 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 24 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 904
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 25 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 905
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 26 Sᴰ
  lem-pass-CCZ013-vs-CCZ123 : St 906
  lem-pass-CCZ013-vs-CCZ123 = pickᴰ 27 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 907
  lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 28 Sᴰ
  lem-pass-CCZ023-vs-CS13 : St 908
  lem-pass-CCZ023-vs-CS13 = pickᴰ 29 Sᴰ
  lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 : St 909
  lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 30 Sᴰ
  lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 : St 910
  lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 31 Sᴰ
  lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 : St 911
  lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 32 Sᴰ
  lem-pass-CCZ012-vs-CSd23 : St 912
  lem-pass-CCZ012-vs-CSd23 = pickᴰ 33 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 914
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 35 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 915
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 36 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 916
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 37 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 917
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 38 Sᴰ

private
  q1 : Eqn
  q1 = wE 1519 W
  q2 : Eqn
  q2 = sE 829 lem-pass-CCZ012-vs-CS13
  q3 : Eqn
  q3 = sE 28 lem-pass-CSd02-vs-CS13
  q4 : Eqn
  q4 = sE 888 lem-pass-Sd1-vs-CS13
  q5 : Eqn
  q5 = wE 1512 W
  q6 : Eqn
  q6 = wE 1352 W
  q7 : Eqn
  q7 = sE 887 lem-pass-CCZ012-vs-CSd02
  q8 : Eqn
  q8 = sE 872 lem-pass-CCZ012-vs-CZ02
  q9 : Eqn
  q9 = wE 1515 W
  q10 : Eqn
  q10 = wE 32 W
  q11 : Eqn
  q11 = sE 889 lem-pass-Sd1-vs-CSd13

-- pass [Sd1] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丏习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丏") ⟫ʷ
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丏习丽习举") (ℓ "习丽习举丏")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 4 q9 ∷
   rw 4 q10 ∷
   rw 3 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 1520 W
  q13 : Eqn
  q13 = wE 1521 W
  q14 : Eqn
  q14 = wE 1522 W
  q15 : Eqn
  q15 = sE 905 lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q16 : Eqn
  q16 = wE 1523 W
  q17 : Eqn
  q17 = wE 1524 W
  q18 : Eqn
  q18 = wE 1525 W

-- pass [X3 CKd32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乘丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乘丞义乣乊乣") (ℓ "义乣乊乣丞乘丞")
  (rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q13 ∷
   rw⁻ 4 q15 ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 53 W
  q20 : Eqn
  q20 = eqn (ℓ "下义") (ℓ "义下") (low₁-comm ((K • iI)) ((CS ↑)))
  q21 : Eqn
  q21 = sE 902 lem-pass-CCZ012-vs-CS23
  q22 : Eqn
  q22 = eqn (ℓ "上义") (ℓ "义上") (low₁-comm (K) ((CS ↑)))
  q23 : Eqn
  q23 = wE 55 W

-- pass [TOFF012] [CS23]: 5 steps
lem-pass-TOFF012-vs-CS23 : ⟪ (ℓ "九义") ⟫ʷ ≈ ⟪ (ℓ "义九") ⟫ʷ
lem-pass-TOFF012-vs-CS23 = derive (ℓ "九义") (ℓ "义九")
  (rw 0 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1 W
  q25 : Eqn
  q25 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 3 W
  q29 : Eqn
  q29 = wE 56 W
  q30 : Eqn
  q30 = wE 43 W
  q31 : Eqn
  q31 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q32 : Eqn
  q32 = sE 903 lem-pass-CCZ013-vs-CS23

-- pass [TOFF013] [CS23]: 109 steps
lem-pass-TOFF013-vs-CS23 : ⟪ (ℓ "乞义") ⟫ʷ ≈ ⟪ (ℓ "义乞") ⟫ʷ
lem-pass-TOFF013-vs-CS23 = derive (ℓ "乞义") (ℓ "义乞")
  (rw 1 q24 ∷
   re 0 1 (ℓ "乏九乏") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q25 ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q25 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw 0 q25 ∷
   rw 1 q29 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q19 ∷
   rw⁻ 0 q25 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q24 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q28 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q28 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q28 ∷
   rw 2 q30 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw⁻ 2 q31 ∷
   rw 3 q28 ∷
   rw 2 q20 ∷
   rw 1 q32 ∷
   rw 0 q22 ∷
   rw 4 q24 ∷
   rw 3 q31 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q28 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q28 ∷
   rw 5 q26 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q28 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q28 ∷
   rw 3 q30 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q25 ∷
   rw 2 q23 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q25 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q24 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (ℓ "下乜") (ℓ "乜下") (low₁-comm ((K • iI)) (CCZ))
  q34 : Eqn
  q34 = sE 906 lem-pass-CCZ013-vs-CCZ123
  q35 : Eqn
  q35 = eqn (ℓ "上乜") (ℓ "乜上") (low₁-comm (K) (CCZ))

-- pass [TOFF013] [CCZ123]: 109 steps
lem-pass-TOFF013-vs-CCZ123 : ⟪ (ℓ "乞乜") ⟫ʷ ≈ ⟪ (ℓ "乜乞") ⟫ʷ
lem-pass-TOFF013-vs-CCZ123 = derive (ℓ "乞乜") (ℓ "乜乞")
  (rw 1 q24 ∷
   re 0 1 (ℓ "乏九乏") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q25 ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q25 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw 0 q25 ∷
   rw 1 q29 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q19 ∷
   rw⁻ 0 q25 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q24 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q28 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q28 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q28 ∷
   rw 2 q30 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw⁻ 2 q31 ∷
   rw 3 q28 ∷
   rw 2 q33 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷
   rw 4 q24 ∷
   rw 3 q31 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q28 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q28 ∷
   rw 5 q26 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q28 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q28 ∷
   rw 3 q30 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q25 ∷
   rw 2 q23 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q25 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q24 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1526 W
  q37 : Eqn
  q37 = sE 890 lem-pass-CS23-vs-CS02
  q38 : Eqn
  q38 = sE 151 lem-pass-CS23-vs-CS01
  q39 : Eqn
  q39 = wE 1527 W
  q40 : Eqn
  q40 = wE 1528 W
  q41 : Eqn
  q41 = sE 886 lem-pass-CCZ012-vs-CZ01
  q42 : Eqn
  q42 = sE 893 lem-pass-CS02-vs-CZ01
  q43 : Eqn
  q43 = wE 1529 W
  q44 : Eqn
  q44 = sE 892 lem-pass-CS02-vs-CSd23

-- pass [CS02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丧乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丧") ⟫ʷ
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丧乣义乣乊") (ℓ "乣义乣乊丧")
  (rw 0 q36 ∷
   rw 3 q21 ∷
   rw⁻ 2 q37 ∷
   rw⁻ 1 q38 ∷
   rw 4 q39 ∷
   rw 3 q36 ∷
   rw 2 q40 ∷
   rw 6 q41 ∷
   rw 5 q42 ∷
   rw 3 q43 ∷
   rw 4 q10 ∷
   rw 3 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1530 W
  q46 : Eqn
  q46 = sE 891 lem-pass-CS23-vs-CSd02
  q47 : Eqn
  q47 = sE 152 lem-pass-CS23-vs-CSd01
  q48 : Eqn
  q48 = wE 1531 W
  q49 : Eqn
  q49 = sE 895 lem-pass-CSd02-vs-CZ01
  q50 : Eqn
  q50 = wE 1532 W
  q51 : Eqn
  q51 = sE 894 lem-pass-CSd02-vs-CSd23

-- pass [CSd02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丨乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丨") ⟫ʷ
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丨乣义乣乊") (ℓ "乣义乣乊丨")
  (rw 0 q45 ∷
   rw 3 q21 ∷
   rw⁻ 2 q46 ∷
   rw⁻ 1 q47 ∷
   rw 4 q39 ∷
   rw 3 q45 ∷
   rw 2 q48 ∷
   rw 6 q41 ∷
   rw 5 q49 ∷
   rw 3 q50 ∷
   rw 4 q10 ∷
   rw 3 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q53 : Eqn
  q53 = wE 173 W
  q54 : Eqn
  q54 = wE 1533 W
  q55 : Eqn
  q55 = wE 175 W
  q56 : Eqn
  q56 = wE 1534 W
  q57 : Eqn
  q57 = sE 907 lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X3 CK31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (ℓ "丞乔丞丌丽习举习丌") ⟫ʷ ≈ ⟪ (ℓ "丌丽习举习丌丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (ℓ "丞乔丞丌丽习举习丌") (ℓ "丌丽习举习丌丞乔丞")
  (rw 4 q24 ∷
   rw 3 q52 ∷
   rw 2 q53 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q28 ∷
   rw 0 q53 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw 1 q55 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "乔") ∷
   rw 3 q55 ∷
   rw 4 q28 ∷
   rw 1 q56 ∷
   rw 1 q57 ∷
   rw 5 q56 ∷
   rw 9 q24 ∷
   rw 8 q52 ∷
   rw 7 q53 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 8 q28 ∷
   rw 5 q53 ∷
   rw 6 q54 ∷
   rw⁻ 5 q52 ∷
   rw 6 q55 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "乔") ∷
   rw 8 q55 ∷
   rw 9 q28 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 5 W
  q59 : Eqn
  q59 = wE 121 W
  q60 : Eqn
  q60 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q61 : Eqn
  q61 = wE 30 W
  q62 : Eqn
  q62 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q63 : Eqn
  q63 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q64 : Eqn
  q64 = wE 27 W
  q65 : Eqn
  q65 = wE 122 W
  q66 : Eqn
  q66 = wE 31 W
  q67 : Eqn
  q67 = wE 127 W
  q68 : Eqn
  q68 = wE 118 W
  q69 : Eqn
  q69 = wE 7 W
  q70 : Eqn
  q70 = wE 74 W
  q71 : Eqn
  q71 = wE 125 W
  q72 : Eqn
  q72 = wE 128 W
  q73 : Eqn
  q73 = wE 24 W
  q74 : Eqn
  q74 = wE 25 W
  q75 : Eqn
  q75 = wE 26 W
  q76 : Eqn
  q76 = wE 129 W
  q77 : Eqn
  q77 = eqn (ℓ "下丽") (ℓ "丽下") (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))
  q78 : Eqn
  q78 = sE 908 lem-pass-CCZ023-vs-CS13
  q79 : Eqn
  q79 = eqn (ℓ "上丽") (ℓ "丽上") (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))
  q80 : Eqn
  q80 = wE 119 W
  q81 : Eqn
  q81 = wE 1437 W
  q82 : Eqn
  q82 = wE 123 W
  q83 : Eqn
  q83 = wE 124 W

-- pass [TOFF023] [CS13]: 117 steps
lem-pass-TOFF023-vs-CS13 : ⟪ (ℓ "也丽") ⟫ʷ ≈ ⟪ (ℓ "丽也") ⟫ʷ
lem-pass-TOFF023-vs-CS13 = derive (ℓ "也丽") (ℓ "丽也")
  (rw 1 q58 ∷
   re 0 1 (ℓ "並乢並") ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q59 ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q63 ∷
   rw 6 q64 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q59 ∷
   rw 7 q65 ∷
   rw 8 q66 ∷
   rw 7 q67 ∷
   rw 6 q68 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q63 ∷
   rw 6 q69 ∷
   rw⁻ 5 q63 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q70 ∷
   rw⁻ 3 q62 ∷
   rw 2 q70 ∷
   rw⁻ 1 q60 ∷
   rw 0 q68 ∷
   rw 1 q71 ∷
   re 1 8 (ℓ "乢") ∷
   rw 1 q72 ∷
   rw 0 q59 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q63 ∷
   rw 6 q64 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q58 ∷
   rw 2 q60 ∷
   rw 3 q73 ∷
   rw 4 q62 ∷
   rw 5 q73 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q63 ∷
   rw 7 q74 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q75 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q76 ∷
   rw 3 q66 ∷
   rw 2 q77 ∷
   rw 1 q78 ∷
   rw 0 q79 ∷
   rw 4 q58 ∷
   rw 3 q80 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q60 ∷
   rw 3 q61 ∷
   rw 4 q62 ∷
   rw 5 q61 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q63 ∷
   rw 7 q64 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q66 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q63 ∷
   rw 7 q69 ∷
   rw⁻ 6 q63 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q70 ∷
   rw⁻ 4 q62 ∷
   rw 3 q70 ∷
   rw⁻ 2 q60 ∷
   rw 3 q75 ∷
   re 3 5 (ℓ "乜") ∷
   rw 1 q68 ∷
   rw 2 q81 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q59 ∷
   rw 2 q60 ∷
   rw 3 q61 ∷
   rw 4 q62 ∷
   rw 5 q61 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q63 ∷
   rw 7 q64 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q59 ∷
   rw 8 q65 ∷
   rw 1 q58 ∷
   rw 2 q82 ∷
   rw 3 q60 ∷
   rw 4 q73 ∷
   rw 5 q62 ∷
   rw 6 q73 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q63 ∷
   rw 8 q74 ∷
   rw 9 q63 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q82 ∷
   rw 9 q83 ∷
   rw 2 q71 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q66 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 909 lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 : ⟪ (ℓ "义乣乊乣三") ⟫ʷ ≈ ⟪ (ℓ "三义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 = derive (ℓ "义乣乊乣三") (ℓ "三义乣乊乣")
  (rw⁻ 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = sE 910 lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd3]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 : ⟪ (ℓ "义乣乊乣丛") ⟫ʷ ≈ ⟪ (ℓ "丛义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 = derive (ℓ "义乣乊乣丛") (ℓ "丛义乣乊乣")
  (rw⁻ 0 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 1535 W
  q87 : Eqn
  q87 = eqn (ℓ "並丗") (ℓ "丗並") (low-comm (Swap) ((K • iI)))
  q88 : Eqn
  q88 = wE 1536 W
  q89 : Eqn
  q89 = sE 822 lem-pass-CCZ012-vs-CS03
  q90 : Eqn
  q90 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q91 : Eqn
  q91 = wE 1537 W
  q92 : Eqn
  q92 = wE 1538 W

-- pass [TOFF201] [CS03]: 33 steps
lem-pass-TOFF201-vs-CS03 : ⟪ (ℓ "乣中") ⟫ʷ ≈ ⟪ (ℓ "中乣") ⟫ʷ
lem-pass-TOFF201-vs-CS03 = derive (ℓ "乣中") (ℓ "中乣")
  (rw 0 q86 ∷
   rw 4 q58 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q63 ∷
   rw 4 q69 ∷
   rw⁻ 3 q63 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 2 q87 ∷
   rw 3 q88 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q63 ∷
   rw 3 q64 ∷
   rw 4 q63 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q87 ∷
   rw 4 q66 ∷
   rw 1 q89 ∷
   rw 2 q58 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q63 ∷
   rw 2 q69 ∷
   rw⁻ 1 q63 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 0 q90 ∷
   rw 1 q91 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q63 ∷
   rw 1 q64 ∷
   rw 2 q63 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q90 ∷
   rw 2 q66 ∷
   rw 1 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 1539 W
  q94 : Eqn
  q94 = sE 898 lem-pass-CS23-vs-S2
  q95 : Eqn
  q95 = sE 896 lem-pass-CCZ012-vs-CS01
  q96 : Eqn
  q96 = sE 900 lem-pass-S2-vs-CSd23

-- pass [S2] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "且乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊且") ⟫ʷ
lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "且乣义乣乊") (ℓ "乣义乣乊且")
  (rw 0 q93 ∷
   rw 3 q21 ∷
   rw⁻ 2 q38 ∷
   rw⁻ 1 q94 ∷
   rw 4 q39 ∷
   rw 3 q40 ∷
   rw 2 q93 ∷
   rw 5 q95 ∷
   rw 6 q41 ∷
   rw 4 q43 ∷
   rw 4 q10 ∷
   rw 3 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 1540 W
  q98 : Eqn
  q98 = sE 899 lem-pass-CS23-vs-Sd2
  q99 : Eqn
  q99 = sE 897 lem-pass-CCZ012-vs-CSd01
  q100 : Eqn
  q100 = sE 901 lem-pass-Sd2-vs-CSd23

-- pass [Sd2] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丕乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丕") ⟫ʷ
lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丕乣义乣乊") (ℓ "乣义乣乊丕")
  (rw 0 q97 ∷
   rw 3 q21 ∷
   rw⁻ 2 q47 ∷
   rw⁻ 1 q98 ∷
   rw 4 q39 ∷
   rw 3 q48 ∷
   rw 2 q97 ∷
   rw 5 q99 ∷
   rw 6 q41 ∷
   rw 4 q50 ∷
   rw 4 q10 ∷
   rw 3 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 1366 W
  q102 : Eqn
  q102 = wE 1367 W

-- pass [CK31] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 3 steps
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "乔丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "乔丞丽习举习丞") (ℓ "丞丽习举习丞乔")
  (rw 0 q101 ∷
   rw 1 q57 ∷
   rw 5 q102 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = sE 911 lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [S0]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 : ⟪ (ℓ "丽习举习丈") ⟫ʷ ≈ ⟪ (ℓ "丈丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 = derive (ℓ "丽习举习丈") (ℓ "丈丽习举习")
  (rw⁻ 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 1376 W
  q105 : Eqn
  q105 = wE 1377 W
  q106 : Eqn
  q106 = wE 1378 W
  q107 : Eqn
  q107 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q108 : Eqn
  q108 = wE 1379 W
  q109 : Eqn
  q109 = wE 1380 W
  q110 : Eqn
  q110 = wE 1381 W

-- pass [X2 CS21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丶丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丶丘丽习举习") (ℓ "丽习举习丘丶丘")
  (rw 0 q104 ∷
   rw 1 q105 ∷
   rw 2 q106 ∷
   rw 3 q105 ∷
   rw⁻ 4 q107 ∷
   rw 10 q108 ∷
   rw 9 q109 ∷
   rw 8 q110 ∷
   rw 7 q109 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = sE 904 lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CSd21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丷丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丷丘丽习举习") (ℓ "丽习举习丘丷丘")
  (rw 0 q104 ∷
   rw 1 q105 ∷
   rw 2 q106 ∷
   rw 3 q105 ∷
   rw⁻ 4 q111 ∷
   rw 10 q108 ∷
   rw 9 q109 ∷
   rw 8 q110 ∷
   rw 7 q109 ∷ []) Eq.refl

private
  q112 : Eqn
  q112 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q113 : Eqn
  q113 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q114 : Eqn
  q114 = wE 76 W
  q115 : Eqn
  q115 = wE 1499 W
  q116 : Eqn
  q116 = wE 29 W
  q117 : Eqn
  q117 = wE 1541 W
  q118 : Eqn
  q118 = sE 917 lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q119 : Eqn
  q119 = wE 1542 W

-- pass [X2 CSd20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (ℓ "丘丨丘丞丏丑与与丽习举习丏丏丐与丞") ⟫ʷ ≈ ⟪ (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (ℓ "丘丨丘丞丏丑与与丽习举习丏丏丐与丞") (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘丨丘")
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q114 ∷
   rw⁻ 0 q113 ∷
   rw 1 q115 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q116 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q117 ∷
   rw 5 q118 ∷
   rw 9 q119 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q114 ∷
   rw⁻ 13 q113 ∷
   rw 14 q115 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q116 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q120 : Eqn
  q120 = wE 137 W
  q121 : Eqn
  q121 = wE 1497 W
  q122 : Eqn
  q122 = wE 139 W
  q123 : Eqn
  q123 = wE 1543 W
  q124 : Eqn
  q124 = sE 915 lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q125 : Eqn
  q125 = wE 1544 W

-- pass [X2 CKd20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (ℓ "丘久丘丞丏丑与与丽习举习丏丏丐与丞") ⟫ʷ ≈ ⟪ (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (ℓ "丘久丘丞丏丑与与丽习举习丏丏丐与丞") (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘久丘")
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q120 ∷
   rw⁻ 0 q113 ∷
   rw 1 q121 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q122 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q123 ∷
   rw 5 q124 ∷
   rw 9 q125 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q120 ∷
   rw⁻ 13 q113 ∷
   rw 14 q121 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q122 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = wE 140 W
  q127 : Eqn
  q127 = wE 1495 W
  q128 : Eqn
  q128 = wE 142 W
  q129 : Eqn
  q129 = wE 1545 W
  q130 : Eqn
  q130 = sE 914 lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q131 : Eqn
  q131 = wE 1546 W

-- pass [X2 CK20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (ℓ "丘乄丘丞丏丑与与丽习举习丏丏丐与丞") ⟫ʷ ≈ ⟪ (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (ℓ "丘乄丘丞丏丑与与丽习举习丏丏丐与丞") (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘乄丘")
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q126 ∷
   rw⁻ 0 q113 ∷
   rw 1 q127 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q128 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q129 ∷
   rw 5 q130 ∷
   rw 9 q131 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q126 ∷
   rw⁻ 13 q113 ∷
   rw 14 q127 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q128 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = wE 1493 W
  q133 : Eqn
  q133 = wE 1547 W
  q134 : Eqn
  q134 = sE 916 lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q135 : Eqn
  q135 = wE 1548 W

-- pass [X2 CS20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (ℓ "丘丧丘丞丏丑与与丽习举习丏丏丐与丞") ⟫ʷ ≈ ⟪ (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (ℓ "丘丧丘丞丏丑与与丽习举习丏丏丐与丞") (ℓ "丞丏丑与与丽习举习丏丏丐与丞丘丧丘")
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q69 ∷
   rw⁻ 0 q113 ∷
   rw 1 q132 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q64 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q133 ∷
   rw 5 q134 ∷
   rw 9 q135 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q69 ∷
   rw⁻ 13 q113 ∷
   rw 14 q132 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q64 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q136 : Eqn
  q136 = wE 1357 W
  q137 : Eqn
  q137 = wE 45 W
  q138 : Eqn
  q138 = wE 231 W
  q139 : Eqn
  q139 = sE 913 lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q140 : Eqn
  q140 = wE 1358 W
  q141 : Eqn
  q141 = wE 227 W
  q142 : Eqn
  q142 = wE 1342 W

-- pass [X1 CSd10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丒両丒中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丒両丒中九丮九") (ℓ "中九丮九丒両丒")
  (rw 0 q24 ∷
   rw 1 q136 ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q28 ∷
   rw 1 q137 ∷
   rw 2 q24 ∷
   rw 3 q138 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q28 ∷
   rw 3 q137 ∷
   rw⁻ 4 q139 ∷
   rw 12 q24 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q28 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q28 ∷
   rw 11 q140 ∷
   rw 10 q28 ∷
   rw 9 q141 ∷
   rw 10 q24 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q28 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q28 ∷
   rw 9 q142 ∷
   rw 8 q28 ∷
   rw 7 q141 ∷ []) Eq.refl

private
  q143 : Eqn
  q143 = eqn (ℓ "下乊") (ℓ "乊下") (low₁-comm ((K • iI)) (((CS • CS • CS) ↑)))
  q144 : Eqn
  q144 = sE 912 lem-pass-CCZ012-vs-CSd23
  q145 : Eqn
  q145 = eqn (ℓ "上乊") (ℓ "乊上") (low₁-comm (K) (((CS • CS • CS) ↑)))

-- pass [TOFF012] [CSd23]: 5 steps
lem-pass-TOFF012-vs-CSd23 : ⟪ (ℓ "九乊") ⟫ʷ ≈ ⟪ (ℓ "乊九") ⟫ʷ
lem-pass-TOFF012-vs-CSd23 = derive (ℓ "九乊") (ℓ "乊九")
  (rw 0 q19 ∷
   rw 2 q143 ∷
   rw 1 q144 ∷
   rw 0 q145 ∷
   rw 1 q23 ∷ []) Eq.refl
