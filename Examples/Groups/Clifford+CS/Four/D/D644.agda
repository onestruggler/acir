{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD644 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D644 (W : Ws) (Sᴰ : SD644) where

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
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS03-vs-S1 : St 663
  lem-pass-CS03-vs-S1 = pickᴰ 2 Sᴰ
  lem-pass-CSd03-vs-S1 : St 664
  lem-pass-CSd03-vs-S1 = pickᴰ 3 Sᴰ
  lem-pass-CS03-vs-CZ13 : St 1341
  lem-pass-CS03-vs-CZ13 = pickᴰ 4 Sᴰ
  lem-pass-CSd03-vs-CZ13 : St 1347
  lem-pass-CSd03-vs-CZ13 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 6 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 7 Sᴰ
  lem-pass-TOFF012-vs-CZ13 : St 1363
  lem-pass-TOFF012-vs-CZ13 = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-TOFF012 : St 1444
  lem-pass-CCZ123-vs-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-CSd13-vs-TOFF012 : St 1436
  lem-pass-CSd13-vs-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : St 1572
  lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = pickᴰ 11 Sᴰ
  lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : St 1573
  lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = pickᴰ 12 Sᴰ
  lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : St 1574
  lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = pickᴰ 13 Sᴰ
  lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : St 1575
  lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = pickᴰ 14 Sᴰ
  lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : St 1576
  lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = pickᴰ 15 Sᴰ
  lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : St 1577
  lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = pickᴰ 16 Sᴰ
  lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 1578
  lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 17 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : St 1579
  lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = pickᴰ 18 Sᴰ
  lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 1580
  lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 19 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 1581
  lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 20 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 1582
  lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 21 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : St 1583
  lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = pickᴰ 22 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 1584
  lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 23 Sᴰ
  lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : St 1585
  lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 24 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 : St 1586
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 = pickᴰ 25 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 : St 1587
  lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 = pickᴰ 26 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : St 1588
  lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = pickᴰ 27 Sᴰ

private
  q1 : Eqn
  q1 = sE 1095 lem-pass-CSd13-vs-CS03
  q2 : Eqn
  q2 = sE 1436 lem-pass-CSd13-vs-TOFF012
  q3 : Eqn
  q3 = sE 1096 lem-pass-CSd13-vs-CSd03

-- pass [CSd13] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "举中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九举") ⟫ʷ
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "举中九丮九") (ℓ "中九丮九举")
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q2 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 663 lem-pass-CS03-vs-S1
  q5 : Eqn
  q5 = wE 1418 W
  q6 : Eqn
  q6 = sE 664 lem-pass-CSd03-vs-S1

-- pass [S1 CSd13] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "与举中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九与举") ⟫ʷ
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "与举中九丮九") (ℓ "中九丮九与举")
  (rw 1 q1 ∷
   rw⁻ 0 q4 ∷
   rw 2 q2 ∷
   rw 1 q5 ∷
   rw 3 q3 ∷
   rw⁻ 2 q6 ∷
   rw 4 q2 ∷
   rw 3 q5 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = sE 1576 lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2
  q8 : Eqn
  q8 = sE 1574 lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2
  q9 : Eqn
  q9 = sE 1572 lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2

-- pass [CS03 TOFF012 CSd03 TOFF012] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (ℓ "中九丮九丽丘习丘举丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丽丘习丘举丘习丘中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = derive (ℓ "中九丮九丽丘习丘举丘习丘") (ℓ "丽丘习丘举丘习丘中九丮九")
  (rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q7 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = sE 1577 lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2
  q11 : Eqn
  q11 = sE 1575 lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2
  q12 : Eqn
  q12 = sE 1573 lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2

-- pass [CS03 TOFF012 CSd03 TOFF012] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (ℓ "中九丮九与举丘习丘丏丽丘习丘") ⟫ʷ ≈ ⟪ (ℓ "与举丘习丘丏丽丘习丘中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = derive (ℓ "中九丮九与举丘习丘丏丽丘习丘") (ℓ "与举丘习丘丏丽丘习丘中九丮九")
  (rw 3 q10 ∷
   rw 2 q11 ∷
   rw 1 q10 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 843 lem-pass-CCZ123-vs-CS03
  q14 : Eqn
  q14 = sE 1341 lem-pass-CS03-vs-CZ13
  q15 : Eqn
  q15 = sE 1444 lem-pass-CCZ123-vs-TOFF012
  q16 : Eqn
  q16 = sE 1363 lem-pass-TOFF012-vs-CZ13
  q17 : Eqn
  q17 = sE 861 lem-pass-CCZ123-vs-CSd03
  q18 : Eqn
  q18 = sE 1347 lem-pass-CSd03-vs-CZ13

-- pass [CZ13 CCZ123] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丿乜中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丿乜") ⟫ʷ
lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丿乜中九丮九") (ℓ "中九丮九丿乜")
  (rw 1 q13 ∷
   rw⁻ 0 q14 ∷
   rw 2 q15 ∷
   rw⁻ 1 q16 ∷
   rw 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw 4 q15 ∷
   rw⁻ 3 q16 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = wE 1459 W
  q22 : Eqn
  q22 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = wE 175 W
  q24 : Eqn
  q24 = sE 1583 lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2
  q25 : Eqn
  q25 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q26 : Eqn
  q26 = wE 1846 W
  q27 : Eqn
  q27 = wE 1460 W
  q28 : Eqn
  q28 = wE 173 W
  q29 : Eqn
  q29 = wE 1461 W

-- CA CK30 Gad(t=0, W=(2,), d=Kd, e=-1): 25 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ : ⟪ (ℓ "乑丘下中九丮九上丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘乑") ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ = derive (ℓ "乑丘下中九丮九上丘") (ℓ "丘中九丮九丘乑")
  (rw 1 q19 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 0 q22 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 5 q27 ∷
   rw 5 q25 ∷
   rw 10 q19 ∷
   rw 9 q28 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q20 ∷
   rw 7 q28 ∷
   rw 6 q22 ∷
   rw 7 q29 ∷
   rw 8 q19 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 1817 W
  q31 : Eqn
  q31 = sE 1578 lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q32 : Eqn
  q32 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q33 : Eqn
  q33 = wE 1813 W
  q34 : Eqn
  q34 = wE 1732 W
  q35 : Eqn
  q35 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(2,), d=1, e=-1): 7 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "両丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘三中九丮九丈丘両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = derive (ℓ "両丘中九丮九丘") (ℓ "丘三中九丮九丈丘両")
  (rw 0 q30 ∷
   rw 1 q31 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷
   rw 6 q34 ∷
   rw 7 q32 ∷
   rw 8 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1819 W
  q37 : Eqn
  q37 = sE 1579 lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2
  q38 : Eqn
  q38 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q39 : Eqn
  q39 = wE 1728 W
  q40 : Eqn
  q40 = wE 1727 W
  q41 : Eqn
  q41 = wE 1820 W

-- CA CS10 Gad(t=0, W=(2,), d=Sd, e=-1): 7 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ : ⟪ (ℓ "丠丘三中九丮九丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ = derive (ℓ "丠丘三中九丮九丈丘") (ℓ "丘中九丮九丘丠")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   rw 1 q39 ∷
   rw 5 q40 ∷
   rw 5 q38 ∷
   rw 6 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q43 : Eqn
  q43 = wE 1464 W
  q44 : Eqn
  q44 = sE 1582 lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q45 : Eqn
  q45 = wE 1465 W

-- pass [CKd30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "乒丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞乒") ⟫ʷ
lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "乒丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞乒")
  (rw 1 q42 ∷
   rw 2 q19 ∷
   rw 1 q28 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q20 ∷
   rw 1 q43 ∷
   rw 0 q23 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 1 q44 ∷
   rw 11 q19 ∷
   rw 10 q28 ∷
   rw 9 q28 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q20 ∷
   rw 7 q28 ∷
   rw 8 q45 ∷
   rw 7 q23 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q20 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q47 : Eqn
  q47 = wE 1940 W
  q48 : Eqn
  q48 = sE 1584 lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q49 : Eqn
  q49 = wE 1941 W

-- pass [CKd31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "乕丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "乕丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞乕")
  (rw 1 q46 ∷
   rw 0 q47 ∷
   rw 1 q48 ∷
   rw 7 q49 ∷
   rw⁻ 0 q46 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q51 : Eqn
  q51 = wE 1474 W
  q52 : Eqn
  q52 = sE 1580 lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q53 : Eqn
  q53 = wE 1475 W

-- pass [CS21] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 5 steps
lem-pass-CS21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "丶丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘丶") ⟫ʷ
lem-pass-CS21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "丶丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘丶")
  (rw 1 q50 ∷
   rw 0 q51 ∷
   rw 1 q52 ∷
   rw 7 q53 ∷
   rw⁻ 0 q50 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 1480 W
  q55 : Eqn
  q55 = sE 1581 lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q56 : Eqn
  q56 = wE 1481 W

-- pass [CSd21] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 5 steps
lem-pass-CSd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "丷丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘丷") ⟫ʷ
lem-pass-CSd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "丷丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘丷")
  (rw 1 q50 ∷
   rw 0 q54 ∷
   rw 1 q55 ∷
   rw 7 q56 ∷
   rw⁻ 0 q50 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 1585 lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CZ13 CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 : ⟪ (ℓ "丽习举习丿乜") ⟫ʷ ≈ ⟪ (ℓ "丿乜丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 = derive (ℓ "丽习举习丿乜") (ℓ "丿乜丽习举习")
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 1588 lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2

-- pass [CKd31] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "乕丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "乕丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞乕")
  (rw 2 q42 ∷
   rw 1 q46 ∷
   rw 0 q47 ∷
   rw 1 q58 ∷
   rw 9 q49 ∷
   rw⁻ 0 q46 ∷
   rw⁻ 1 q42 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 1587 lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0
  q60 : Eqn
  q60 = wE 1942 W
  q61 : Eqn
  q61 = wE 1943 W

-- CA CS10 Gad(t=0, W=(), d=SdKdKd, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩ : ⟪ (ℓ "丠三下下中九丮九上上丈") ⟫ʷ ≈ ⟪ (ℓ "下下中九丮九上上丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩ = derive (ℓ "丠三下下中九丮九上上丈") (ℓ "下下中九丮九上上丠")
  (rw 0 q36 ∷
   rw 1 q59 ∷
   rw 0 q60 ∷
   rw 6 q61 ∷
   rw 8 q41 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1586 lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0
  q63 : Eqn
  q63 = wE 1944 W
  q64 : Eqn
  q64 = wE 1945 W

-- CA CS10 Gad(t=0, W=(), d=SdKKKK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ : ⟪ (ℓ "丠三上上上上中九丮九下下下下丈") ⟫ʷ ≈ ⟪ (ℓ "上上上上中九丮九下下下下丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ = derive (ℓ "丠三上上上上中九丮九下下下下丈") (ℓ "上上上上中九丮九下下下下丠")
  (rw 0 q36 ∷
   rw 1 q62 ∷
   rw 0 q63 ∷
   rw 8 q64 ∷
   rw 12 q41 ∷ []) Eq.refl
