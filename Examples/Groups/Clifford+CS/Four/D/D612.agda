{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD612 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D612 (W : Ws) (Sᴰ : SD612) where

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
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1 : St 1328
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1 = pickᴰ 0 Sᴰ
  lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 1374
  lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 1 Sᴰ
  lem-pass-X2-CS20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 : St 1375
  lem-pass-X2-CS20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 = pickᴰ 2 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 1371
  lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 3 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 : St 1376
  lem-pass-X2-CSd20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-TOFF213-X1 : St 1377
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-TOFF213-X1 = pickᴰ 5 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : St 1378
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = pickᴰ 6 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 : St 1379
  lem-pass-X2-CK21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 = pickᴰ 7 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 : St 1380
  lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 = pickᴰ 8 Sᴰ
  lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 1381
  lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 9 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 : St 1382
  lem-pass-X3-CKd32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 = pickᴰ 10 Sᴰ

private
  q1 : Eqn
  q1 = wE 1714 W
  q2 : Eqn
  q2 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q3 : Eqn
  q3 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q4 : Eqn
  q4 = sE 1374 lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q5 : Eqn
  q5 = wE 1715 W

-- pass [CS10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CS10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "丠丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞丠") ⟫ʷ
lem-pass-CS10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "丠丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞丠")
  (rw 0 q1 ∷
   rw 10 q2 ∷
   rw 11 q3 ∷
   rw 1 q4 ∷
   rw 9 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 7 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1466 W
  q7 : Eqn
  q7 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q8 : Eqn
  q8 = sE 1376 lem-pass-X2-CSd20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3
  q9 : Eqn
  q9 = wE 1467 W

-- pass [CSd20] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CSd20-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "丨丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "丨丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞丨")
  (rw 1 q2 ∷
   rw 0 q6 ∷
   rw 11 q7 ∷
   rw 1 q8 ∷
   rw 9 q9 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 8 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1462 W
  q11 : Eqn
  q11 = sE 1375 lem-pass-X2-CS20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3
  q12 : Eqn
  q12 = wE 1463 W

-- pass [CS20] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CS20-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "丧丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "丧丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞丧")
  (rw 1 q2 ∷
   rw 0 q10 ∷
   rw 11 q7 ∷
   rw 1 q11 ∷
   rw 9 q12 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 8 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 1371 lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3

-- pass [CS20] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丧丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丧丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丧")
  (rw 0 q10 ∷
   rw 9 q7 ∷
   rw 1 q13 ∷
   rw 7 q12 ∷
   rw⁻ 6 q7 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1817 W
  q15 : Eqn
  q15 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q17 : Eqn
  q17 = wE 1813 W
  q18 : Eqn
  q18 = wE 1732 W
  q19 : Eqn
  q19 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(2, 3), d=1, e=1): 9 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ : ⟪ (ℓ "両丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三九中九丮丈丘丞両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ = derive (ℓ "両丘丞九中九丮丘丞") (ℓ "丘丞三九中九丮丈丘丞両")
  (rw 0 q14 ∷
   rw 1 q4 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 7 q18 ∷
   rw 8 q15 ∷
   rw 9 q16 ∷
   rw 10 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1819 W
  q21 : Eqn
  q21 = sE 1378 lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3
  q22 : Eqn
  q22 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q24 : Eqn
  q24 = wE 1728 W
  q25 : Eqn
  q25 = wE 1727 W
  q26 : Eqn
  q26 = wE 1820 W

-- CA CS10 Gad(t=0, W=(2, 3), d=Sd, e=1): 9 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ : ⟪ (ℓ "丠丘丞三九中九丮丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ = derive (ℓ "丠丘丞三九中九丮丈丘丞") (ℓ "丘丞九中九丮丘丞丠")
  (rw 0 q20 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 6 q25 ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   rw 8 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1478 W
  q28 : Eqn
  q28 = sE 1380 lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3
  q29 : Eqn
  q29 = wE 1479 W

-- pass [CKd21] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (ℓ "么丘丞上丈丈下九中九丮上三三下丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞上丈丈下九中九丮上三三下丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = derive (ℓ "么丘丞上丈丈下九中九丮上三三下丘丞") (ℓ "丘丞上丈丈下九中九丮上三三下丘丞么")
  (rw 0 q27 ∷
   rw 17 q7 ∷
   rw 1 q28 ∷
   rw 15 q29 ∷
   rw⁻ 14 q7 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 1476 W
  q31 : Eqn
  q31 = sE 1379 lem-pass-X2-CK21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3
  q32 : Eqn
  q32 = wE 1477 W

-- pass [CK21] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (ℓ "乇丘丞上丈丈下九中九丮上三三下丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞上丈丈下九中九丮上三三下丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = derive (ℓ "乇丘丞上丈丈下九中九丮上三三下丘丞") (ℓ "丘丞上丈丈下九中九丮上三三下丘丞乇")
  (rw 0 q30 ∷
   rw 17 q7 ∷
   rw 1 q31 ∷
   rw 15 q32 ∷
   rw⁻ 14 q7 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q34 : Eqn
  q34 = wE 1674 W
  q35 : Eqn
  q35 = sE 1382 lem-pass-X3-CKd32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0
  q36 : Eqn
  q36 = wE 1675 W

-- pass [CKd32] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "乘丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "乘丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞乘")
  (rw 1 q33 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   rw 7 q36 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q38 : Eqn
  q38 = wE 1474 W
  q39 : Eqn
  q39 = sE 1381 lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q40 : Eqn
  q40 = wE 1475 W

-- pass [CS21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "丶丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "丶丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞丶")
  (rw 1 q37 ∷
   rw 0 q38 ∷
   rw 11 q7 ∷
   rw 1 q39 ∷
   rw 9 q40 ∷
   rw⁻ 0 q37 ∷
   rw⁻ 8 q7 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 1823 W
  q42 : Eqn
  q42 = wE 1824 W
  q43 : Eqn
  q43 = sE 1328 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF312-X1
  q44 : Eqn
  q44 = wE 1825 W

-- X->Y 3 2: 4 steps
lem-X-⟶Y-3-2 : ⟪ (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") ⟫ʷ ≈ ⟪ (ℓ "乌丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乌") ⟫ʷ
lem-X-⟶Y-3-2 = derive (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") (ℓ "乌丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乌")
  (rw 0 q41 ∷
   rw 35 q42 ∷
   rw⁻ 1 q43 ∷
   rw 32 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1826 W
  q46 : Eqn
  q46 = wE 1827 W
  q47 : Eqn
  q47 = sE 1377 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-TOFF213-X1
  q48 : Eqn
  q48 = wE 1828 W

-- X->Y 2 3: 4 steps
lem-X-⟶Y-2-3 : ⟪ (ℓ "乥丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乥") ⟫ʷ ≈ ⟪ (ℓ "乖丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乖") ⟫ʷ
lem-X-⟶Y-2-3 = derive (ℓ "乥丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乥") (ℓ "乖丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乖")
  (rw 0 q45 ∷
   rw 35 q46 ∷
   rw⁻ 1 q47 ∷
   rw 32 q48 ∷ []) Eq.refl
