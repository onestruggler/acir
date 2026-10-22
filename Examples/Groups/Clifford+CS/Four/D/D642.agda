{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD642 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D642 (W : Ws) (Sᴰ : SD642) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CZ12-vs-CS03 : St 574
  lem-pass-CZ12-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CZ12-vs-CSd03 : St 597
  lem-pass-CZ12-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS03-vs-CZ13 : St 1341
  lem-pass-CS03-vs-CZ13 = pickᴰ 2 Sᴰ
  lem-pass-CS03-vs-Z1 : St 1343
  lem-pass-CS03-vs-Z1 = pickᴰ 3 Sᴰ
  lem-pass-CSd03-vs-CZ13 : St 1347
  lem-pass-CSd03-vs-CZ13 = pickᴰ 4 Sᴰ
  lem-pass-CSd03-vs-Z1 : St 1349
  lem-pass-CSd03-vs-Z1 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 6 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 7 Sᴰ
  lem-pass-CX23-vs-X2-TOFF312-X2 : St 1548
  lem-pass-CX23-vs-X2-TOFF312-X2 = pickᴰ 8 Sᴰ
  lem-pass-CK30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 1549
  lem-pass-CK30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 9 Sᴰ
  lem-pass-TOFF012-vs-CZ13 : St 1363
  lem-pass-TOFF012-vs-CZ13 = pickᴰ 10 Sᴰ
  lem-pass-CCZ123-vs-TOFF012 : St 1444
  lem-pass-CCZ123-vs-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1457
  lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 12 Sᴰ
  lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1485
  lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-TOFF302-vs-X2-TOFF312-X2 : St 1510
  lem-pass-TOFF302-vs-X2-TOFF312-X2 = pickᴰ 14 Sᴰ
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-III-units-3 : St 1550
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-III-units-3 = pickᴰ 15 Sᴰ
  lem-pass-X1-CS10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1551
  lem-pass-X1-CS10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 16 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : St 1552
  lem-pass-X1-CSd10-X1-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = pickᴰ 17 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : St 1553
  lem-pass-X2-CSd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : St 1554
  lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = pickᴰ 19 Sᴰ
  lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : St 1555
  lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = pickᴰ 20 Sᴰ
  lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : St 1556
  lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = pickᴰ 21 Sᴰ
  lem-pass-TOFF201-vs-CCZ013 : St 1557
  lem-pass-TOFF201-vs-CCZ013 = pickᴰ 22 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : St 1558
  lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = pickᴰ 23 Sᴰ
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : St 1559
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 24 Sᴰ
  lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 1560
  lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 1561
  lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 26 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : St 1562
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = pickᴰ 27 Sᴰ
  lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : St 1563
  lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = pickᴰ 28 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : St 1564
  lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = pickᴰ 29 Sᴰ
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 : St 1565
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 30 Sᴰ
  lem-pass-CS10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 1566
  lem-pass-CS10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 31 Sᴰ

private
  q1 : Eqn
  q1 = wE 1896 W
  q2 : Eqn
  q2 = sE 1550 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-III-units-3
  q3 : Eqn
  q3 = wE 1897 W

-- pass [CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX20 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 S0 S0 CK01 S0 S0 S0 S0 CK01 S0 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01] [X2 TOFF312 X2]: 3 steps
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-TOFF312-X2 : ⟪ (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX20-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-S0-S0-CK01-S0-S0-S0-S0-CK01-S0-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-vs-X2-TOFF312-X2 = derive (CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ S0 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ [])
  (rw 74 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q6 : Eqn
  q6 = wE 1106 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q9 : Eqn
  q9 = wE 30 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 122 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 127 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 74 W
  q18 : Eqn
  q18 = wE 337 W
  q19 : Eqn
  q19 = wE 1932 W
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q21 : Eqn
  q21 = wE 24 W
  q22 : Eqn
  q22 = wE 25 W
  q23 : Eqn
  q23 = wE 124 W
  q24 : Eqn
  q24 = sE 1510 lem-pass-TOFF302-vs-X2-TOFF312-X2
  q25 : Eqn
  q25 = sE 1548 lem-pass-CX23-vs-X2-TOFF312-X2
  q26 : Eqn
  q26 = wE 1933 W
  q27 : Eqn
  q27 = wE 317 W

-- pass [X0 X3 TOFF302 X0 X3] [X2 TOFF312 X2]: 134 steps
lem-pass-X0-X3-TOFF302-X0-X3-vs-X2-TOFF312-X2 : ⟪ (X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-TOFF302-X0-X3-vs-X2-TOFF312-X2 = derive (X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ [])
  (rw 5 q4 ∷
   rw⁻ 4 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 3 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   rw⁻ 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q16 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q17 ∷
   rw⁻ 5 q10 ∷
   rw 4 q17 ∷
   rw⁻ 3 q8 ∷
   rw⁻ 2 q7 ∷
   rw 3 q18 ∷
   re 3 8 (Toff312 ∷ []) ∷
   rw⁻ 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q19 ∷
   rw 0 q20 ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q13 ∷
   rw 1 q4 ∷
   rw 2 q7 ∷
   rw 3 q8 ∷
   rw 4 q21 ∷
   rw 5 q10 ∷
   rw 6 q21 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q22 ∷
   rw 9 q11 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q23 ∷
   rw 2 q18 ∷
   re 2 8 (Toff312 ∷ []) ∷
   re 1 3 (Toff302 ∷ []) ∷
   rw 2 q14 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 5 q4 ∷
   re 4 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ∷
   re 5 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q8 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw 8 q9 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q13 ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw⁻ 10 q7 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 10 q16 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q17 ∷
   rw⁻ 7 q10 ∷
   rw 6 q17 ∷
   rw⁻ 5 q8 ∷
   rw⁻ 4 q7 ∷
   rw 5 q18 ∷
   re 5 8 (Toff312 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 4 q26 ∷
   rw 3 q27 ∷
   rw 4 q5 ∷
   re 6 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q13 ∷
   rw 5 q4 ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q21 ∷
   rw 9 q10 ∷
   rw 10 q21 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q22 ∷
   rw 13 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q23 ∷
   rw 6 q18 ∷
   re 6 8 (Toff312 ∷ []) ∷
   re 5 3 (Toff302 ∷ []) ∷
   rw 6 q27 ∷
   rw 7 q5 ∷
   rw 8 q14 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 1812 W
  q29 : Eqn
  q29 = sE 1457 lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q30 : Eqn
  q30 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q31 : Eqn
  q31 = wE 1813 W
  q32 : Eqn
  q32 = wE 1732 W
  q33 : Eqn
  q33 = wE 1814 W

-- CA CSd20 Gad(t=0, W=(3,), d=1, e=-1): 7 steps
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : ⟪ (CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = derive (CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q28 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 6 q32 ∷
   rw 7 q30 ∷
   rw 8 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1815 W
  q35 : Eqn
  q35 = sE 1553 lem-pass-X2-CSd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3
  q36 : Eqn
  q36 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q37 : Eqn
  q37 = wE 1728 W
  q38 : Eqn
  q38 = wE 1727 W
  q39 : Eqn
  q39 = wE 1816 W

-- CA CS20 Gad(t=0, W=(3,), d=Sd, e=-1): 7 steps
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ : ⟪ (CS02 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ = derive (CS02 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q34 ∷
   rw 1 q35 ∷
   rw 0 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷
   rw 5 q36 ∷
   rw 6 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 843 lem-pass-CCZ123-vs-CS03
  q41 : Eqn
  q41 = sE 574 lem-pass-CZ12-vs-CS03
  q42 : Eqn
  q42 = sE 1444 lem-pass-CCZ123-vs-TOFF012
  q43 : Eqn
  q43 = wE 467 W
  q44 : Eqn
  q44 = sE 861 lem-pass-CCZ123-vs-CSd03
  q45 : Eqn
  q45 = sE 597 lem-pass-CZ12-vs-CSd03

-- pass [CZ12 CCZ123] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-CZ12-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CZ12 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = derive (CZ12 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q40 ∷
   rw 0 q41 ∷
   rw 2 q42 ∷
   rw 1 q43 ∷
   rw 3 q44 ∷
   rw 2 q45 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1817 W
  q47 : Eqn
  q47 = sE 1551 lem-pass-X1-CS10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q48 : Eqn
  q48 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(3,), d=1, e=-1): 7 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : ⟪ (CS01⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = derive (CS01⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CS01⁻ ∷ [])
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 6 q32 ∷
   rw 7 q30 ∷
   rw 8 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1819 W
  q50 : Eqn
  q50 = sE 1552 lem-pass-X1-CSd10-X1-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3
  q51 : Eqn
  q51 = wE 1820 W

-- CA CS10 Gad(t=0, W=(3,), d=Sd, e=-1): 7 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ : ⟪ (CS01 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ = derive (CS01 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS01 ∷ [])
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 0 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷
   rw 5 q36 ∷
   rw 6 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 1559 lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 1557 lem-pass-TOFF201-vs-CCZ013

-- pass [CCZ013] [TOFF201]: 1 steps
lem-pass-CCZ013-vs-TOFF201 : ⟪ (CCZ013 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-TOFF201 = derive (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ [])
  (rw⁻ 0 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 1556 lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123
  q55 : Eqn
  q55 = sE 1555 lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123
  q56 : Eqn
  q56 = sE 1554 lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123

-- pass [CS03 TOFF012 CSd03 TOFF012] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q54 ∷
   rw 2 q55 ∷
   rw 1 q54 ∷
   rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q58 : Eqn
  q58 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q59 : Eqn
  q59 = wE 1 W
  q60 : Eqn
  q60 = wE 173 W
  q61 : Eqn
  q61 = wE 3 W
  q62 : Eqn
  q62 = wE 1464 W
  q63 : Eqn
  q63 = wE 175 W
  q64 : Eqn
  q64 = sE 1558 lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2
  q65 : Eqn
  q65 = wE 1465 W

-- pass [CKd30] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 27 steps
lem-pass-CKd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q57 ∷
   rw 1 q58 ∷
   rw 2 q59 ∷
   rw 1 q60 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q61 ∷
   rw 1 q62 ∷
   rw 0 q63 ∷
   rw 1 q63 ∷
   rw 4 q59 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q63 ∷
   rw 4 q61 ∷
   rw 1 q64 ∷
   rw 13 q59 ∷
   rw 12 q60 ∷
   rw 11 q60 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q61 ∷
   rw 9 q60 ∷
   rw 10 q65 ∷
   rw 9 q63 ∷
   rw 12 q59 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   rw 11 q61 ∷
   rw⁻ 0 q58 ∷
   rw⁻ 1 q57 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q67 : Eqn
  q67 = wE 1466 W
  q68 : Eqn
  q68 = sE 1564 lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3
  q69 : Eqn
  q69 = wE 1467 W

-- pass [CSd20] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CSd20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 1 q66 ∷
   rw 0 q67 ∷
   rw 11 q57 ∷
   rw 1 q68 ∷
   rw 9 q69 ∷
   rw⁻ 0 q66 ∷
   rw⁻ 8 q57 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1462 W
  q71 : Eqn
  q71 = sE 1563 lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3
  q72 : Eqn
  q72 = wE 1463 W

-- pass [CS20] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CS20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS02 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (CS02 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 1 q66 ∷
   rw 0 q70 ∷
   rw 11 q57 ∷
   rw 1 q71 ∷
   rw 9 q72 ∷
   rw⁻ 0 q66 ∷
   rw⁻ 8 q57 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = sE 1485 lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q74 : Eqn
  q74 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))

-- CA CSd10 Gad(t=0, W=(2, 3), d=1, e=-1): 9 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ : ⟪ (CS01⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ = derive (CS01⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  (rw 0 q46 ∷
   rw 1 q73 ∷
   rw 0 q74 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 7 q32 ∷
   rw 8 q74 ∷
   rw 9 q30 ∷
   rw 10 q48 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 1562 lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3
  q76 : Eqn
  q76 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))

-- CA CS10 Gad(t=0, W=(2, 3), d=Sd, e=-1): 9 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡-1⟩ : ⟪ (CS01 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡-1⟩ = derive (CS01 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS01 ∷ [])
  (rw 0 q49 ∷
   rw 1 q75 ∷
   rw 0 q76 ∷
   rw 1 q36 ∷
   rw 2 q37 ∷
   rw 6 q38 ∷
   rw 6 q76 ∷
   rw 7 q36 ∷
   rw 8 q51 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 1341 lem-pass-CS03-vs-CZ13
  q78 : Eqn
  q78 = sE 1343 lem-pass-CS03-vs-Z1
  q79 : Eqn
  q79 = sE 1363 lem-pass-TOFF012-vs-CZ13
  q80 : Eqn
  q80 = wE 1934 W
  q81 : Eqn
  q81 = sE 1347 lem-pass-CSd03-vs-CZ13
  q82 : Eqn
  q82 = sE 1349 lem-pass-CSd03-vs-Z1

-- pass [Z1 CZ12 CZ13 CCZ123] [CS03 TOFF012 CSd03 TOFF012]: 16 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = derive (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 3 q40 ∷
   rw⁻ 2 q77 ∷
   rw 1 q41 ∷
   rw⁻ 0 q78 ∷
   rw 4 q42 ∷
   rw⁻ 3 q79 ∷
   rw 2 q43 ∷
   rw 1 q80 ∷
   rw 5 q44 ∷
   rw⁻ 4 q81 ∷
   rw 3 q45 ∷
   rw⁻ 2 q82 ∷
   rw 6 q42 ∷
   rw⁻ 5 q79 ∷
   rw 4 q43 ∷
   rw 3 q80 ∷ []) Eq.refl

-- pass [CZ12 CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 8 steps
lem-pass-CZ12-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CZ12 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CZ12 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q42 ∷
   rw 0 q43 ∷
   rw 2 q40 ∷
   rw 1 q41 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   rw 4 q44 ∷
   rw 3 q45 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = sE 1565 lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q83 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 3 q55 ∷
   rw 2 q54 ∷
   rw 1 q56 ∷
   rw 0 q54 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 464 W
  q85 : Eqn
  q85 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q86 : Eqn
  q86 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q87 : Eqn
  q87 = wE 1935 W
  q88 : Eqn
  q88 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q89 : Eqn
  q89 = sE 1560 lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q90 : Eqn
  q90 = sE 1561 lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q91 : Eqn
  q91 = sE 1549 lem-pass-CK30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q92 : Eqn
  q92 = sE 1566 lem-pass-CS10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q93 : Eqn
  q93 = wE 1936 W
  q94 : Eqn
  q94 = wE 151 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 132 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 31 q59 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q61 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q61 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q61 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q61 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q61 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q61 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q61 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q61 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q61 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q61 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q61 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q61 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q61 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q61 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q61 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q61 ∷
   rw 14 q84 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q61 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q61 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q61 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q61 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q61 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q61 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q61 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q61 ∷
   rw 5 q85 ∷
   rw 4 q85 ∷
   rw 3 q86 ∷
   rw 2 q85 ∷
   rw 1 q85 ∷
   rw 0 q85 ∷
   rw 1 q87 ∷
   rw⁻ 0 q85 ∷
   rw 3 q59 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw⁻ 2 q88 ∷
   rw 5 q59 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q61 ∷
   rw 3 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 0 q92 ∷
   rw 14 q59 ∷
   re 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q61 ∷
   rw 12 q88 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 13 q61 ∷
   rw 10 q85 ∷
   rw 11 q93 ∷
   rw⁻ 10 q85 ∷
   rw⁻ 11 q85 ∷
   rw⁻ 12 q85 ∷
   rw⁻ 13 q86 ∷
   rw⁻ 14 q85 ∷
   rw⁻ 15 q85 ∷
   rw 18 q59 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 19 q59 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q59 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q59 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q59 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q59 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q59 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q59 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 24 q94 ∷
   rw 27 q59 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q59 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q59 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q59 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q59 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q59 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q59 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q59 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q59 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q59 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 37 q59 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q59 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q59 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q59 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 41 q59 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q59 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q61 ∷ []) Eq.refl

-- pass [Z1 CZ12 CZ13 CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 16 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = derive (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 3 q42 ∷
   rw⁻ 2 q79 ∷
   rw 1 q43 ∷
   rw 0 q80 ∷
   rw 4 q40 ∷
   rw⁻ 3 q77 ∷
   rw 2 q41 ∷
   rw⁻ 1 q78 ∷
   rw 5 q42 ∷
   rw⁻ 4 q79 ∷
   rw 3 q43 ∷
   rw 2 q80 ∷
   rw 6 q44 ∷
   rw⁻ 5 q81 ∷
   rw 4 q45 ∷
   rw⁻ 3 q82 ∷ []) Eq.refl
