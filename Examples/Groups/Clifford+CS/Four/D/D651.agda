{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD651 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D651 (W : Ws) (Sᴰ : SD651) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-SW-T-SW : St 1608
  lem-SW-T-SW = pickᴰ 0 Sᴰ
  lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 : St 1609
  lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 1 Sᴰ
  lem-pass-TOFF103-vs-X3-TOFF013-X3 : St 1610
  lem-pass-TOFF103-vs-X3-TOFF013-X3 = pickᴰ 2 Sᴰ
  lem-pass-TOFF013-vs-X3-TOFF103-X3 : St 1611
  lem-pass-TOFF013-vs-X3-TOFF103-X3 = pickᴰ 3 Sᴰ
  lem-pass-CCZ123-vs-CS13 : St 1333
  lem-pass-CCZ123-vs-CS13 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-CSd13 : St 1334
  lem-pass-CCZ123-vs-CSd13 = pickᴰ 5 Sᴰ
  lem-pass-CCZ023-vs-CSd13 : St 1612
  lem-pass-CCZ023-vs-CSd13 = pickᴰ 6 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 7 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 : St 1613
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 = pickᴰ 8 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 : St 1614
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 = pickᴰ 9 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS02 : St 1615
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS02 = pickᴰ 10 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd02 : St 1616
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd02 = pickᴰ 11 Sᴰ
  lem-pass-TOFF102-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : St 1617
  lem-pass-TOFF102-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = pickᴰ 12 Sᴰ
  lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1618
  lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 13 Sᴰ
  lem-pass-TOFF102-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : St 1619
  lem-pass-TOFF102-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = pickᴰ 14 Sᴰ
  lem-pass-TOFF102-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : St 1620
  lem-pass-TOFF102-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = pickᴰ 15 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 : St 1621
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 = pickᴰ 16 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 : St 1622
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 = pickᴰ 17 Sᴰ
  lem-S3 : St 1623
  lem-S3 = pickᴰ 18 Sᴰ
  lem-pass-CS12-vs-X1-X3-TOFF013-X1-X3 : St 1624
  lem-pass-CS12-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS12-vs-X3-TOFF013-X3 : St 1625
  lem-pass-CS12-vs-X3-TOFF013-X3 = pickᴰ 20 Sᴰ
  lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1626
  lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 21 Sᴰ
  lem-pass-CS13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : St 1627
  lem-pass-CS13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = pickᴰ 22 Sᴰ
  lem-pass-CSd12-vs-X1-X3-TOFF013-X1-X3 : St 1628
  lem-pass-CSd12-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 23 Sᴰ
  lem-pass-CSd12-vs-X3-TOFF013-X3 : St 1629
  lem-pass-CSd12-vs-X3-TOFF013-X3 = pickᴰ 24 Sᴰ
  lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1630
  lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 25 Sᴰ
  lem-pass-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : St 1631
  lem-pass-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = pickᴰ 26 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3 : St 1632
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3 = pickᴰ 27 Sᴰ
  lem-pass-CCZ023-vs-TOFF102 : St 1633
  lem-pass-CCZ023-vs-TOFF102 = pickᴰ 28 Sᴰ
  lem-pass-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : St 1634
  lem-pass-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 29 Sᴰ
  lem-pass-CS02-vs-X3-TOFF103-X3 : St 1635
  lem-pass-CS02-vs-X3-TOFF103-X3 = pickᴰ 30 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : St 1636
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = pickᴰ 31 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : St 1637
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = pickᴰ 32 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3 : St 1638
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3 = pickᴰ 33 Sᴰ
  lem-pass-CS13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : St 1639
  lem-pass-CS13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = pickᴰ 34 Sᴰ
  lem-pass-CS13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : St 1640
  lem-pass-CS13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = pickᴰ 35 Sᴰ
  lem-pass-CSd02-vs-X3-TOFF103-X3 : St 1641
  lem-pass-CSd02-vs-X3-TOFF103-X3 = pickᴰ 36 Sᴰ
  lem-pass-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : St 1642
  lem-pass-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = pickᴰ 37 Sᴰ
  lem-pass-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : St 1643
  lem-pass-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = pickᴰ 38 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03 : St 1644
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03 = pickᴰ 39 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 : St 1645
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 = pickᴰ 40 Sᴰ

private
  q1 : Eqn
  q1 = sE 1623 lem-S3
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = sE 1608 lem-SW-T-SW
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = wE 135 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 76 W
  q11 : Eqn
  q11 = wE 1957 W
  q12 : Eqn
  q12 = wE 29 W

-- S2: 28 steps
lem-S2 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-S2 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw⁻ 0 q1 ∷
   rw 4 q2 ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   rw 0 q3 ∷
   rw 4 q4 ∷
   rw⁻ 3 q5 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 3 q6 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q5 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q10 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q5 ∷
   rw 4 q11 ∷
   rw 3 q12 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 1632 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3
  q14 : Eqn
  q14 = sE 1615 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS02
  q15 : Eqn
  q15 = sE 1616 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd02

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q13 ∷
   rw 3 q14 ∷
   rw 4 q13 ∷
   rw 7 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 1629 lem-pass-CSd12-vs-X3-TOFF013-X3
  q17 : Eqn
  q17 = sE 1610 lem-pass-TOFF103-vs-X3-TOFF013-X3
  q18 : Eqn
  q18 = sE 1625 lem-pass-CS12-vs-X3-TOFF013-X3

-- pass [TOFF103 CS12 TOFF103 CSd12] [X3 TOFF013 X3]: 4 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw 3 q16 ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw 0 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 1631 lem-pass-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03
  q20 : Eqn
  q20 = sE 1620 lem-pass-TOFF102-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03
  q21 : Eqn
  q21 = sE 1627 lem-pass-CS13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 3 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q20 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 1628 lem-pass-CSd12-vs-X1-X3-TOFF013-X1-X3
  q23 : Eqn
  q23 = sE 1609 lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3
  q24 : Eqn
  q24 = sE 1624 lem-pass-CS12-vs-X1-X3-TOFF013-X1-X3

-- pass [TOFF103 CS12 TOFF103 CSd12] [X1 X3 TOFF013 X1 X3]: 4 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw 3 q22 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q23 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 1630 lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2
  q26 : Eqn
  q26 = sE 1618 lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2
  q27 : Eqn
  q27 = sE 1626 lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2

-- pass [TOFF102 CS13 TOFF102 CSd13] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 3 q25 ∷
   rw 2 q26 ∷
   rw 1 q27 ∷
   rw 0 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 1641 lem-pass-CSd02-vs-X3-TOFF103-X3
  q29 : Eqn
  q29 = sE 1611 lem-pass-TOFF013-vs-X3-TOFF103-X3
  q30 : Eqn
  q30 = sE 1635 lem-pass-CS02-vs-X3-TOFF103-X3

-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF103 X3]: 4 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF103-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF103-X3 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  (rw 3 q28 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 0 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 1638 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3
  q32 : Eqn
  q32 = sE 1613 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02
  q33 : Eqn
  q33 = sE 1614 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 0 q31 ∷
   rw 3 q32 ∷
   rw 4 q31 ∷
   rw 7 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1642 lem-pass-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2
  q35 : Eqn
  q35 = sE 1617 lem-pass-TOFF102-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2
  q36 : Eqn
  q36 = sE 1639 lem-pass-CS13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2

-- pass [TOFF102 CS13 TOFF102 CSd13] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 3 q34 ∷
   rw 2 q35 ∷
   rw 1 q36 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 1643 lem-pass-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03
  q38 : Eqn
  q38 = sE 1619 lem-pass-TOFF102-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03
  q39 : Eqn
  q39 = sE 1640 lem-pass-CS13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF012 X2 CS03 X2 TOFF012 X2 CSd03]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 3 q37 ∷
   rw 2 q38 ∷
   rw 1 q39 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 1333 lem-pass-CCZ123-vs-CS13
  q41 : Eqn
  q41 = wE 1377 W
  q42 : Eqn
  q42 = wE 127 W
  q43 : Eqn
  q43 = wE 271 W
  q44 : Eqn
  q44 = wE 8 W
  q45 : Eqn
  q45 = wE 9 W
  q46 : Eqn
  q46 = wE 10 W
  q47 : Eqn
  q47 = wE 272 W
  q48 : Eqn
  q48 = wE 253 W
  q49 : Eqn
  q49 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q50 : Eqn
  q50 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q51 : Eqn
  q51 = wE 24 W
  q52 : Eqn
  q52 = wE 25 W
  q53 : Eqn
  q53 = wE 26 W
  q54 : Eqn
  q54 = wE 12 W
  q55 : Eqn
  q55 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q56 : Eqn
  q56 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q57 : Eqn
  q57 = wE 14 W
  q58 : Eqn
  q58 = wE 15 W
  q59 : Eqn
  q59 = wE 16 W
  q60 : Eqn
  q60 = wE 46 W
  q61 : Eqn
  q61 = wE 30 W
  q62 : Eqn
  q62 = wE 22 W
  q63 : Eqn
  q63 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q64 : Eqn
  q64 = wE 23 W
  q65 : Eqn
  q65 = wE 47 W
  q66 : Eqn
  q66 = wE 48 W
  q67 : Eqn
  q67 = wE 3 W
  q68 : Eqn
  q68 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q69 : Eqn
  q69 = wE 43 W
  q70 : Eqn
  q70 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q71 : Eqn
  q71 = wE 20 W
  q72 : Eqn
  q72 = wE 21 W
  q73 : Eqn
  q73 = wE 49 W
  q74 : Eqn
  q74 = wE 50 W
  q75 : Eqn
  q75 = wE 51 W
  q76 : Eqn
  q76 = wE 52 W
  q77 : Eqn
  q77 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q78 : Eqn
  q78 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q79 : Eqn
  q79 = sE 1612 lem-pass-CCZ023-vs-CSd13
  q80 : Eqn
  q80 = sE 1633 lem-pass-CCZ023-vs-TOFF102
  q81 : Eqn
  q81 = wE 74 W
  q82 : Eqn
  q82 = wE 33 W

-- pass [CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 461 steps
lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CCZ123 ∷ [])
  (rw 0 q40 ∷
   rw 1 q41 ∷
   rw 5 q4 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q42 ∷
   rw 10 q43 ∷
   rw 9 q6 ∷
   rw 8 q44 ∷
   rw 7 q45 ∷
   rw 6 q44 ∷
   rw 5 q46 ∷
   rw 4 q43 ∷
   rw 5 q47 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 8 q46 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 6 q48 ∷
   rw⁻ 5 q49 ∷
   rw 4 q48 ∷
   rw⁻ 3 q50 ∷
   rw 4 q4 ∷
   rw 5 q50 ∷
   rw 6 q51 ∷
   rw 7 q49 ∷
   rw 8 q51 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q52 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q53 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q42 ∷
   rw 8 q43 ∷
   rw 7 q6 ∷
   rw 6 q44 ∷
   rw 5 q45 ∷
   rw 4 q44 ∷
   rw 3 q46 ∷
   rw 2 q43 ∷
   rw 3 q47 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 6 q54 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 12 q55 ∷
   rw 11 q56 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q57 ∷
   rw 9 q54 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q58 ∷
   rw 7 q54 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q59 ∷
   rw 5 q56 ∷
   rw 6 q60 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q61 ∷
   rw 6 q49 ∷
   rw 7 q61 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q62 ∷
   rw 10 q63 ∷
   rw 8 q64 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q57 ∷
   rw 6 q65 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q57 ∷
   rw 4 q66 ∷
   rw 5 q2 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q67 ∷
   rw⁻ 7 q68 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q67 ∷
   rw⁻ 9 q68 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q67 ∷
   rw 6 q69 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q55 ∷
   rw 9 q56 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q57 ∷
   rw 7 q54 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q58 ∷
   rw 5 q54 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q59 ∷
   rw 3 q56 ∷
   rw 4 q60 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 4 q70 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q68 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q68 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q67 ∷
   rw 3 q71 ∷
   rw 6 q54 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q72 ∷
   rw 8 q54 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q62 ∷
   rw⁻ 9 q63 ∷
   rw 10 q64 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q50 ∷
   rw 5 q51 ∷
   rw 6 q49 ∷
   rw 7 q51 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q52 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q53 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q73 ∷
   rw 5 q74 ∷
   rw 6 q75 ∷
   rw 7 q74 ∷
   rw 8 q71 ∷
   rw 4 q76 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q57 ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q61 ∷
   rw 5 q49 ∷
   rw 6 q61 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q8 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q9 ∷
   rw 2 q50 ∷
   rw 3 q51 ∷
   rw 4 q49 ∷
   rw 5 q51 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q52 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q53 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q61 ∷
   rw 5 q49 ∷
   rw 6 q61 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q8 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q50 ∷
   rw 5 q51 ∷
   rw 6 q49 ∷
   rw 7 q51 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q52 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q53 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q9 ∷
   rw 2 q77 ∷
   rw 3 q78 ∷
   rw 2 q79 ∷
   rw 4 q41 ∷
   rw 8 q4 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q42 ∷
   rw 13 q43 ∷
   rw 12 q6 ∷
   rw 11 q44 ∷
   rw 10 q45 ∷
   rw 9 q44 ∷
   rw 8 q46 ∷
   rw 7 q43 ∷
   rw 8 q47 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 11 q46 ∷
   rw⁻ 10 q5 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 9 q48 ∷
   rw⁻ 8 q49 ∷
   rw 7 q48 ∷
   rw⁻ 6 q50 ∷
   rw 7 q4 ∷
   rw 8 q50 ∷
   rw 9 q51 ∷
   rw 10 q49 ∷
   rw 11 q51 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 13 q52 ∷
   rw 14 q5 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q53 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q42 ∷
   rw 11 q43 ∷
   rw 10 q6 ∷
   rw 9 q44 ∷
   rw 8 q45 ∷
   rw 7 q44 ∷
   rw 6 q46 ∷
   rw 5 q43 ∷
   rw 6 q47 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 9 q54 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 15 q55 ∷
   rw 14 q56 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q57 ∷
   rw 12 q54 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q58 ∷
   rw 10 q54 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q59 ∷
   rw 8 q56 ∷
   rw 9 q60 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q50 ∷
   rw 8 q61 ∷
   rw 9 q49 ∷
   rw 10 q61 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 12 q8 ∷
   rw 13 q5 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q9 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q62 ∷
   rw 13 q63 ∷
   rw 11 q64 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q57 ∷
   rw 9 q65 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q57 ∷
   rw 7 q66 ∷
   rw 8 q2 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q67 ∷
   rw⁻ 10 q68 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q67 ∷
   rw⁻ 12 q68 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q67 ∷
   rw 9 q69 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 13 q55 ∷
   rw 12 q56 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q57 ∷
   rw 10 q54 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q58 ∷
   rw 8 q54 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q59 ∷
   rw 6 q56 ∷
   rw 7 q60 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 7 q70 ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q68 ∷
   rw 11 q2 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q68 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q67 ∷
   rw 6 q71 ∷
   rw 9 q54 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q72 ∷
   rw 11 q54 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q62 ∷
   rw⁻ 12 q63 ∷
   rw 13 q64 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q50 ∷
   rw 8 q51 ∷
   rw 9 q49 ∷
   rw 10 q51 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 12 q52 ∷
   rw 13 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q53 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q73 ∷
   rw 8 q74 ∷
   rw 9 q75 ∷
   rw 10 q74 ∷
   rw 11 q71 ∷
   rw 7 q76 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   rw 8 q57 ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q50 ∷
   rw 7 q61 ∷
   rw 8 q49 ∷
   rw 9 q61 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q9 ∷
   rw 5 q50 ∷
   rw 6 q51 ∷
   rw 7 q49 ∷
   rw 8 q51 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q52 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q53 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q50 ∷
   rw 7 q61 ∷
   rw 8 q49 ∷
   rw 9 q61 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q50 ∷
   rw 8 q51 ∷
   rw 9 q49 ∷
   rw 10 q51 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 12 q52 ∷
   rw 13 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q53 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q9 ∷
   rw 3 q80 ∷
   rw 5 q77 ∷
   rw 6 q4 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q50 ∷
   rw 6 q61 ∷
   rw 7 q49 ∷
   rw 8 q61 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q8 ∷
   rw 11 q5 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 10 q6 ∷
   rw⁻ 9 q5 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q81 ∷
   rw⁻ 7 q49 ∷
   rw 6 q81 ∷
   rw⁻ 5 q50 ∷
   rw 6 q53 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q61 ∷
   rw 6 q49 ∷
   rw 7 q61 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 9 q6 ∷
   rw⁻ 8 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q81 ∷
   rw⁻ 6 q49 ∷
   rw 5 q81 ∷
   rw⁻ 4 q50 ∷
   rw 5 q53 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 5 q82 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = sE 1634 lem-pass-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CCZ123 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CCZ123 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 1778 W
  q85 : Eqn
  q85 = wE 257 W
  q86 : Eqn
  q86 = wE 258 W
  q87 : Eqn
  q87 = sE 1636 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13
  q88 : Eqn
  q88 = wE 1777 W

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [TOFF102 CS13 TOFF102 CSd13]: 9 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  (rw 5 q84 ∷
   rw 8 q85 ∷
   rw 9 q84 ∷
   rw 12 q86 ∷
   rw 1 q87 ∷
   rw 0 q88 ∷
   rw 1 q85 ∷
   rw 2 q88 ∷
   rw 3 q86 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q90 : Eqn
  q90 = wE 1958 W
  q91 : Eqn
  q91 = wE 1959 W
  q92 : Eqn
  q92 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q93 : Eqn
  q93 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q94 : Eqn
  q94 = sE 1637 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13
  q95 : Eqn
  q95 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q96 : Eqn
  q96 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q97 : Eqn
  q97 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q98 : Eqn
  q98 = wE 1960 W
  q99 : Eqn
  q99 = wE 1961 W

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [TOFF102 CS13 TOFF102 CSd13]: 31 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 7 q89 ∷
   rw 8 q90 ∷
   rw⁻ 10 q89 ∷
   rw 11 q91 ∷
   rw 6 q84 ∷
   rw⁻ 9 q92 ∷
   rw 10 q86 ∷
   rw 11 q84 ∷
   rw⁻ 14 q93 ∷
   rw 15 q85 ∷
   rw 2 q94 ∷
   rw⁻ 1 q95 ∷
   rw⁻ 2 q89 ∷
   rw⁻ 3 q95 ∷
   rw⁻ 4 q96 ∷
   rw 5 q91 ∷
   rw⁻ 7 q95 ∷
   rw⁻ 8 q89 ∷
   rw⁻ 9 q95 ∷
   rw⁻ 10 q97 ∷
   rw 11 q90 ∷
   rw 0 q88 ∷
   rw⁻ 1 q92 ∷
   rw⁻ 2 q93 ∷
   rw 3 q85 ∷
   rw 4 q88 ∷
   rw⁻ 5 q93 ∷
   rw⁻ 6 q92 ∷
   rw 7 q86 ∷
   rw 1 q98 ∷
   rw 3 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 173 W
  q101 : Eqn
  q101 = wE 1962 W
  q102 : Eqn
  q102 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q103 : Eqn
  q103 = wE 175 W
  q104 : Eqn
  q104 = sE 1644 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03
  q105 : Eqn
  q105 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q106 : Eqn
  q106 = wE 1963 W
  q107 : Eqn
  q107 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q108 : Eqn
  q108 = wE 1964 W

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [CS03]: 31 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03 : ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03 = derive (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q67 ∷
   rw 5 q100 ∷
   rw 6 q101 ∷
   rw⁻ 5 q102 ∷
   rw 8 q2 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q103 ∷
   rw 8 q67 ∷
   rw 1 q104 ∷
   rw⁻ 0 q105 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q67 ∷
   rw 1 q100 ∷
   rw 2 q106 ∷
   rw⁻ 1 q107 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q103 ∷
   rw 4 q67 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q67 ∷
   rw 1 q107 ∷
   rw 0 q102 ∷
   rw 1 q108 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q67 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = sE 1645 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3
  q110 : Eqn
  q110 = sE 1621 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12
  q111 : Eqn
  q111 = sE 1622 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF103 X3 CS12 X3 TOFF103 X3 CSd12]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q109 ∷
   rw 3 q110 ∷
   rw 4 q109 ∷
   rw 7 q111 ∷ []) Eq.refl
