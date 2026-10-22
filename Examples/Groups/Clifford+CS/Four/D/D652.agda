{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD652 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D652 (W : Ws) (Sᴰ : SD652) where

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
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-Sd0 : St 1428
  lem-pass-CS13-vs-Sd0 = pickᴰ 3 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 4 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 6 Sᴰ
  lem-pass-CSd13-vs-Sd0 : St 1429
  lem-pass-CSd13-vs-Sd0 = pickᴰ 7 Sᴰ
  lem-pass-CS13-vs-S3 : St 1462
  lem-pass-CS13-vs-S3 = pickᴰ 8 Sᴰ
  lem-pass-CS13-vs-Sd3 : St 1463
  lem-pass-CS13-vs-Sd3 = pickᴰ 9 Sᴰ
  lem-pass-CS13-vs-iI : St 1464
  lem-pass-CS13-vs-iI = pickᴰ 10 Sᴰ
  lem-pass-CSd13-vs-iI : St 1646
  lem-pass-CSd13-vs-iI = pickᴰ 11 Sᴰ
  lem-pass-CSd13-vs-S3 : St 1647
  lem-pass-CSd13-vs-S3 = pickᴰ 12 Sᴰ
  lem-pass-CSd13-vs-Sd3 : St 1648
  lem-pass-CSd13-vs-Sd3 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 : St 1210
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 : St 1297
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF013-X3 : St 1227
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF013-X3 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 : St 1300
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 : St 1613
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02 = pickᴰ 18 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 : St 1614
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02 = pickᴰ 19 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S0 : St 1649
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S0 = pickᴰ 20 Sᴰ
  lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1618
  lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 21 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 : St 1650
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 = pickᴰ 22 Sᴰ
  lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1626
  lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 23 Sᴰ
  lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1630
  lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 24 Sᴰ
  lem-pass-CCZ023-vs-X3-TOFF013-X3 : St 1651
  lem-pass-CCZ023-vs-X3-TOFF013-X3 = pickᴰ 25 Sᴰ
  lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 : St 1652
  lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 26 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 : St 1653
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 = pickᴰ 27 Sᴰ
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 : St 1654
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 = pickᴰ 28 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 : St 1655
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 = pickᴰ 29 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3 : St 1656
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 30 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF213-X3 : St 1657
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF213-X3 = pickᴰ 31 Sᴰ
  lem-pass-CS13-vs-X2-TOFF012-X2 : St 1658
  lem-pass-CS13-vs-X2-TOFF012-X2 = pickᴰ 32 Sᴰ
  lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : St 1659
  lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 33 Sᴰ
  lem-pass-CSd13-vs-X2-TOFF012-X2 : St 1660
  lem-pass-CSd13-vs-X2-TOFF012-X2 = pickᴰ 34 Sᴰ
  lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : St 1661
  lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 35 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : St 1662
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = pickᴰ 36 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : St 1663
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = pickᴰ 37 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : St 1664
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = pickᴰ 38 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 : St 1665
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 = pickᴰ 39 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q10 : Eqn
  q10 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q11 : Eqn
  q11 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q12 : Eqn
  q12 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q13 : Eqn
  q13 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q14 : Eqn
  q14 = eqn (Toff213 ∷ []) (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (wn 1751 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q17 : Eqn
  q17 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q19 : Eqn
  q19 = eqn (K2⁻ ∷ X3 ∷ []) (X3 ∷ K2⁻ ∷ []) (low₃-comm (((K • iI) ↑ ↑)) (X))
  q20 : Eqn
  q20 = eqn (K2⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K3⁻ ∷ []) (wn 1809 W)
  q21 : Eqn
  q21 = eqn (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) (low₃-comm (Toff) ((K • iI)))
  q22 : Eqn
  q22 = eqn (K3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2⁻ ∷ []) (wn 1810 W)
  q23 : Eqn
  q23 = eqn (CCZ023 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-X3-TOFF013-X3)
  q24 : Eqn
  q24 = eqn (K2 ∷ X3 ∷ []) (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X))
  q25 : Eqn
  q25 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wn 1811 W)
  q26 : Eqn
  q26 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (K))
  q27 : Eqn
  q27 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q28 : Eqn
  q28 = eqn (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ []) (wn 1755 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)

-- pass [TOFF203] [X3 TOFF013 X3]: 129 steps
lem-pass-TOFF203-vs-X3-TOFF013-X3 : ⟪ (Toff203 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ
lem-pass-TOFF203-vs-X3-TOFF013-X3 = derive (Toff203 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 8 q9 ∷
   rw 7 q10 ∷
   rw⁻ 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q11 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q12 ∷
   rw⁻ 3 q5 ∷
   rw 2 q12 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 0 q2 ∷
   rw 1 q13 ∷
   re 1 8 (Toff213 ∷ []) ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q15 ∷
   rw 4 q5 ∷
   rw 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q16 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q17 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q18 ∷
   rw 3 q9 ∷
   rw 2 q19 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw⁻ 4 q21 ∷
   rw 5 q22 ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q19 ∷
   rw 1 q23 ∷
   rw 0 q24 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 1 q25 ∷
   rw⁻ 2 q26 ∷
   rw 3 q27 ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q24 ∷
   rw 6 q1 ∷
   rw⁻ 5 q18 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q11 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q5 ∷
   rw 5 q12 ∷
   rw⁻ 4 q3 ∷
   rw 5 q17 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 4 q28 ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 3 q1 ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q15 ∷
   rw 7 q5 ∷
   rw 8 q15 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q16 ∷
   rw 11 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q29 ∷
   rw 4 q13 ∷
   re 4 8 (Toff213 ∷ []) ∷
   re 3 3 (Toff203 ∷ []) ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [CS03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CS03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CS03 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q32 : Eqn
  q32 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q33 : Eqn
  q33 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q34 : Eqn
  q34 = eqn (X2 ∷ CS02 ∷ []) (S0 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1962 W)
  q35 : Eqn
  q35 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q36 : Eqn
  q36 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q37 : Eqn
  q37 = eqn (X0 ∷ S0 ∷ []) (ι ∷ S0⁻ ∷ X0 ∷ []) (wn 1965 W)
  q38 : Eqn
  q38 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q39 : Eqn
  q39 = eqn (X0 ∷ CS02⁻ ∷ []) (S2⁻ ∷ CS02 ∷ X0 ∷ []) (wn 1966 W)
  q40 : Eqn
  q40 = eqn (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) (wn 153 W)
  q41 : Eqn
  q41 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03)
  q42 : Eqn
  q42 = eqn (ι ∷ []) (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q43 : Eqn
  q43 = eqn (X3 ∷ ι3 ∷ []) (ι3 ∷ X3 ∷ []) (wn 1967 W)
  q44 : Eqn
  q44 = eqn (ι3 ∷ []) (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))
  q45 : Eqn
  q45 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q46 : Eqn
  q46 = eqn (X3 ∷ S3⁻ ∷ []) (ι3 ∷ ι3 ∷ ι3 ∷ S3 ∷ X3 ∷ []) (wn 1968 W)
  q47 : Eqn
  q47 = eqn (X0 ∷ ι ∷ []) (ι ∷ X0 ∷ []) (wn 1969 W)
  q48 : Eqn
  q48 = eqn (X0 ∷ S0⁻ ∷ []) (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) (wn 1970 W)
  q49 : Eqn
  q49 = eqn (X0 ∷ S3 ∷ []) (S3 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑ ↑)))
  q50 : Eqn
  q50 = eqn (S3⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S2⁻ ∷ []) (wn 689 W)
  q51 : Eqn
  q51 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q52 : Eqn
  q52 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q54 : Eqn
  q54 = eqn (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ []) (CS02 ∷ []) (wn 1971 W)

-- pass [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3] [CS03]: 76 steps
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CS03 : ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CS03 = derive (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ [])
  (rw 9 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q32 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   rw⁻ 7 q35 ∷
   rw 10 q31 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q36 ∷
   rw 10 q32 ∷
   rw 6 q37 ∷
   rw 10 q31 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q32 ∷
   rw 8 q38 ∷
   rw 9 q39 ∷
   rw 8 q40 ∷
   rw 11 q31 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q38 ∷
   rw 11 q32 ∷
   rw 2 q41 ∷
   rw 2 q42 ∷
   rw 1 q43 ∷
   rw 1 q44 ∷
   rw⁻ 2 q45 ∷
   rw 3 q46 ∷
   rw 3 q44 ∷
   rw 4 q44 ∷
   rw 5 q44 ∷
   rw 9 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q32 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   rw⁻ 7 q35 ∷
   rw 10 q31 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q36 ∷
   rw 10 q32 ∷
   rw 0 q47 ∷
   rw 1 q48 ∷
   rw 5 q47 ∷
   rw 6 q47 ∷
   rw 7 q47 ∷
   rw 8 q49 ∷
   rw 9 q37 ∷
   rw 13 q31 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q32 ∷
   rw 11 q38 ∷
   rw 12 q39 ∷
   rw 11 q40 ∷
   rw 14 q31 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q38 ∷
   rw 14 q32 ∷
   rw 13 q31 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q32 ∷
   rw 11 q50 ∷
   rw 10 q51 ∷
   rw 9 q52 ∷
   rw 8 q53 ∷
   rw 7 q52 ∷
   rw 6 q52 ∷
   rw 5 q52 ∷
   rw 4 q35 ∷
   rw 3 q52 ∷
   rw 2 q52 ∷
   rw 1 q52 ∷
   rw 0 q52 ∷
   rw 1 q54 ∷
   rw 2 q31 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q32 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03)
  q56 : Eqn
  q56 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q57 : Eqn
  q57 = eqn (X2 ∷ CS02⁻ ∷ []) (S0⁻ ∷ CS02 ∷ X2 ∷ []) (wn 1963 W)
  q58 : Eqn
  q58 = eqn (S0 ∷ S0⁻ ∷ CS02 ∷ []) (CS02 ∷ []) (wn 1964 W)

-- pass [X3 CS13 TOFF102 CSd13 TOFF102 X3] [CS03]: 31 steps
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 : ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 = derive (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  (rw 7 q31 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q32 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   rw⁻ 5 q35 ∷
   rw 8 q31 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q36 ∷
   rw 8 q32 ∷
   rw 1 q55 ∷
   rw⁻ 0 q56 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q32 ∷
   rw 1 q33 ∷
   rw 2 q57 ∷
   rw⁻ 1 q51 ∷
   rw 4 q31 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q32 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q32 ∷
   rw 1 q51 ∷
   rw 0 q35 ∷
   rw 1 q58 ∷
   rw 2 q31 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q32 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2)
  q60 : Eqn
  q60 = eqn (CS13⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2)
  q61 : Eqn
  q61 = eqn (CS13 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2)

-- pass [CS13 TOFF102 CSd13 TOFF102] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 4 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 3 q59 ∷
   rw 2 q60 ∷
   rw 1 q59 ∷
   rw 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3)
  q63 : Eqn
  q63 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S0)
  q64 : Eqn
  q64 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd02)
  q65 : Eqn
  q65 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0)
  q66 : Eqn
  q66 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02 ∷ []) (CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS02)

-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02]: 6 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 0 q62 ∷
   rw 5 q63 ∷
   rw 6 q64 ∷
   rw 7 q62 ∷
   rw 12 q65 ∷
   rw 13 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [CSd03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CSd03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CSd03 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [S0 CSd03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (CS13 ∷ ι ∷ []) (ι ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI)
  q70 : Eqn
  q70 = eqn (CS13 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd0)
  q71 : Eqn
  q71 = eqn (CS13 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd3)
  q72 : Eqn
  q72 = eqn (CS13 ∷ CS03 ∷ []) (CS03 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS03)
  q73 : Eqn
  q73 = eqn (CS13 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-X2-TOFF012-X2)
  q74 : Eqn
  q74 = eqn (CS13 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0)
  q75 : Eqn
  q75 = eqn (CS13 ∷ S3 ∷ []) (S3 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S3)
  q76 : Eqn
  q76 = eqn (CS13 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd03)

-- pass [CS13] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (CS13 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ [])
  (rw 0 q69 ∷
   rw 1 q70 ∷
   rw 2 q71 ∷
   rw 3 q72 ∷
   rw 4 q73 ∷
   rw 7 q69 ∷
   rw 8 q69 ∷
   rw 9 q69 ∷
   rw 10 q74 ∷
   rw 11 q75 ∷
   rw 12 q76 ∷
   rw 13 q73 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CS13⁻ ∷ ι ∷ []) (ι ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI)
  q78 : Eqn
  q78 = eqn (CS13⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-Sd0)
  q79 : Eqn
  q79 = eqn (CS13⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-Sd3)
  q80 : Eqn
  q80 = eqn (CS13⁻ ∷ CS03 ∷ []) (CS03 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CS03)
  q81 : Eqn
  q81 = eqn (CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-X2-TOFF012-X2)
  q82 : Eqn
  q82 = eqn (CS13⁻ ∷ S0 ∷ []) (S0 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S0)
  q83 : Eqn
  q83 = eqn (CS13⁻ ∷ S3 ∷ []) (S3 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S3)
  q84 : Eqn
  q84 = eqn (CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CSd03)

-- pass [CSd13] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (CS13⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ [])
  (rw 0 q77 ∷
   rw 1 q78 ∷
   rw 2 q79 ∷
   rw 3 q80 ∷
   rw 4 q81 ∷
   rw 7 q77 ∷
   rw 8 q77 ∷
   rw 9 q77 ∷
   rw 10 q82 ∷
   rw 11 q83 ∷
   rw 12 q84 ∷
   rw 13 q81 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3)
  q86 : Eqn
  q86 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3)
  q87 : Eqn
  q87 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3)

-- Bar(SSKSKK;3,2->0) passes Fredkin WBar(SSKSKK;~3,0->1): 7 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q85 ∷
   rw 3 q86 ∷
   rw 6 q85 ∷
   rw 9 q87 ∷
   rw 40 q85 ∷
   rw 43 q86 ∷
   rw 46 q85 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (Toff213 ∷ []) (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (wn 1389 W)
  q89 : Eqn
  q89 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q90 : Eqn
  q90 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q91 : Eqn
  q91 = eqn (X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) (wn 1764 W)
  q92 : Eqn
  q92 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF213-X3
  q93 : Eqn
  q93 = eqn (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ X2 ∷ []) (wn 1765 W)
  q94 : Eqn
  q94 = eqn (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (Toff213 ∷ []) (wn 1392 W)

-- pass [TOFF213] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3]: 165 steps
lem-pass-TOFF213-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ
lem-pass-TOFF213-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = derive (Toff213 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ Toff213 ∷ [])
  (rw 0 q88 ∷
   rw 36 q31 ∷
   rw 35 q33 ∷
   rw 34 q89 ∷
   rw 33 q89 ∷
   rw 32 q90 ∷
   rw 31 q89 ∷
   rw 30 q90 ∷
   rw 29 q90 ∷
   re 28 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 30 q32 ∷
   rw 27 q90 ∷
   rw 26 q90 ∷
   rw 25 q90 ∷
   rw 24 q90 ∷
   rw 23 q90 ∷
   rw 22 q90 ∷
   rw 21 q35 ∷
   rw 20 q89 ∷
   rw 19 q90 ∷
   rw 18 q90 ∷
   rw 17 q90 ∷
   rw 16 q35 ∷
   rw 15 q89 ∷
   rw 14 q35 ∷
   rw 13 q89 ∷
   re 12 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 14 q32 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q32 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q32 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q32 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q32 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q32 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q32 ∷
   rw 5 q33 ∷
   rw 4 q33 ∷
   rw 5 q91 ∷
   rw 6 q31 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q31 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 8 q31 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 9 q31 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 10 q31 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 11 q31 ∷
   re 9 3 (CK31 ∷ []) ∷
   rw 12 q31 ∷
   re 10 3 (CX30 ∷ []) ∷
   rw⁻ 11 q89 ∷
   rw⁻ 12 q35 ∷
   rw⁻ 13 q89 ∷
   rw⁻ 14 q35 ∷
   rw⁻ 15 q90 ∷
   rw⁻ 16 q90 ∷
   rw⁻ 17 q90 ∷
   rw⁻ 18 q89 ∷
   rw⁻ 19 q35 ∷
   rw⁻ 20 q90 ∷
   rw⁻ 21 q90 ∷
   rw⁻ 22 q90 ∷
   rw⁻ 23 q90 ∷
   rw⁻ 24 q90 ∷
   rw⁻ 25 q90 ∷
   rw 28 q31 ∷
   re 26 3 (CX30 ∷ []) ∷
   rw⁻ 27 q90 ∷
   rw⁻ 28 q90 ∷
   rw⁻ 29 q89 ∷
   rw⁻ 30 q90 ∷
   rw⁻ 31 q89 ∷
   rw⁻ 32 q89 ∷
   rw 33 q36 ∷
   rw 34 q32 ∷
   rw⁻ 1 q92 ∷
   rw 30 q31 ∷
   rw 29 q89 ∷
   rw 28 q89 ∷
   rw 27 q90 ∷
   rw 26 q89 ∷
   rw 25 q90 ∷
   rw 24 q90 ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 25 q32 ∷
   rw 22 q90 ∷
   rw 21 q90 ∷
   rw 20 q90 ∷
   rw 19 q90 ∷
   rw 18 q90 ∷
   rw 17 q90 ∷
   rw 16 q35 ∷
   rw 15 q89 ∷
   rw 14 q90 ∷
   rw 13 q90 ∷
   rw 12 q90 ∷
   rw 11 q35 ∷
   rw 10 q89 ∷
   rw 9 q35 ∷
   rw 8 q89 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 9 q32 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q32 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q32 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q32 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q32 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q32 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q32 ∷
   rw 0 q33 ∷
   rw 1 q93 ∷
   rw 0 q36 ∷
   rw 3 q31 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q31 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 5 q31 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 6 q31 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q31 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 8 q31 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 9 q31 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw⁻ 8 q89 ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q89 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q90 ∷
   rw⁻ 13 q90 ∷
   rw⁻ 14 q90 ∷
   rw⁻ 15 q89 ∷
   rw⁻ 16 q35 ∷
   rw⁻ 17 q90 ∷
   rw⁻ 18 q90 ∷
   rw⁻ 19 q90 ∷
   rw⁻ 20 q90 ∷
   rw⁻ 21 q90 ∷
   rw⁻ 22 q90 ∷
   rw 25 q31 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw⁻ 24 q90 ∷
   rw⁻ 25 q90 ∷
   rw⁻ 26 q89 ∷
   rw⁻ 27 q90 ∷
   rw⁻ 28 q89 ∷
   rw⁻ 29 q89 ∷
   rw 30 q36 ∷
   rw 31 q36 ∷
   rw 32 q32 ∷
   rw 31 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF013-X3)
  q96 : Eqn
  q96 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3)
  q97 : Eqn
  q97 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3)

-- Bar(SSSKSS;3,2->0) passes Fredkin WBar(SSKSKK;~3,0->1): 7 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶1⟩ = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ Toff103 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 0 q95 ∷
   rw 3 q96 ∷
   rw 6 q95 ∷
   rw 9 q97 ∷
   rw 40 q95 ∷
   rw 43 q96 ∷
   rw 46 q95 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3)

-- Bar(SSKSKK;3,1->0) passes factors of X3 TOFF203 X3: 1 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-TOFF203-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-TOFF203-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q98 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3)

-- Bar(SSKSKK;3,1->0) passes factors of X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3: 1 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3)

-- Bar(SSKSKK;3,1->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3: 1 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q100 ∷ []) Eq.refl
