{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD623 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D623 (W : Ws) (Sᴰ : SD623) where

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
  lem-pass-CS03-vs-X3-TOFF013-X3 : St 1426
  lem-pass-CS03-vs-X3-TOFF013-X3 = pickᴰ 0 Sᴰ
  lem-pass-CSd03-vs-X3-TOFF013-X3 : St 1427
  lem-pass-CSd03-vs-X3-TOFF013-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 4 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-CCZ013-vs-CS03 : St 1438
  lem-pass-CCZ013-vs-CS03 = pickᴰ 6 Sᴰ
  lem-pass-CCZ013-vs-CSd03 : St 1439
  lem-pass-CCZ013-vs-CSd03 = pickᴰ 7 Sᴰ
  lem-pass-CS13-vs-X3-TOFF103-X3 : St 1440
  lem-pass-CS13-vs-X3-TOFF103-X3 = pickᴰ 8 Sᴰ
  lem-pass-CSd13-vs-X3-TOFF103-X3 : St 1441
  lem-pass-CSd13-vs-X3-TOFF103-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS23-vs-CS02 : St 890
  lem-pass-CS23-vs-CS02 = pickᴰ 10 Sᴰ
  lem-pass-CS23-vs-CS03 : St 1442
  lem-pass-CS23-vs-CS03 = pickᴰ 11 Sᴰ
  lem-pass-CS23-vs-CSd02 : St 891
  lem-pass-CS23-vs-CSd02 = pickᴰ 12 Sᴰ
  lem-pass-CS23-vs-CSd03 : St 1443
  lem-pass-CS23-vs-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-CS23-vs-S0 : St 177
  lem-pass-CS23-vs-S0 = pickᴰ 14 Sᴰ
  lem-pass-CS23-vs-Sd0 : St 157
  lem-pass-CS23-vs-Sd0 = pickᴰ 15 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 17 Sᴰ
  lem-pass-CCZ123-vs-TOFF012 : St 1444
  lem-pass-CCZ123-vs-TOFF012 = pickᴰ 18 Sᴰ
  lem-pass-CS02-vs-TOFF103 : St 1445
  lem-pass-CS02-vs-TOFF103 = pickᴰ 19 Sᴰ
  lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : St 1446
  lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = pickᴰ 20 Sᴰ
  lem-pass-CS03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : St 1447
  lem-pass-CS03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = pickᴰ 21 Sᴰ
  lem-pass-CS13-vs-TOFF012 : St 1434
  lem-pass-CS13-vs-TOFF012 = pickᴰ 22 Sᴰ
  lem-pass-CSd02-vs-TOFF103 : St 1448
  lem-pass-CSd02-vs-TOFF103 = pickᴰ 23 Sᴰ
  lem-pass-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 : St 1449
  lem-pass-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 24 Sᴰ
  lem-pass-CSd03-vs-TOFF123-CS01-TOFF123-CSd01 : St 1450
  lem-pass-CSd03-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 25 Sᴰ
  lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : St 1451
  lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = pickᴰ 26 Sᴰ
  lem-pass-CSd03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : St 1452
  lem-pass-CSd03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = pickᴰ 27 Sᴰ
  lem-pass-CSd13-vs-TOFF012 : St 1436
  lem-pass-CSd13-vs-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-S0-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 : St 1453
  lem-pass-S0-CSd03-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 29 Sᴰ
  lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : St 1454
  lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = pickᴰ 30 Sᴰ
  lem-pass-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : St 1455
  lem-pass-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = pickᴰ 31 Sᴰ
  lem-pass-TOFF012-vs-X3-TOFF013-X3 : St 1437
  lem-pass-TOFF012-vs-X3-TOFF013-X3 = pickᴰ 32 Sᴰ
  lem-pass-TOFF102-vs-CCZ023 : St 1456
  lem-pass-TOFF102-vs-CCZ023 = pickᴰ 33 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1457
  lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 34 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 1458
  lem-pass-X2-CSd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 35 Sᴰ
  lem-pass-CS23-vs-TOFF012 : St 1459
  lem-pass-CS23-vs-TOFF012 = pickᴰ 36 Sᴰ
  lem-pass-CS23-vs-TOFF013 : St 1460
  lem-pass-CS23-vs-TOFF013 = pickᴰ 37 Sᴰ
  lem-pass-TOFF102-vs-X3-TOFF103-X3 : St 1461
  lem-pass-TOFF102-vs-X3-TOFF103-X3 = pickᴰ 38 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 196 W
  q8 : Eqn
  q8 = wE 1359 W
  q9 : Eqn
  q9 = wE 1360 W
  q10 : Eqn
  q10 = sE 1445 lem-pass-CS02-vs-TOFF103
  q11 : Eqn
  q11 = wE 1361 W
  q12 : Eqn
  q12 = wE 175 W

-- pass [CS02] [X3 TOFF103 X3]: 122 steps
lem-pass-CS02-vs-X3-TOFF103-X3 : ⟪ (CS02 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-X3-TOFF103-X3 = derive (CS02 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS02 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q4 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 0 q4 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q12 ∷
   rw 3 q6 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1748 W
  q14 : Eqn
  q14 = sE 1448 lem-pass-CSd02-vs-TOFF103

-- pass [CSd02] [X3 TOFF103 X3]: 122 steps
lem-pass-CSd02-vs-X3-TOFF103-X3 : ⟪ (CS02⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-X3-TOFF103-X3 = derive (CS02⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q4 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q13 ∷
   rw 1 q14 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 0 q4 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q12 ∷
   rw 3 q6 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 1437 lem-pass-TOFF012-vs-X3-TOFF013-X3
  q16 : Eqn
  q16 = sE 1427 lem-pass-CSd03-vs-X3-TOFF013-X3
  q17 : Eqn
  q17 = sE 1426 lem-pass-CS03-vs-X3-TOFF013-X3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 TOFF013 X3]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q15 ∷
   rw 2 q16 ∷
   rw 1 q15 ∷
   rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 45 W
  q19 : Eqn
  q19 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q20 : Eqn
  q20 = sE 843 lem-pass-CCZ123-vs-CS03
  q21 : Eqn
  q21 = sE 1438 lem-pass-CCZ013-vs-CS03
  q22 : Eqn
  q22 = sE 1444 lem-pass-CCZ123-vs-TOFF012
  q23 : Eqn
  q23 = wE 33 W
  q24 : Eqn
  q24 = sE 1439 lem-pass-CCZ013-vs-CSd03

-- pass [CCZ013] [TOFF012 CS03 TOFF012 CSd03]: 9 steps
lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ [])
  (rw 0 q18 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 3 q22 ∷
   rw 2 q18 ∷
   rw 3 q19 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 1092 lem-pass-CS13-vs-CS03
  q26 : Eqn
  q26 = wE 1362 W
  q27 : Eqn
  q27 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q28 : Eqn
  q28 = wE 1382 W
  q29 : Eqn
  q29 = sE 1434 lem-pass-CS13-vs-TOFF012
  q30 : Eqn
  q30 = wE 1364 W
  q31 : Eqn
  q31 = sE 1093 lem-pass-CS13-vs-CSd03

-- pass [CS13] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 26 steps
lem-pass-CS13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (CS13 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (CS13 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ [])
  (rw 0 q25 ∷
   rw 2 q26 ∷
   rw 3 q1 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q28 ∷
   rw⁻ 1 q27 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 4 q31 ∷
   rw 6 q26 ∷
   rw 7 q1 ∷
   rw 6 q27 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q28 ∷
   rw⁻ 5 q27 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q29 ∷
   rw 5 q30 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1095 lem-pass-CSd13-vs-CS03
  q33 : Eqn
  q33 = wE 1881 W
  q34 : Eqn
  q34 = sE 1436 lem-pass-CSd13-vs-TOFF012
  q35 : Eqn
  q35 = sE 1096 lem-pass-CSd13-vs-CSd03

-- pass [CSd13] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 26 steps
lem-pass-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (CS13⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (CS13⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ [])
  (rw 0 q32 ∷
   rw 2 q26 ∷
   rw 3 q1 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q33 ∷
   rw⁻ 1 q27 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q34 ∷
   rw 1 q30 ∷
   rw 4 q35 ∷
   rw 6 q26 ∷
   rw 7 q1 ∷
   rw 6 q27 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q33 ∷
   rw⁻ 5 q27 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q34 ∷
   rw 5 q30 ∷ []) Eq.refl

-- pass [CS13] [X2 TOFF012 X2 CS03 X2 TOFF012 X2 CSd03]: 26 steps
lem-pass-CS13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : ⟪ (CS13 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = derive (CS13 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ CS13 ∷ [])
  (rw 1 q26 ∷
   rw 2 q1 ∷
   rw 1 q27 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q28 ∷
   rw⁻ 0 q27 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 3 q25 ∷
   rw 5 q26 ∷
   rw 6 q1 ∷
   rw 5 q27 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q28 ∷
   rw⁻ 4 q27 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q29 ∷
   rw 4 q30 ∷
   rw 7 q31 ∷ []) Eq.refl

-- pass [CSd13] [X2 TOFF012 X2 CS03 X2 TOFF012 X2 CSd03]: 26 steps
lem-pass-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 : ⟪ (CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03 = derive (CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ CS13⁻ ∷ [])
  (rw 1 q26 ∷
   rw 2 q1 ∷
   rw 1 q27 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q33 ∷
   rw⁻ 0 q27 ∷
   rw 3 q1 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q34 ∷
   rw 0 q30 ∷
   rw 3 q32 ∷
   rw 5 q26 ∷
   rw 6 q1 ∷
   rw 5 q27 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q33 ∷
   rw⁻ 4 q27 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q34 ∷
   rw 4 q30 ∷
   rw 7 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 1456 lem-pass-TOFF102-vs-CCZ023

-- pass [CCZ023] [TOFF102]: 1 steps
lem-pass-CCZ023-vs-TOFF102 : ⟪ (CCZ023 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-TOFF102 = derive (CCZ023 ∷ Toff102 ∷ []) (Toff102 ∷ CCZ023 ∷ [])
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 861 lem-pass-CCZ123-vs-CSd03

-- pass [CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ [])
  (rw 0 q22 ∷
   rw 1 q20 ∷
   rw 2 q22 ∷
   rw 3 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 1454 lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13
  q39 : Eqn
  q39 = sE 1451 lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13
  q40 : Eqn
  q40 = sE 1446 lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q38 ∷
   rw 2 q39 ∷
   rw 1 q38 ∷
   rw 0 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 1462 W
  q42 : Eqn
  q42 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q43 : Eqn
  q43 = sE 1457 lem-pass-X2-CS20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q44 : Eqn
  q44 = wE 1463 W

-- pass [CS20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CS02 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CS02 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q41 ∷
   rw 9 q42 ∷
   rw 1 q43 ∷
   rw 7 q44 ∷
   rw⁻ 6 q42 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1466 W
  q46 : Eqn
  q46 = sE 1458 lem-pass-X2-CSd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q47 : Eqn
  q47 = wE 1467 W

-- pass [CSd20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CS02⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CS02⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q45 ∷
   rw 9 q42 ∷
   rw 1 q46 ∷
   rw 7 q47 ∷
   rw⁻ 6 q42 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = sE 1455 lem-pass-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13
  q49 : Eqn
  q49 = sE 1452 lem-pass-CSd03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13
  q50 : Eqn
  q50 = sE 1447 lem-pass-CS03-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q48 ∷
   rw 2 q49 ∷
   rw 1 q48 ∷
   rw 0 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = sE 1449 lem-pass-CSd03-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CSd03]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd03 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd03 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 1450 lem-pass-CSd03-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [TOFF123 CS01 TOFF123 CSd01] [CSd03]: 1 steps
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-CSd03 : ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-CSd03 = derive (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ [])
  (rw⁻ 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 1453 lem-pass-S0-CSd03-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [S0 CSd03]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0-CSd03 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 1441 lem-pass-CSd13-vs-X3-TOFF103-X3
  q55 : Eqn
  q55 = sE 1461 lem-pass-TOFF102-vs-X3-TOFF103-X3
  q56 : Eqn
  q56 = sE 1440 lem-pass-CS13-vs-X3-TOFF103-X3

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF103 X3]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 3 q54 ∷
   rw 2 q55 ∷
   rw 1 q56 ∷
   rw 0 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 1459 lem-pass-CS23-vs-TOFF012
  q58 : Eqn
  q58 = sE 177 lem-pass-CS23-vs-S0
  q59 : Eqn
  q59 = sE 1443 lem-pass-CS23-vs-CSd03
  q60 : Eqn
  q60 = sE 157 lem-pass-CS23-vs-Sd0
  q61 : Eqn
  q61 = sE 1442 lem-pass-CS23-vs-CS03

-- pass [CS23] [TOFF012 S0 CSd03 TOFF012 Sd0 CS03]: 6 steps
lem-pass-CS23-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 : ⟪ (CS23 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 = derive (CS23 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS23 ∷ [])
  (rw 0 q57 ∷
   rw 1 q58 ∷
   rw 2 q59 ∷
   rw 3 q57 ∷
   rw 4 q60 ∷
   rw 5 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q63 : Eqn
  q63 = wE 56 W
  q64 : Eqn
  q64 = eqn (CX10 ∷ CS23 ∷ []) (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS))
  q65 : Eqn
  q65 = sE 1460 lem-pass-CS23-vs-TOFF013
  q66 : Eqn
  q66 = sE 890 lem-pass-CS23-vs-CS02
  q67 : Eqn
  q67 = sE 891 lem-pass-CS23-vs-CSd02

-- pass [CS23] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 246 steps
lem-pass-CS23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS23 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q62 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q62 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q62 ∷
   rw 3 q63 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q26 ∷
   rw⁻ 1 q27 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q62 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q62 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q62 ∷
   rw⁻ 10 q5 ∷
   rw 3 q63 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 0 q64 ∷
   rw 1 q65 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q62 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q62 ∷
   rw 2 q63 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q27 ∷
   rw 1 q30 ∷
   rw 0 q12 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q62 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 2 q63 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q12 ∷
   rw 3 q6 ∷
   rw 3 q66 ∷
   rw 8 q1 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q62 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q62 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q62 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q62 ∷
   rw 7 q63 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q26 ∷
   rw⁻ 5 q27 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q62 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q62 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q62 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q62 ∷
   rw⁻ 14 q5 ∷
   rw 7 q63 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 4 q64 ∷
   rw 5 q65 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q62 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q62 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q62 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q62 ∷
   rw 6 q63 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 4 q27 ∷
   rw 5 q30 ∷
   rw 4 q12 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q62 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q62 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
   rw⁻ 6 q62 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 12 q62 ∷
   rw⁻ 13 q5 ∷
   rw 6 q63 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q6 ∷
   rw 7 q67 ∷ []) Eq.refl

-- pass [CS23] [X3 TOFF013 X3]: 122 steps
lem-pass-CS23-vs-X3-TOFF013-X3 : ⟪ (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF013-X3 = derive (CS23 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS23 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q62 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q62 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q62 ∷
   rw 3 q63 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q26 ∷
   rw⁻ 1 q27 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q62 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q62 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q62 ∷
   rw⁻ 10 q5 ∷
   rw 3 q63 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 0 q64 ∷
   rw 1 q65 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q62 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q62 ∷
   rw 2 q63 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q27 ∷
   rw 1 q30 ∷
   rw 0 q12 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q62 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q62 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q62 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q62 ∷
   rw⁻ 9 q5 ∷
   rw 2 q63 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q12 ∷
   rw 3 q6 ∷ []) Eq.refl
