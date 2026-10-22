{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD744 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D744 (W : Ws) (Sᴰ : SD744) where

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
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2205
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 0 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 1 Sᴰ
  lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2515
  lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 2 Sᴰ
  lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ : St 2516
  lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩ = pickᴰ 3 Sᴰ
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ : St 2517
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩ = pickᴰ 4 Sᴰ
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : St 2518
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = pickᴰ 5 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 6 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2519
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2520
  lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2521
  lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 9 Sᴰ
  lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2522
  lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 10 Sᴰ
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2523
  lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 2524
  lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 12 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : St 2525
  lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2526
  lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 14 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2527
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 15 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2528
  lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 16 Sᴰ
  lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2529
  lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 17 Sᴰ
  lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2530
  lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 18 Sᴰ
  lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2531
  lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 19 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2532
  lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 20 Sᴰ
  lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2533
  lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 21 Sᴰ
  lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : St 2534
  lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = pickᴰ 22 Sᴰ
  lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2535
  lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 2536
  lem-pass-X2-CK21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 24 Sᴰ
  lem-pass-X3-CS30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : St 2537
  lem-pass-X3-CS30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = pickᴰ 25 Sᴰ
  lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : St 2538
  lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = pickᴰ 26 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : St 2539
  lem-pass-X2-CKd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = pickᴰ 27 Sᴰ
  lem-pass-X3-CK32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2540
  lem-pass-X3-CK32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 28 Sᴰ
  lem-pass-X3-CKd32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2541
  lem-pass-X3-CKd32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 29 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q6 : Eqn
  q6 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ CK30 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)
  q8 : Eqn
  q8 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CK30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (CK30 ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (CK30 ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30 ∷ [])
  (rw 1 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q7 ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 15 q3 ∷
   rw 16 q8 ∷
   rw 15 q6 ∷
   rw 18 q2 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 0 q1 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q10 : Eqn
  q10 = eqn (X3 ∷ CS03 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0)
  q11 : Eqn
  q11 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CS30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (CS03 ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (CS03 ∷ X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03 ∷ [])
  (rw 1 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q10 ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 15 q3 ∷
   rw 16 q11 ∷
   rw 15 q6 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 0 q1 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q15 : Eqn
  q15 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3)
  q16 : Eqn
  q16 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (CK20⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 0 q13 ∷
   rw 13 q14 ∷
   rw 1 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q14 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3)

-- pass [CS20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (CS02 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (CS02 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q9 ∷
   rw 13 q14 ∷
   rw 1 q17 ∷
   rw 11 q11 ∷
   rw⁻ 10 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (K1 ∷ X3 ∷ []) (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑)))
  q20 : Eqn
  q20 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q21 : Eqn
  q21 = eqn (K1⁻ ∷ X3 ∷ []) (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑)))
  q22 : Eqn
  q22 = eqn (S1 ∷ K1 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CK31 ∷ []) (wn 2225 W)
  q23 : Eqn
  q23 = eqn (K1⁻ ∷ S1⁻ ∷ []) (CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2226 W)
  q24 : Eqn
  q24 = eqn (CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3)
  q25 : Eqn
  q25 = eqn (CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3)
  q26 : Eqn
  q26 = eqn (CS13 ∷ CK31 ∷ CK31⁻ ∷ CS13⁻ ∷ []) [] (wn 2227 W)

-- ca-split Gad(t=1, W=(3,), d=SK, e=-1) 3: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = derive (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw⁻ 0 q18 ∷
   rw⁻ 1 q19 ∷
   rw 8 q20 ∷
   rw 7 q21 ∷
   rw 0 q22 ∷
   rw 14 q23 ∷
   rw 7 q24 ∷
   rw 6 q25 ∷
   rw 12 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1466 W)
  q28 : Eqn
  q28 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1)
  q29 : Eqn
  q29 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) (wn 1467 W)

-- pass [CSd30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CSd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q27 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q28 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q29 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1)

-- pass [CKd30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CKd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q13 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q30 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q16 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X3 ∷ CK30 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1)

-- pass [CK30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CK30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (CK30 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (CK30 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q31 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q8 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X3 ∷ CS03 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1)

-- pass [CS30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CS30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (CS03 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (CS03 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q32 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q11 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1497 W)
  q34 : Eqn
  q34 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1498 W)
  q35 : Eqn
  q35 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X2 CKd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q33 ∷
   rw 1 q34 ∷
   rw 1 q35 ∷
   rw 5 q34 ∷
   rw 5 q33 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2267 W)
  q37 : Eqn
  q37 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2268 W)
  q38 : Eqn
  q38 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2308 W)
  q39 : Eqn
  q39 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [X1 CKd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 2 q39 ∷
   rw 6 q38 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (CS01⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1821 W)
  q41 : Eqn
  q41 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q42 : Eqn
  q42 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q43 : Eqn
  q43 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3)
  q44 : Eqn
  q44 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ []) (wn 1822 W)

-- pass [CSd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  (rw 0 q40 ∷
   rw 18 q41 ∷
   rw 19 q42 ∷
   rw 1 q43 ∷
   rw 17 q44 ∷
   rw⁻ 16 q42 ∷
   rw⁻ 15 q41 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (CK10⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2415 W)
  q46 : Eqn
  q46 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3)
  q47 : Eqn
  q47 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ []) (wn 2416 W)

-- pass [CKd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ [])
  (rw 0 q45 ∷
   rw 18 q41 ∷
   rw 19 q42 ∷
   rw 1 q46 ∷
   rw 17 q47 ∷
   rw⁻ 16 q42 ∷
   rw⁻ 15 q41 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2160 W)
  q49 : Eqn
  q49 = eqn (X1 ∷ CK10 ∷ X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2161 W)
  q50 : Eqn
  q50 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2417 W)
  q51 : Eqn
  q51 = eqn (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q52 : Eqn
  q52 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2418 W)

-- pass [X1 CK10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 11 steps
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   rw 18 q51 ∷
   rw 15 q39 ∷
   rw 12 q51 ∷
   rw 9 q51 ∷
   rw 6 q39 ∷
   rw 10 q52 ∷
   rw 14 q48 ∷
   rw 15 q49 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1680 W)
  q54 : Eqn
  q54 = eqn (X1 ∷ CS01 ∷ X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1669 W)
  q55 : Eqn
  q55 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2419 W)
  q56 : Eqn
  q56 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2420 W)

-- pass [X1 CS10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 9 steps
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q53 ∷
   rw 1 q54 ∷
   rw 2 q55 ∷
   rw 12 q51 ∷
   rw 9 q39 ∷
   rw 6 q51 ∷
   rw 10 q56 ∷
   rw 14 q53 ∷
   rw 15 q54 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2)

-- pass [CSd30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q27 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q57 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q29 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2)

-- pass [CKd30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CKd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q13 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q58 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q16 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (CK30⁻ ∷ []) ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (X3 ∷ CK30 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2)

-- pass [CK30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CK30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CK30 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (CK30 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q59 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q8 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X3 ∷ CS03 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2)

-- pass [CS30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CS30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CS03 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (CS03 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q60 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q11 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1833 W)

-- pass [X2 CKd21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q61 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 2 q35 ∷
   rw 6 q34 ∷
   rw 6 q61 ∷
   rw 7 q33 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CK21 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1476 W)
  q63 : Eqn
  q63 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3)
  q64 : Eqn
  q64 = eqn (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ []) (wn 1477 W)

-- pass [CK21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (CK21 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  (rw 0 q62 ∷
   rw 9 q14 ∷
   rw 1 q63 ∷
   rw 7 q64 ∷
   rw⁻ 6 q14 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q66 : Eqn
  q66 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q67 : Eqn
  q67 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q68 : Eqn
  q68 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q69 : Eqn
  q69 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q70 : Eqn
  q70 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q71 : Eqn
  q71 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (CK31 ∷ CS12 ∷ CK31⁻ ∷ CS12⁻ ∷ []) (wn 2004 W)
  q72 : Eqn
  q72 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q73 : Eqn
  q73 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q74 : Eqn
  q74 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q75 : Eqn
  q75 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q76 : Eqn
  q76 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q77 : Eqn
  q77 = eqn (CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CS02⁻ ∷ []) (lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩)
  q78 : Eqn
  q78 = eqn (CK30⁻ ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ []) (lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3)
  q79 : Eqn
  q79 = eqn (CS02 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS02 ∷ []) (lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩)
  q80 : Eqn
  q80 = eqn (CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ []) (lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q81 : Eqn
  q81 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q82 : Eqn
  q82 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q83 : Eqn
  q83 = eqn (CK31 ∷ CS12 ∷ CK31⁻ ∷ CS12⁻ ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 2005 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 140 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 29 q65 ∷
   rw 28 q66 ∷
   rw 27 q66 ∷
   rw 26 q67 ∷
   rw 25 q66 ∷
   rw 24 q67 ∷
   rw 23 q67 ∷
   rw⁻ 22 q68 ∷
   rw 21 q67 ∷
   rw 20 q67 ∷
   rw 19 q67 ∷
   rw 18 q67 ∷
   rw 17 q67 ∷
   rw 16 q67 ∷
   rw⁻ 15 q69 ∷
   rw 14 q66 ∷
   rw 13 q67 ∷
   rw 12 q67 ∷
   rw 11 q67 ∷
   rw⁻ 10 q69 ∷
   rw 9 q66 ∷
   rw⁻ 8 q69 ∷
   rw 7 q66 ∷
   rw⁻ 6 q68 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q70 ∷
   rw 6 q66 ∷
   rw⁻ 5 q70 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q70 ∷
   rw 5 q66 ∷
   rw⁻ 4 q70 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q70 ∷
   rw 4 q67 ∷
   rw⁻ 3 q70 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q70 ∷
   rw 3 q66 ∷
   rw⁻ 2 q70 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q70 ∷
   rw 2 q67 ∷
   rw⁻ 1 q70 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q70 ∷
   rw 1 q67 ∷
   rw⁻ 0 q70 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q71 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q70 ∷
   rw 1 q72 ∷
   rw 2 q70 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 1 q73 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q70 ∷
   rw 3 q74 ∷
   rw 4 q70 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q75 ∷
   rw 4 q76 ∷
   rw 3 q77 ∷
   rw 2 q78 ∷
   rw 1 q79 ∷
   rw 0 q80 ∷
   rw 10 q65 ∷
   rw 9 q81 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q70 ∷
   rw 9 q82 ∷
   rw⁻ 8 q70 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw 7 q67 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q70 ∷
   rw 7 q66 ∷
   rw⁻ 6 q70 ∷
   re 7 3 (CK31 ∷ []) ∷
   rw 7 q83 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q70 ∷
   rw 7 q73 ∷
   rw 8 q70 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q70 ∷
   rw 8 q73 ∷
   rw 9 q70 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q70 ∷
   rw 9 q72 ∷
   rw 10 q70 ∷
   re 8 3 (CK30 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q70 ∷
   rw 10 q73 ∷
   rw 11 q70 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q70 ∷
   rw 11 q72 ∷
   rw 12 q70 ∷
   re 10 3 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q70 ∷
   rw 12 q72 ∷
   rw 13 q70 ∷
   re 11 3 (CK30 ∷ []) ∷
   rw 12 q68 ∷
   rw 13 q72 ∷
   rw 14 q69 ∷
   rw 15 q72 ∷
   rw 16 q69 ∷
   rw 17 q73 ∷
   rw 18 q73 ∷
   rw 19 q73 ∷
   rw 20 q72 ∷
   rw 21 q69 ∷
   rw 22 q73 ∷
   rw 23 q73 ∷
   rw 24 q73 ∷
   rw 25 q73 ∷
   rw 26 q73 ∷
   rw 27 q73 ∷
   rw 28 q68 ∷
   rw 29 q73 ∷
   rw 30 q73 ∷
   rw 31 q72 ∷
   rw 32 q73 ∷
   rw 33 q72 ∷
   rw 34 q72 ∷
   rw 35 q76 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (CK32⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1674 W)
  q85 : Eqn
  q85 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q86 : Eqn
  q86 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ []) (wn 1675 W)

-- pass [CKd32] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CK32⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CK32⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 0 q84 ∷
   rw 1 q85 ∷
   rw 9 q86 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3)
  q88 : Eqn
  q88 = eqn (CCZ123 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ CCZ123 ∷ []) (lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩)
  q89 : Eqn
  q89 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [CCZ123] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CCZ123 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CCZ123 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 1 q87 ∷
   rw 0 q88 ∷
   rw⁻ 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (CK32 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (wn 1409 W)
  q91 : Eqn
  q91 = eqn (X3 ∷ CK32 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q92 : Eqn
  q92 = eqn (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ []) (wn 1410 W)

-- pass [CK32] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CK32 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CK32 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32 ∷ [])
  (rw 0 q90 ∷
   rw 1 q91 ∷
   rw 9 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = eqn (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1459 W)
  q94 : Eqn
  q94 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3)
  q95 : Eqn
  q95 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q96 : Eqn
  q96 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q97 : Eqn
  q97 = eqn (K0 ∷ []) (K0 ∷ []) (wn 1460 W)
  q98 : Eqn
  q98 = eqn (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) (wn 1461 W)

-- CA CK20 Gad(t=0, W=(3,), d=Kd, e=-1): 7 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ : ⟪ (CK20 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ = derive (CK20 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK20 ∷ [])
  (rw 0 q93 ∷
   rw 1 q94 ∷
   rw 0 q95 ∷
   rw 1 q96 ∷
   rw 5 q97 ∷
   rw 5 q95 ∷
   rw 6 q98 ∷ []) Eq.refl
