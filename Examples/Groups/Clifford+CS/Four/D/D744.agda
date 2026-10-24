{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD744 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D744 (W : Ws) (Sᴰ : SD744) where

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
  q1 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 1407 W
  q6 : Eqn
  q6 = wE 175 W
  q7 : Eqn
  q7 = sE 2520 lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0
  q8 : Eqn
  q8 = wE 1408 W

-- pass [CK30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CK30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乑丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乑") ⟫ʷ
lem-pass-CK30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乑丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乑")
  (rw 1 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q7 ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q4 ∷
   rw 15 q3 ∷
   rw 16 q8 ∷
   rw 15 q6 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q4 ∷
   rw⁻ 0 q1 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1462 W
  q10 : Eqn
  q10 = sE 2521 lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0
  q11 : Eqn
  q11 = wE 1463 W

-- pass [CS30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CS30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "中丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中") ⟫ʷ
lem-pass-CS30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "中丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞中")
  (rw 1 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q10 ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   rw 15 q3 ∷
   rw 16 q11 ∷
   rw 15 q6 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q4 ∷
   rw⁻ 0 q1 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = sE 2519 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "中九丮九丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "中九丮九丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞中九丮九")
  (rw⁻ 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1464 W
  q14 : Eqn
  q14 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q15 : Eqn
  q15 = sE 2526 lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q16 : Eqn
  q16 = wE 1465 W

-- pass [CKd20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "久丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "久丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞久")
  (rw 0 q13 ∷
   rw 13 q14 ∷
   rw 1 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q14 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 2528 lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3

-- pass [CS20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丧丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丧丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丧")
  (rw 0 q9 ∷
   rw 13 q14 ∷
   rw 1 q17 ∷
   rw 11 q11 ∷
   rw⁻ 10 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q22 : Eqn
  q22 = wE 2225 W
  q23 : Eqn
  q23 = wE 2226 W
  q24 : Eqn
  q24 = sE 2515 lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q25 : Eqn
  q25 = sE 2522 lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q26 : Eqn
  q26 = wE 2227 W

-- ca-split Gad(t=1, W=(3,), d=SK, e=-1) 3: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : ⟪ (ℓ "丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = derive (ℓ "丞与丐丽习举习丑丏丞") (ℓ "丞丽丞丞乔丞丞丽习举习丞丞乕丞丞举丞")
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
  q27 = wE 1466 W
  q28 : Eqn
  q28 = sE 2534 lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1
  q29 : Eqn
  q29 = wE 1467 W

-- pass [CSd30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CSd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "丮丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞丮") ⟫ʷ
lem-pass-CSd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "丮丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞丮")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q27 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q28 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q29 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "丮") ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 2531 lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1

-- pass [CKd30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CKd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乒丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乒") ⟫ʷ
lem-pass-CKd30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乒丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乒")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q4 ∷
   rw 1 q13 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q30 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q16 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乒") ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 2529 lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1

-- pass [CK30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CK30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "乑丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞乑") ⟫ʷ
lem-pass-CK30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "乑丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞乑")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q31 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q8 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 2533 lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1

-- pass [CS30] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 23 steps
lem-pass-CS30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (ℓ "中丞与丐丽习举习丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐丽习举习丑丏丞中") ⟫ʷ
lem-pass-CS30-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (ℓ "中丞与丐丽习举习丑丏丞") (ℓ "丞与丐丽习举习丑丏丞中")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q32 ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q4 ∷
   rw 9 q3 ∷
   rw 10 q11 ∷
   rw 9 q6 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q4 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1497 W
  q34 : Eqn
  q34 = wE 1498 W
  q35 : Eqn
  q35 = sE 2527 lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X2 CKd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "丘么丘丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "丘么丘丞丽习举习丞") (ℓ "丞丽习举习丞丘么丘")
  (rw 0 q33 ∷
   rw 1 q34 ∷
   rw 1 q35 ∷
   rw 5 q34 ∷
   rw 5 q33 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 2267 W
  q37 : Eqn
  q37 = wE 2268 W
  q38 : Eqn
  q38 = wE 2308 W
  q39 : Eqn
  q39 = sE 2523 lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X1 CKd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丒丵丒丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丒丵丒丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丒丵丒")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 2 q39 ∷
   rw 6 q38 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1821 W
  q41 : Eqn
  q41 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q42 : Eqn
  q42 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q43 : Eqn
  q43 = sE 2525 lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q44 : Eqn
  q44 = wE 1822 W

-- pass [CSd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (ℓ "両丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞両") ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (ℓ "両丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞両")
  (rw 0 q40 ∷
   rw 18 q41 ∷
   rw 19 q42 ∷
   rw 1 q43 ∷
   rw 17 q44 ∷
   rw⁻ 16 q42 ∷
   rw⁻ 15 q41 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 2415 W
  q46 : Eqn
  q46 = sE 2524 lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3
  q47 : Eqn
  q47 = wE 2416 W

-- pass [CKd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (ℓ "丵丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞丵") ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = derive (ℓ "丵丒丘丞三下丈丈中九丮九三三上丈丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞丵")
  (rw 0 q45 ∷
   rw 18 q41 ∷
   rw 19 q42 ∷
   rw 1 q46 ∷
   rw 17 q47 ∷
   rw⁻ 16 q42 ∷
   rw⁻ 15 q41 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 2160 W
  q49 : Eqn
  q49 = wE 2161 W
  q50 : Eqn
  q50 = wE 2417 W
  q51 : Eqn
  q51 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q52 : Eqn
  q52 = wE 2418 W

-- pass [X1 CK10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 11 steps
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "丒临丒丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "丒临丒丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丒临丒")
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
  q53 = wE 1680 W
  q54 : Eqn
  q54 = wE 1669 W
  q55 : Eqn
  q55 = wE 2419 W
  q56 : Eqn
  q56 = wE 2420 W

-- pass [X1 CS10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 9 steps
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "丒丠丒丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "丒丠丒丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞丒丠丒")
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
  q57 = sE 2535 lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2

-- pass [CSd30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "丮丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞丮") ⟫ʷ
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "丮丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞丮")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q4 ∷
   rw 1 q27 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q57 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏丨乏") ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q29 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "丮") ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 2532 lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2

-- pass [CKd30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CKd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乒丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乒") ⟫ʷ
lem-pass-CKd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乒丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乒")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q4 ∷
   rw 1 q13 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q58 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏久乏") ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q16 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "乒") ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 2530 lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2

-- pass [CK30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CK30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "乑丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乑") ⟫ʷ
lem-pass-CK30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "乑丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞乑")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q59 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q8 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2537 lem-pass-X3-CS30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2

-- pass [CS30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CS30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "中丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中") ⟫ʷ
lem-pass-CS30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "中丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞中")
  (rw 2 q2 ∷
   rw 1 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q6 ∷
   rw 4 q4 ∷
   rw 1 q60 ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q11 ∷
   rw 13 q6 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q4 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 1833 W

-- pass [X2 CKd21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "丘么丘丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "丘么丘丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞丘么丘")
  (rw 0 q61 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 2 q35 ∷
   rw 6 q34 ∷
   rw 6 q61 ∷
   rw 7 q33 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 1476 W
  q63 : Eqn
  q63 = sE 2536 lem-pass-X2-CK21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q64 : Eqn
  q64 = wE 1477 W

-- pass [CK21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "乇丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "乇丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞乇")
  (rw 0 q62 ∷
   rw 9 q14 ∷
   rw 1 q63 ∷
   rw 7 q64 ∷
   rw⁻ 6 q14 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 5 W
  q66 : Eqn
  q66 = wE 140 W
  q67 : Eqn
  q67 = wE 7 W
  q68 : Eqn
  q68 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q69 : Eqn
  q69 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q70 : Eqn
  q70 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q71 : Eqn
  q71 = wE 2004 W
  q72 : Eqn
  q72 = wE 142 W
  q73 : Eqn
  q73 = wE 27 W
  q74 : Eqn
  q74 = wE 139 W
  q75 : Eqn
  q75 = wE 29 W
  q76 : Eqn
  q76 = wE 31 W
  q77 : Eqn
  q77 = sE 2517 lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡-1⟩
  q78 : Eqn
  q78 = sE 2538 lem-pass-CKd30-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3
  q79 : Eqn
  q79 = sE 2516 lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡-1⟩
  q80 : Eqn
  q80 = sE 2205 lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q81 : Eqn
  q81 = wE 76 W
  q82 : Eqn
  q82 = wE 137 W
  q83 : Eqn
  q83 = wE 2005 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 140 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中九丮九丞") (ℓ "丞中九丮九丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
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
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q70 ∷
   rw 6 q66 ∷
   rw⁻ 5 q70 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q70 ∷
   rw 5 q66 ∷
   rw⁻ 4 q70 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q70 ∷
   rw 4 q67 ∷
   rw⁻ 3 q70 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q70 ∷
   rw 3 q66 ∷
   rw⁻ 2 q70 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q70 ∷
   rw 2 q67 ∷
   rw⁻ 1 q70 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q70 ∷
   rw 1 q67 ∷
   rw⁻ 0 q70 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q71 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 0 q70 ∷
   rw 1 q72 ∷
   rw 2 q70 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q73 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q70 ∷
   rw 3 q74 ∷
   rw 4 q70 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q75 ∷
   rw 4 q76 ∷
   rw 3 q77 ∷
   rw 2 q78 ∷
   rw 1 q79 ∷
   rw 0 q80 ∷
   rw 10 q65 ∷
   rw 9 q81 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q70 ∷
   rw 9 q82 ∷
   rw⁻ 8 q70 ∷
   re 9 3 (ℓ "乕") ∷
   rw 7 q67 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q70 ∷
   rw 7 q66 ∷
   rw⁻ 6 q70 ∷
   re 7 3 (ℓ "乔") ∷
   rw 7 q83 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q70 ∷
   rw 7 q73 ∷
   rw 8 q70 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q70 ∷
   rw 8 q73 ∷
   rw 9 q70 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q70 ∷
   rw 9 q72 ∷
   rw 10 q70 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q70 ∷
   rw 10 q73 ∷
   rw 11 q70 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q70 ∷
   rw 11 q72 ∷
   rw 12 q70 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q70 ∷
   rw 12 q72 ∷
   rw 13 q70 ∷
   re 11 3 (ℓ "乑") ∷
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
  q84 = wE 1674 W
  q85 : Eqn
  q85 = sE 2541 lem-pass-X3-CKd32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q86 : Eqn
  q86 = wE 1675 W

-- pass [CKd32] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乘丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乘") ⟫ʷ
lem-pass-CKd32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乘丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乘")
  (rw 0 q84 ∷
   rw 1 q85 ∷
   rw 9 q86 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q88 : Eqn
  q88 = sE 2518 lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩
  q89 : Eqn
  q89 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [CCZ123] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乜丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乜丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乜")
  (rw 1 q87 ∷
   rw 0 q88 ∷
   rw⁻ 0 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 1409 W
  q91 : Eqn
  q91 = sE 2540 lem-pass-X3-CK32-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q92 : Eqn
  q92 = wE 1410 W

-- pass [CK32] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "乗丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞乗") ⟫ʷ
lem-pass-CK32-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "乗丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞乗")
  (rw 0 q90 ∷
   rw 1 q91 ∷
   rw 9 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 1459 W
  q94 : Eqn
  q94 = sE 2539 lem-pass-X2-CKd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3
  q95 : Eqn
  q95 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q96 : Eqn
  q96 = wE 1846 W
  q97 : Eqn
  q97 = wE 1460 W
  q98 : Eqn
  q98 = wE 1461 W

-- CA CK20 Gad(t=0, W=(3,), d=Kd, e=-1): 7 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ : ⟪ (ℓ "乄丞下中九丮九上丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞乄") ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ = derive (ℓ "乄丞下中九丮九上丞") (ℓ "丞中九丮九丞乄")
  (rw 0 q93 ∷
   rw 1 q94 ∷
   rw 0 q95 ∷
   rw 1 q96 ∷
   rw 5 q97 ∷
   rw 5 q95 ∷
   rw 6 q98 ∷ []) Eq.refl
