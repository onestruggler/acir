{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD742 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D742 (W : Ws) (Sᴰ : SD742) where

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
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2278
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 : St 2438
  lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 = pickᴰ 4 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 : St 2439
  lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 = pickᴰ 5 Sᴰ
  lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 : St 2440
  lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 = pickᴰ 6 Sᴰ
  lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 : St 2441
  lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 = pickᴰ 7 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : St 2442
  lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = pickᴰ 8 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 : St 2443
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 = pickᴰ 9 Sᴰ
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 : St 2444
  lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 = pickᴰ 10 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 : St 2445
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = eqn (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1459 W)
  q2 : Eqn
  q2 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0)
  q3 : Eqn
  q3 = eqn (K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (wn 2374 W)
  q4 : Eqn
  q4 = eqn (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (wn 2375 W)
  q5 : Eqn
  q5 = eqn (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) (wn 1461 W)

-- CA CK20 Gad(t=0, W=(), d=SdKSS, e=-1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩ : ⟪ (CK20 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩ = derive (CK20 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 0 q3 ∷
   rw 9 q4 ∷
   rw 14 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2376 W)
  q7 : Eqn
  q7 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q8 : Eqn
  q8 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q9 : Eqn
  q9 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2377 W)

-- pass [X1 CS10 X1] [S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0 = derive (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q6 ∷
   rw 9 q7 ∷
   rw 6 q8 ∷
   rw 3 q7 ∷
   rw 7 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CK10⁻ ∷ []) (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2311 W)
  q11 : Eqn
  q11 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0)
  q12 : Eqn
  q12 = eqn (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (wn 2378 W)
  q13 : Eqn
  q13 = eqn (K0 ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (wn 2379 W)
  q14 : Eqn
  q14 = eqn (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (CK10⁻ ∷ []) (wn 2312 W)

-- CA CKd10 Gad(t=0, W=(), d=SKd, e=1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩ : ⟪ (CK10⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩ = derive (CK10⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ CK10⁻ ∷ [])
  (rw 0 q10 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   rw 7 q13 ∷
   rw 10 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CS01 ∷ []) (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1819 W)
  q16 : Eqn
  q16 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0)
  q17 : Eqn
  q17 = eqn (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (wn 2380 W)
  q18 : Eqn
  q18 = eqn (K0 ∷ S0⁻ ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0 ∷ []) (wn 2381 W)
  q19 : Eqn
  q19 = eqn (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS01 ∷ []) (wn 1820 W)

-- CA CS10 Gad(t=0, W=(), d=KdSKd, e=1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩ : ⟪ (CS01 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩ = derive (CS01 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CS01 ∷ [])
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw 8 q18 ∷
   rw 12 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2382 W)
  q21 : Eqn
  q21 = eqn (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q22 : Eqn
  q22 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2383 W)

-- pass [X1 CKd10 X1] [S0 S0 K0 K0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 Kd0 Kd0 Sd0 Sd0]: 7 steps
lem-pass-X1-CKd10-X1-vs-S0-S0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-Sd0-Sd0 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-S0-S0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-Sd0-Sd0 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q20 ∷
   rw 18 q21 ∷
   rw 15 q21 ∷
   rw 12 q8 ∷
   rw 9 q21 ∷
   rw 6 q21 ∷
   rw 10 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0)
  q24 : Eqn
  q24 = eqn (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2384 W)
  q25 : Eqn
  q25 = eqn (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) (wn 2385 W)

-- CA CS10 Gad(t=0, W=(), d=SKdSKdSd, e=1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩ : ⟪ (CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩ = derive (CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ [])
  (rw 0 q15 ∷
   rw 1 q23 ∷
   rw 0 q24 ∷
   rw 10 q25 ∷
   rw 16 q19 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CK20⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1709 W)
  q27 : Eqn
  q27 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0)
  q28 : Eqn
  q28 = eqn (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (wn 2386 W)
  q29 : Eqn
  q29 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2387 W)
  q30 : Eqn
  q30 = eqn (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (CK20⁻ ∷ []) (wn 1711 W)

-- CA CKd20 Gad(t=0, W=(), d=SKdSS, e=1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩ : ⟪ (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩ = derive (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ [])
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷
   rw 9 q29 ∷
   rw 14 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2388 W)
  q32 : Eqn
  q32 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2389 W)

-- pass [X1 CS10 X1] [Sd0 Kd0 S0 Kd0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 K0 Sd0 K0 S0]: 5 steps
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 = derive (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q31 ∷
   rw 11 q8 ∷
   rw 8 q21 ∷
   rw 5 q21 ∷
   rw 9 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2390 W)
  q34 : Eqn
  q34 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2391 W)

-- pass [X1 CK10 X1] [S0 S0 Kd0 S0 Kd0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 K0 Sd0 K0 Sd0 Sd0]: 7 steps
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-Sd0-Sd0 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-Sd0-Sd0 = derive (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw 0 q33 ∷
   rw 18 q8 ∷
   rw 15 q21 ∷
   rw 12 q8 ∷
   rw 9 q21 ∷
   rw 6 q21 ∷
   rw 10 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0)
  q36 : Eqn
  q36 = eqn (S0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (wn 2392 W)
  q37 : Eqn
  q37 = eqn (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (wn 2393 W)

-- CA CS10 Gad(t=0, W=(), d=SdKSSK, e=1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩ : ⟪ (CS01 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩ = derive (CS01 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ CS01 ∷ [])
  (rw 0 q15 ∷
   rw 1 q35 ∷
   rw 0 q36 ∷
   rw 8 q37 ∷
   rw 12 q19 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2394 W)
  q39 : Eqn
  q39 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2395 W)

-- pass [X1 CS10 X1] [S0 S0 K0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 Kd0 Sd0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0-Sd0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0-Sd0 = derive (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q38 ∷
   rw 11 q7 ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 9 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2396 W)
  q41 : Eqn
  q41 = eqn (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q42 : Eqn
  q42 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2397 W)

-- pass [X1 CKd10 X1] [S0 K0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 Kd0 Sd0]: 7 steps
lem-pass-X1-CKd10-X1-vs-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q40 ∷
   rw 16 q8 ∷
   rw 13 q21 ∷
   rw 10 q21 ∷
   rw 7 q41 ∷
   rw 4 q21 ∷
   rw 8 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0)
  q44 : Eqn
  q44 = eqn (S0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (wn 2398 W)
  q45 : Eqn
  q45 = eqn (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (wn 2399 W)

-- CA CS10 Gad(t=0, W=(), d=SdKSdKK, e=1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩ : ⟪ (CS01 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩ = derive (CS01 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01 ∷ [])
  (rw 0 q15 ∷
   rw 1 q43 ∷
   rw 0 q44 ∷
   rw 8 q45 ∷
   rw 12 q19 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2400 W)
  q47 : Eqn
  q47 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ []) (S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2401 W)

-- pass [X1 CKd10 X1] [Sd0 TOFF012 CS03 TOFF012 CSd03 S0]: 5 steps
lem-pass-X1-CKd10-X1-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q46 ∷
   rw 7 q7 ∷
   rw 4 q8 ∷
   rw 1 q21 ∷
   rw 5 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (CS01⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1821 W)
  q49 : Eqn
  q49 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0)
  q50 : Eqn
  q50 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ []) (wn 1822 W)

-- pass [CSd10] [X1 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X1]: 3 steps
lem-pass-CSd10-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 : ⟪ (CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 = derive (CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ [])
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 7 q50 ∷ []) Eq.refl
