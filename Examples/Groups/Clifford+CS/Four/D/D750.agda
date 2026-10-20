{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D750 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D542 W using (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D544 W using (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D592 W using (lem-CA-CKd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ ; lem-pass-CS10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
open import Examples.Groups.Clifford+CS.Four.D.D616 W using (lem-CA-CK30-Gad⟨t≡0-W≡⟨1⟩-d≡Kd-e≡1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D726 W using (lem-PP2≡E)
open import Examples.Groups.Clifford+CS.Four.D.D734 W using (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D742 W using (lem-pass-CSd10-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 ; lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-Sd0-Sd0 ; lem-pass-X1-CKd10-X1-vs-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0 ; lem-pass-X1-CKd10-X1-vs-S0-S0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-Sd0-Sd0 ; lem-pass-X1-CKd10-X1-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0 ; lem-pass-X1-CS10-X1-vs-S0-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0-Sd0 ; lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0 ; lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0)

private
  q1 : Eqn
  q1 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2459 W)
  q2 : Eqn
  q2 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q3 : Eqn
  q3 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q4 : Eqn
  q4 = eqn (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q5 : Eqn
  q5 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2460 W)

-- pass [X1 CKd10 X1] [K0 Sd0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 S0 Kd0]: 5 steps
lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q1 ∷
   rw 10 q2 ∷
   rw 7 q3 ∷
   rw 4 q4 ∷
   rw 8 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn (CS01⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1817 W)
  q7 : Eqn
  q7 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0)
  q8 : Eqn
  q8 = eqn (S0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ []) (wn 2461 W)
  q9 : Eqn
  q9 = eqn (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 2462 W)
  q10 : Eqn
  q10 = eqn (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01⁻ ∷ []) (wn 1818 W)

-- CA CSd10 Gad(t=0, W=(), d=SSKd, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ = derive (CS01⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q6 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 6 q9 ∷
   rw 8 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (CK10 ∷ []) (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2430 W)
  q12 : Eqn
  q12 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-S0-S0-K0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Kd0-Sd0-Sd0)
  q13 : Eqn
  q13 = eqn (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2463 W)
  q14 : Eqn
  q14 = eqn (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (wn 2464 W)
  q15 : Eqn
  q15 = eqn (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (CK10 ∷ []) (wn 2431 W)

-- CA CK10 Gad(t=0, W=(), d=SSKKKK, e=1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩ : ⟪ (CK10 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩ = derive (CK10 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ [])
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   rw 9 q14 ∷
   rw 14 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0)
  q17 : Eqn
  q17 = eqn (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (wn 2465 W)
  q18 : Eqn
  q18 = eqn (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 2466 W)

-- CA CSd10 Gad(t=0, W=(), d=SdKdSKdKd, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ : ⟪ (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ = derive (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q6 ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw 10 q18 ∷
   rw 16 q10 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (CK10⁻ ∷ []) (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2311 W)
  q20 : Eqn
  q20 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-Sd0-Sd0)
  q21 : Eqn
  q21 = eqn (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (wn 2467 W)
  q22 : Eqn
  q22 = eqn (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (wn 2468 W)
  q23 : Eqn
  q23 = eqn (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (CK10⁻ ∷ []) (wn 2312 W)

-- CA CKd10 Gad(t=0, W=(), d=SSKdSKdKd, e=1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩ : ⟪ (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩ = derive (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CK10⁻ ∷ [])
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   rw 9 q22 ∷
   rw 14 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0-Sd0)
  q25 : Eqn
  q25 = eqn (S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 2469 W)
  q26 : Eqn
  q26 = eqn (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 2470 W)

-- CA CSd10 Gad(t=0, W=(), d=SSKKK, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩ = derive (CS01⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q6 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 8 q26 ∷
   rw 12 q10 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-S0-K0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-Kd0-Sd0)
  q28 : Eqn
  q28 = eqn (K0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (wn 2471 W)
  q29 : Eqn
  q29 = eqn (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (wn 2472 W)

-- CA CK10 Gad(t=0, W=(), d=SKKK, e=1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩ : ⟪ (CK10 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩ = derive (CK10 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ CK10 ∷ [])
  (rw 0 q11 ∷
   rw 1 q27 ∷
   rw 0 q28 ∷
   rw 9 q29 ∷
   rw 14 q15 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q32 : Eqn
  q32 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q33 : Eqn
  q33 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q34 : Eqn
  q34 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q35 : Eqn
  q35 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q36 : Eqn
  q36 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q37 : Eqn
  q37 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q38 : Eqn
  q38 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q39 : Eqn
  q39 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CCZ123 ∷ []) (lem-PP2≡E)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q45 : Eqn
  q45 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q46 : Eqn
  q46 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- PP2=E @1023: 90 steps
lem-PP2≡E-at1023 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-PP2≡E-at1023 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (CCZ023 ∷ [])
  (rw 8 q30 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q31 ∷
   rw 8 q32 ∷
   rw⁻ 7 q31 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q33 ∷
   rw 12 q34 ∷
   rw 11 q35 ∷
   rw 10 q36 ∷
   rw 9 q32 ∷
   rw 8 q36 ∷
   rw 7 q37 ∷
   rw 6 q34 ∷
   rw 7 q38 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q31 ∷
   rw 6 q37 ∷
   rw⁻ 5 q31 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q33 ∷
   rw 10 q34 ∷
   rw 9 q35 ∷
   rw 8 q36 ∷
   rw 7 q32 ∷
   rw 6 q36 ∷
   rw 5 q37 ∷
   rw 4 q34 ∷
   rw 5 q38 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q31 ∷
   rw 4 q32 ∷
   rw⁻ 3 q31 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q33 ∷
   rw 8 q34 ∷
   rw 7 q35 ∷
   rw 6 q36 ∷
   rw 5 q32 ∷
   rw 4 q36 ∷
   rw 3 q37 ∷
   rw 2 q34 ∷
   rw 3 q38 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q31 ∷
   rw 2 q37 ∷
   rw⁻ 1 q31 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q35 ∷
   rw 4 q36 ∷
   rw 3 q32 ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 0 q34 ∷
   rw 1 q38 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q39 ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 3 q41 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q31 ∷
   rw 5 q43 ∷
   rw 6 q31 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q30 ∷
   rw 1 q40 ∷
   rw 2 q44 ∷
   rw 3 q42 ∷
   rw 4 q44 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q31 ∷
   rw 6 q45 ∷
   rw 7 q31 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q46 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (CK10⁻ ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2415 W)
  q49 : Eqn
  q49 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-Sd0-TOFF012-CS03-TOFF012-CSd03-S0)
  q50 : Eqn
  q50 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ []) (wn 2416 W)

-- pass [CKd10] [X1 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X1]: 3 steps
lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : ⟪ (CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = derive (CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ [])
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 7 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q52 : Eqn
  q52 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q53 : Eqn
  q53 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q54 : Eqn
  q54 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q55 : Eqn
  q55 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q56 : Eqn
  q56 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (CS01 ∷ CK20 ∷ CS01⁻ ∷ CK20⁻ ∷ []) (wn 1935 W)
  q57 : Eqn
  q57 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q58 : Eqn
  q58 = eqn (CK30⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CK30⁻ ∷ []) (lem-CA-CKd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩)
  q59 : Eqn
  q59 = eqn (CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ []) (lem-pass-CSd10-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1)
  q60 : Eqn
  q60 = eqn (CK30 ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK30 ∷ []) (lem-CA-CK30-Gad⟨t≡0-W≡⟨1⟩-d≡Kd-e≡1⟩)
  q61 : Eqn
  q61 = eqn (CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ []) (lem-pass-CS10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
  q62 : Eqn
  q62 = eqn (CS01 ∷ CK20 ∷ CS01⁻ ∷ CK20⁻ ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (wn 1936 W)
  q63 : Eqn
  q63 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 132 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 31 q51 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q52 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q52 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q52 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q52 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q52 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q52 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q52 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q52 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q52 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q52 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q52 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q52 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q52 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q52 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q52 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q52 ∷
   rw 14 q53 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q52 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q52 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q52 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q52 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q52 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q52 ∷
   rw 5 q54 ∷
   rw 4 q54 ∷
   rw 3 q55 ∷
   rw 2 q54 ∷
   rw 1 q54 ∷
   rw 0 q54 ∷
   rw 1 q56 ∷
   rw⁻ 0 q54 ∷
   rw 3 q51 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw⁻ 2 q57 ∷
   rw 5 q51 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q52 ∷
   rw 3 q58 ∷
   rw 2 q59 ∷
   rw 1 q60 ∷
   rw 0 q61 ∷
   rw 10 q51 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   rw 8 q57 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q54 ∷
   rw 7 q62 ∷
   rw⁻ 6 q54 ∷
   rw⁻ 7 q54 ∷
   rw⁻ 8 q54 ∷
   rw⁻ 9 q55 ∷
   rw⁻ 10 q54 ∷
   rw⁻ 11 q54 ∷
   rw 14 q51 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 15 q51 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q51 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q51 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q51 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q51 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q51 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q51 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 20 q63 ∷
   rw 23 q51 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q51 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q51 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q51 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q51 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q51 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q51 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q51 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q51 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q51 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 33 q51 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q51 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q51 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q51 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 37 q51 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q51 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q52 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS23⁻ ∷ []) (wn 1882 W)
  q65 : Eqn
  q65 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q66 : Eqn
  q66 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q67 : Eqn
  q67 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q68 : Eqn
  q68 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q69 : Eqn
  q69 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q70 : Eqn
  q70 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wn 1883 W)
  q71 : Eqn
  q71 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q72 : Eqn
  q72 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q73 : Eqn
  q73 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q74 : Eqn
  q74 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q75 : Eqn
  q75 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q76 : Eqn
  q76 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q77 : Eqn
  q77 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q78 : Eqn
  q78 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q79 : Eqn
  q79 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q80 : Eqn
  q80 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q81 : Eqn
  q81 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q82 : Eqn
  q82 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q83 : Eqn
  q83 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q84 : Eqn
  q84 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)

-- PP2=E @3012: 322 steps
lem-PP2≡E-at3012 : ⟪ (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-PP2≡E-at3012 = derive (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) (CCZ012 ∷ [])
  (rw 8 q51 ∷
   rw 7 q64 ∷
   re 6 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 6 q65 ∷
   rw 9 q51 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q66 ∷
   rw 11 q51 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q66 ∷
   rw 13 q51 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q65 ∷
   rw⁻ 13 q67 ∷
   rw 14 q52 ∷
   rw 13 q67 ∷
   rw 12 q68 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q52 ∷
   rw 10 q66 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   rw 8 q66 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q68 ∷
   rw 7 q69 ∷
   re 7 8 (Toff201 ∷ []) ∷
   rw 5 q70 ∷
   re 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 4 q65 ∷
   rw 7 q51 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q66 ∷
   rw 9 q51 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q66 ∷
   rw 11 q51 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q65 ∷
   rw⁻ 11 q67 ∷
   rw 12 q52 ∷
   rw 11 q67 ∷
   rw 10 q68 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q52 ∷
   rw 8 q66 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q66 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q52 ∷
   rw 4 q68 ∷
   rw 5 q69 ∷
   re 5 8 (Toff201 ∷ []) ∷
   rw 3 q64 ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 2 q65 ∷
   rw 5 q51 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q66 ∷
   rw 7 q51 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q66 ∷
   rw 9 q51 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q65 ∷
   rw⁻ 9 q67 ∷
   rw 10 q52 ∷
   rw 9 q67 ∷
   rw 8 q68 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q52 ∷
   rw 6 q66 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q52 ∷
   rw 4 q66 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q52 ∷
   rw 2 q68 ∷
   rw 3 q69 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw 1 q70 ∷
   re 0 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q65 ∷
   rw 3 q51 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q66 ∷
   rw 5 q51 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q66 ∷
   rw 7 q51 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q65 ∷
   rw⁻ 7 q67 ∷
   rw 8 q52 ∷
   rw 7 q67 ∷
   rw 6 q68 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q52 ∷
   rw 4 q66 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q52 ∷
   rw 2 q66 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q52 ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   re 1 8 (Toff201 ∷ []) ∷
   rw 9 q71 ∷
   rw 8 q72 ∷
   re 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 14 q73 ∷
   rw 13 q74 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q75 ∷
   rw 11 q71 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q76 ∷
   rw 9 q71 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q77 ∷
   rw 7 q74 ∷
   rw 8 q78 ∷
   re 8 8 (Toff102 ∷ []) ∷
   rw 6 q79 ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q73 ∷
   rw 11 q74 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q75 ∷
   rw 9 q71 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q76 ∷
   rw 7 q71 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q77 ∷
   rw 5 q74 ∷
   rw 6 q78 ∷
   re 6 8 (Toff102 ∷ []) ∷
   rw 4 q72 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q73 ∷
   rw 9 q74 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q75 ∷
   rw 7 q71 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q76 ∷
   rw 5 q71 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q77 ∷
   rw 3 q74 ∷
   rw 4 q78 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q79 ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 8 q73 ∷
   rw 7 q74 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q75 ∷
   rw 5 q71 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q76 ∷
   rw 3 q71 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q77 ∷
   rw 1 q74 ∷
   rw 2 q78 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 10 q30 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q31 ∷
   rw 10 q32 ∷
   rw⁻ 9 q31 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q33 ∷
   rw 14 q34 ∷
   rw 13 q35 ∷
   rw 12 q36 ∷
   rw 11 q32 ∷
   rw 10 q36 ∷
   rw 9 q37 ∷
   rw 8 q34 ∷
   rw 9 q38 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q31 ∷
   rw 8 q37 ∷
   rw⁻ 7 q31 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q33 ∷
   rw 12 q34 ∷
   rw 11 q35 ∷
   rw 10 q36 ∷
   rw 9 q32 ∷
   rw 8 q36 ∷
   rw 7 q37 ∷
   rw 6 q34 ∷
   rw 7 q38 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q31 ∷
   rw 6 q32 ∷
   rw⁻ 5 q31 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q33 ∷
   rw 10 q34 ∷
   rw 9 q35 ∷
   rw 8 q36 ∷
   rw 7 q32 ∷
   rw 6 q36 ∷
   rw 5 q37 ∷
   rw 4 q34 ∷
   rw 5 q38 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q31 ∷
   rw 4 q37 ∷
   rw⁻ 3 q31 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q33 ∷
   rw 8 q34 ∷
   rw 7 q35 ∷
   rw 6 q36 ∷
   rw 5 q32 ∷
   rw 4 q36 ∷
   rw 3 q37 ∷
   rw 2 q34 ∷
   rw 3 q38 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 3 q39 ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q40 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 5 q41 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q31 ∷
   rw 7 q43 ∷
   rw 8 q31 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q40 ∷
   rw 4 q44 ∷
   rw 5 q42 ∷
   rw 6 q44 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q31 ∷
   rw 8 q45 ∷
   rw 9 q31 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q46 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   rw 3 q47 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q40 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 5 q41 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q31 ∷
   rw 7 q43 ∷
   rw 8 q31 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q47 ∷
   rw 1 q80 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 q75 ∷
   rw 3 q81 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q75 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q82 ∷
   rw⁻ 7 q54 ∷
   rw 8 q83 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 1 q51 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q52 ∷
   rw⁻ 3 q66 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q52 ∷
   rw⁻ 5 q66 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q52 ∷
   rw 2 q84 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q75 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q51 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q66 ∷
   rw 5 q51 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q66 ∷
   rw 7 q51 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q52 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q52 ∷
   rw⁻ 1 q66 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q52 ∷
   rw⁻ 3 q66 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q52 ∷
   rw 0 q84 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   rw 1 q52 ∷ []) Eq.refl
