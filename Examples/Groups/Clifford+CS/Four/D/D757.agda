{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D757 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D432 W using (lem-HD-units)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D615 W using (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D644 W using (lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D724 W using (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ ; lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ ; lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ ; lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D725 W using (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D741 W using (lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 ; lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D742 W using (lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩ ; lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D743 W using (lem-PP-flip-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D747 W using (lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D749 W using (lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 ; lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 ; lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 ; lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0 ; lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 ; lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 ; lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0 ; lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 ; lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0 ; lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 ; lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0)
open import Examples.Groups.Clifford+CS.Four.D.D750 W using (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩ ; lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩ ; lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ ; lem-PP2≡E-at1023 ; lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0)

private
  q1 : Eqn
  q1 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q2 : Eqn
  q2 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q3 : Eqn
  q3 = eqn (X0 ∷ S1⁻ ∷ []) (S1⁻ ∷ X0 ∷ []) (low₁-comm (X) ((S • S • S)))
  q4 : Eqn
  q4 = eqn (K1⁻ ∷ X3 ∷ []) (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑)))
  q5 : Eqn
  q5 = eqn (K1⁻ ∷ X2 ∷ []) (X2 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (X))
  q6 : Eqn
  q6 = eqn (X0 ∷ K1⁻ ∷ []) (K1⁻ ∷ X0 ∷ []) (low₁-comm (X) ((K • iI)))
  q7 : Eqn
  q7 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q8 : Eqn
  q8 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q9 : Eqn
  q9 = eqn (X0 ∷ S1 ∷ []) (S1 ∷ X0 ∷ []) (low₁-comm (X) (S))
  q10 : Eqn
  q10 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (low₁-comm (X) (K))
  q11 : Eqn
  q11 = eqn (K1 ∷ X2 ∷ []) (X2 ∷ K1 ∷ []) (low-comm ((K ↑)) (X))
  q12 : Eqn
  q12 = eqn (K1 ∷ X3 ∷ []) (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑)))
  q13 : Eqn
  q13 = eqn (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ []) (wn 2509 W)
  q14 : Eqn
  q14 = eqn (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2510 W)
  q15 : Eqn
  q15 = eqn (CS13 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3)
  q16 : Eqn
  q16 = eqn (CK31⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ []) (lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3)
  q17 : Eqn
  q17 = eqn (CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3)
  q18 : Eqn
  q18 = eqn (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) [] (wn 2511 W)

-- ca-split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1) 3: 31 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw⁻ 2 q1 ∷
   rw⁻ 1 q2 ∷
   rw 0 q3 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 2 q5 ∷
   rw 1 q6 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 3 q8 ∷
   rw 2 q9 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 4 q8 ∷
   rw 3 q9 ∷
   rw⁻ 14 q9 ∷
   rw⁻ 13 q10 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   rw 15 q8 ∷
   rw 14 q11 ∷
   rw 13 q2 ∷
   rw 12 q2 ∷
   rw 16 q7 ∷
   rw 15 q12 ∷
   rw 14 q1 ∷
   rw 13 q1 ∷
   rw 0 q13 ∷
   rw 26 q14 ∷
   rw 15 q15 ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   rw 22 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (Toff123 ∷ []) (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) (wn 2502 W)
  q20 : Eqn
  q20 = eqn (CK31⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK31⁻ ∷ []) (lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3)
  q21 : Eqn
  q21 = eqn (CCZ123 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3)
  q22 : Eqn
  q22 = eqn (CK31 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3)
  q23 : Eqn
  q23 = eqn (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) (Toff123 ∷ []) (wn 2503 W)

-- pass [TOFF123] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 5 steps
lem-pass-TOFF123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (Toff123 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (Toff123 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Toff123 ∷ [])
  (rw 0 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 14 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (CK10 ∷ []) (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (wn 2430 W)
  q25 : Eqn
  q25 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3)
  q26 : Eqn
  q26 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q27 : Eqn
  q27 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q28 : Eqn
  q28 = eqn (K0 ∷ []) (K0 ∷ []) (wn 1460 W)
  q29 : Eqn
  q29 = eqn (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (CK10 ∷ []) (wn 2431 W)

-- CA CK10 Gad(t=0, W=(3,), d=Kd, e=-1): 7 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ : ⟪ (CK10 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ = derive (CK10 ∷ X3 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK10 ∷ [])
  (rw 0 q24 ∷
   rw 1 q25 ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 5 q28 ∷
   rw 5 q26 ∷
   rw 6 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2)
  q31 : Eqn
  q31 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))

-- CA CK10 Gad(t=0, W=(2,), d=Kd, e=-1): 7 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ : ⟪ (CK10 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ = derive (CK10 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK10 ∷ [])
  (rw 0 q24 ∷
   rw 1 q30 ∷
   rw 0 q31 ∷
   rw 1 q27 ∷
   rw 5 q28 ∷
   rw 5 q31 ∷
   rw 6 q29 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q33 : Eqn
  q33 = eqn (CK21 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1476 W)
  q34 : Eqn
  q34 = eqn (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ []) (X0 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0)
  q35 : Eqn
  q35 = eqn (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ []) (wn 1477 W)

-- pass [CK21] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 5 steps
lem-pass-CK21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (CK21 ∷ X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (CK21 ∷ X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ CK21 ∷ [])
  (rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 15 q35 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS01⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1817 W)
  q37 : Eqn
  q37 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0)
  q38 : Eqn
  q38 = eqn (S0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ []) (wn 2512 W)
  q39 : Eqn
  q39 = eqn (S0 ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ []) (wn 2513 W)
  q40 : Eqn
  q40 = eqn (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01⁻ ∷ []) (wn 1818 W)

-- CA CSd10 Gad(t=0, W=(), d=SKdSd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩ = derive (CS01⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ CS01⁻ ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   rw 6 q39 ∷
   rw 8 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0)
  q42 : Eqn
  q42 = eqn (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (wn 2514 W)
  q43 : Eqn
  q43 = eqn (K0 ∷ K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) (wn 2515 W)

-- CA CSd10 Gad(t=0, W=(), d=KdKdKd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩ : ⟪ (CS01⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩ = derive (CS01⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ CS01⁻ ∷ [])
  (rw 0 q36 ∷
   rw 1 q41 ∷
   rw 0 q42 ∷
   rw 8 q43 ∷
   rw 12 q40 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0)
  q45 : Eqn
  q45 = eqn (K0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ []) (wn 2516 W)
  q46 : Eqn
  q46 = eqn (K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (wn 2517 W)

-- CA CK10 Gad(t=0, W=(), d=SdKdKdKd, e=-1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩ : ⟪ (CK10 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩ = derive (CK10 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ [])
  (rw 0 q24 ∷
   rw 1 q44 ∷
   rw 0 q45 ∷
   rw 7 q46 ∷
   rw 10 q29 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0)
  q48 : Eqn
  q48 = eqn (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2518 W)
  q49 : Eqn
  q49 = eqn (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 2519 W)

-- CA CSd10 Gad(t=0, W=(), d=SdKdSSKd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ : ⟪ (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ = derive (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q36 ∷
   rw 1 q47 ∷
   rw 0 q48 ∷
   rw 10 q49 ∷
   rw 16 q40 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (CK10⁻ ∷ []) (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2311 W)
  q51 : Eqn
  q51 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0)
  q52 : Eqn
  q52 = eqn (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) (wn 2520 W)
  q53 : Eqn
  q53 = eqn (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (wn 2521 W)
  q54 : Eqn
  q54 = eqn (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (CK10⁻ ∷ []) (wn 2312 W)

-- CA CKd10 Gad(t=0, W=(), d=SSKdSSKd, e=-1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ : ⟪ (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ = derive (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK10⁻ ∷ [])
  (rw 0 q50 ∷
   rw 1 q51 ∷
   rw 0 q52 ∷
   rw 9 q53 ∷
   rw 14 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0)
  q56 : Eqn
  q56 = eqn (S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (wn 2522 W)
  q57 : Eqn
  q57 = eqn (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2523 W)

-- CA CSd10 Gad(t=0, W=(), d=SKSdKK, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ = derive (CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q36 ∷
   rw 1 q55 ∷
   rw 0 q56 ∷
   rw 8 q57 ∷
   rw 12 q40 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0)
  q59 : Eqn
  q59 = eqn (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 2524 W)
  q60 : Eqn
  q60 = eqn (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (wn 2525 W)

-- CA CK10 Gad(t=0, W=(), d=KSdKK, e=-1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ : ⟪ (CK10 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ = derive (CK10 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK10 ∷ [])
  (rw 0 q24 ∷
   rw 1 q58 ∷
   rw 0 q59 ∷
   rw 9 q60 ∷
   rw 14 q29 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (wn 2526 W)
  q62 : Eqn
  q62 = eqn (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (wn 2527 W)
  q63 : Eqn
  q63 = eqn (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (X0 ∷ ι ∷ ι ∷ []) (wn 2528 W)
  q64 : Eqn
  q64 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q65 : Eqn
  q65 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q66 : Eqn
  q66 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q67 : Eqn
  q67 = eqn (ι ∷ CS02 ∷ []) (CS02 ∷ ι ∷ []) (wn 1739 W)
  q68 : Eqn
  q68 = eqn (ι ∷ Toff012 ∷ []) (Toff012 ∷ ι ∷ []) (wn 1738 W)
  q69 : Eqn
  q69 = eqn (ι ∷ CS02⁻ ∷ []) (CS02⁻ ∷ ι ∷ []) (wn 1740 W)
  q70 : Eqn
  q70 = eqn (ι ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ []) (wn 2529 W)
  q71 : Eqn
  q71 = eqn (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1)

-- spell Gad(t=0, W=(), d=SKdSSKdS, e=-1) -> Gad(t=0, W=(), d=1, e=1): 45 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q61 ∷
   rw 10 q62 ∷
   rw 0 q63 ∷
   rw 4 q64 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q65 ∷
   rw 2 q66 ∷
   rw 3 q67 ∷
   rw 4 q64 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q66 ∷
   rw 4 q65 ∷
   rw 3 q68 ∷
   rw 6 q64 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q65 ∷
   rw 4 q66 ∷
   rw 5 q69 ∷
   rw 6 q64 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw⁻ 5 q66 ∷
   rw 6 q65 ∷
   rw 5 q68 ∷
   rw 3 q64 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q65 ∷
   rw 1 q66 ∷
   rw 2 q67 ∷
   rw 3 q64 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 2 q66 ∷
   rw 3 q65 ∷
   rw 2 q68 ∷
   rw 5 q64 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q65 ∷
   rw 3 q66 ∷
   rw 4 q69 ∷
   rw 5 q64 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw⁻ 4 q66 ∷
   rw 5 q65 ∷
   rw 4 q68 ∷
   rw 5 q70 ∷
   rw 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ []) (lem-HD-units)
  q73 : Eqn
  q73 = eqn (CK30⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CK30⁻ ∷ []) (lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩)
  q74 : Eqn
  q74 = eqn (CS01⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩)
  q75 : Eqn
  q75 = eqn (CK10⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ CK10⁻ ∷ []) (lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩)
  q76 : Eqn
  q76 = eqn (CS01 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩)
  q77 : Eqn
  q77 = eqn (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK20⁻ ∷ []) (lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩)
  q78 : Eqn
  q78 = eqn (CS01⁻ ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩)
  q79 : Eqn
  q79 = eqn (CK10 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ []) (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩)
  q80 : Eqn
  q80 = eqn (CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩)
  q81 : Eqn
  q81 = eqn (CK20 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ []) (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩)
  q82 : Eqn
  q82 = eqn (CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK30 ∷ []) (lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩)
  q83 : Eqn
  q83 = eqn (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ []) (lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩)
  q84 : Eqn
  q84 = eqn (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩)
  q85 : Eqn
  q85 = eqn (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CK10⁻ ∷ []) (lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩)
  q86 : Eqn
  q86 = eqn (CS01 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩)
  q87 : Eqn
  q87 = eqn (CK20 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK20 ∷ []) (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩)
  q88 : Eqn
  q88 = eqn (CS01⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩)
  q89 : Eqn
  q89 = eqn (CK10 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ CK10 ∷ []) (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩)
  q90 : Eqn
  q90 = eqn (CS01 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩)
  q91 : Eqn
  q91 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ []) lem-HD-units

-- HD conj Gad(t=0, W=(), d=KSSKd, e=1): 20 steps
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  (rw 0 q72 ∷
   rw 17 q73 ∷
   rw 16 q74 ∷
   rw 15 q75 ∷
   rw 14 q76 ∷
   rw 13 q77 ∷
   rw 12 q78 ∷
   rw 11 q79 ∷
   rw 10 q80 ∷
   rw 9 q81 ∷
   rw 8 q82 ∷
   rw 7 q83 ∷
   rw 6 q84 ∷
   rw 5 q85 ∷
   rw 4 q86 ∷
   rw 3 q87 ∷
   rw 2 q88 ∷
   rw 1 q89 ∷
   rw 0 q90 ∷
   rw⁻ 12 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (wn 2530 W)
  q93 : Eqn
  q93 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) (wn 2531 W)
  q94 : Eqn
  q94 = eqn (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (X0 ∷ S0 ∷ ι ∷ []) (wn 2532 W)
  q95 : Eqn
  q95 = eqn (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012)
  q96 : Eqn
  q96 = eqn (S0 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (X0 ∷ []) (wn 2533 W)

-- spell Gad(t=0, W=(), d=SdKdSS, e=-1) -> Gad(t=0, W=(), d=SKdSd, e=1): 26 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ = derive (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ [])
  (rw 0 q92 ∷
   rw 12 q93 ∷
   rw 3 q94 ∷
   rw 7 q64 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q65 ∷
   rw 5 q66 ∷
   rw 6 q67 ∷
   rw 7 q64 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q66 ∷
   rw 7 q65 ∷
   rw 6 q68 ∷
   rw 9 q64 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q65 ∷
   rw 7 q66 ∷
   rw 8 q69 ∷
   rw 9 q64 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q66 ∷
   rw 9 q65 ∷
   rw 8 q68 ∷
   rw 4 q95 ∷
   rw 8 q96 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (X0 ∷ X1 ∷ X0 ∷ X1 ∷ []) [] (wn 2534 W)
  q98 : Eqn
  q98 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (CCZ023 ∷ []) (lem-PP2≡E-at1023)
  q99 : Eqn
  q99 = eqn (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) (wn 217 W)
  q100 : Eqn
  q100 = eqn (X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ))
  q101 : Eqn
  q101 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q102 : Eqn
  q102 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q103 : Eqn
  q103 = eqn (X1 ∷ X1 ∷ []) [] (wn 388 W)
  q104 : Eqn
  q104 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)

-- top z form: 10 steps
lem-top-z-form : ⟪ (X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ023 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ
lem-top-z-form = derive (X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CCZ023 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ [])
  (rw 6 q97 ∷
   rw 2 q98 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   rw 1 q99 ∷
   rw 2 q100 ∷
   rw 3 q101 ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw⁻ 2 q102 ∷
   rw 3 q103 ∷
   rw 2 q104 ∷ []) Eq.refl
