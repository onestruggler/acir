{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD757 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D757 (W : Ws) (Sᴰ : SD757) where

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
  lem-HD-units : St 2829
  lem-HD-units = pickᴰ 0 Sᴰ
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1117
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 1 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ : St 2830
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩ = pickᴰ 2 Sᴰ
  lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2831
  lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 3 Sᴰ
  lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ : St 2832
  lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ = pickᴰ 4 Sᴰ
  lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ : St 2833
  lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ = pickᴰ 5 Sᴰ
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ : St 2834
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ = pickᴰ 6 Sᴰ
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : St 2835
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = pickᴰ 7 Sᴰ
  lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : St 2836
  lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = pickᴰ 8 Sᴰ
  lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2837
  lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 9 Sᴰ
  lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2838
  lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 10 Sᴰ
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩ : St 2839
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩ = pickᴰ 11 Sᴰ
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩ : St 2840
  lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩ = pickᴰ 12 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩ : St 2841
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩ = pickᴰ 13 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩ : St 2842
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩ = pickᴰ 14 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩ : St 2843
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩ = pickᴰ 15 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩ : St 2844
  lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩ = pickᴰ 16 Sᴰ
  lem-PP-flip-ᵖ-1 : St 2671
  lem-PP-flip-ᵖ-1 = pickᴰ 17 Sᴰ
  lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 2806
  lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2845
  lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 2846
  lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 20 Sᴰ
  lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 : St 2847
  lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 = pickᴰ 21 Sᴰ
  lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0 : St 2848
  lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0 = pickᴰ 22 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : St 2849
  lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = pickᴰ 23 Sᴰ
  lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : St 2850
  lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = pickᴰ 24 Sᴰ
  lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0 : St 2851
  lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0 = pickᴰ 25 Sᴰ
  lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 : St 2852
  lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 = pickᴰ 26 Sᴰ
  lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0 : St 2853
  lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0 = pickᴰ 27 Sᴰ
  lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : St 2854
  lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = pickᴰ 28 Sᴰ
  lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2855
  lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 29 Sᴰ
  lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩ : St 2856
  lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩ = pickᴰ 30 Sᴰ
  lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩ : St 2857
  lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩ = pickᴰ 31 Sᴰ
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩ : St 2858
  lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩ = pickᴰ 32 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩ : St 2859
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩ = pickᴰ 33 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ : St 2860
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ = pickᴰ 34 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ : St 2861
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ = pickᴰ 35 Sᴰ
  lem-PP2≡E-at1023 : St 2862
  lem-PP2≡E-at1023 = pickᴰ 36 Sᴰ
  lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 : St 2863
  lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 = pickᴰ 37 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q2 : Eqn
  q2 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q3 : Eqn
  q3 = eqn (ℓ "丌丏") (ℓ "丏丌") (low₁-comm (X) ((S • S • S)))
  q4 : Eqn
  q4 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "丑丘") (ℓ "丘丑") (low-comm (((K • iI) ↑)) (X))
  q6 : Eqn
  q6 = eqn (ℓ "丌丑") (ℓ "丑丌") (low₁-comm (X) ((K • iI)))
  q7 : Eqn
  q7 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "丌与") (ℓ "与丌") (low₁-comm (X) (S))
  q10 : Eqn
  q10 = eqn (ℓ "丌丐") (ℓ "丐丌") (low₁-comm (X) (K))
  q11 : Eqn
  q11 = eqn (ℓ "丐丘") (ℓ "丘丐") (low-comm ((K ↑)) (X))
  q12 : Eqn
  q12 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q13 : Eqn
  q13 = wE 2509 W
  q14 : Eqn
  q14 = wE 2510 W
  q15 : Eqn
  q15 = sE 2845 lem-pass-CS31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q16 : Eqn
  q16 = sE 2831 lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q17 : Eqn
  q17 = sE 2846 lem-pass-CSd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3
  q18 : Eqn
  q18 = wE 2511 W

-- ca-split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1) 3: 31 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丘丞丽习举习丌丘丞丞举丞丞举丞丞乔丞丞丽丞")
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
  q19 = wE 2502 W
  q20 : Eqn
  q20 = sE 2838 lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q21 : Eqn
  q21 = sE 2806 lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q22 : Eqn
  q22 = sE 2837 lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q23 : Eqn
  q23 = wE 2503 W

-- pass [TOFF123] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 5 steps
lem-pass-TOFF123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乢丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乢") ⟫ʷ
lem-pass-TOFF123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乢丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乢")
  (rw 0 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 14 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 2430 W
  q25 : Eqn
  q25 = sE 2850 lem-pass-X1-CKd10-X1-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3
  q26 : Eqn
  q26 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q27 : Eqn
  q27 = wE 1846 W
  q28 : Eqn
  q28 = wE 1460 W
  q29 : Eqn
  q29 = wE 2431 W

-- CA CK10 Gad(t=0, W=(3,), d=Kd, e=-1): 7 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ : ⟪ (ℓ "临丞下中九丮九上丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞临") ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡-1⟩ = derive (ℓ "临丞下中九丮九上丞") (ℓ "丞中九丮九丞临")
  (rw 0 q24 ∷
   rw 1 q25 ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 5 q28 ∷
   rw 5 q26 ∷
   rw 6 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 2849 lem-pass-X1-CKd10-X1-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2
  q31 : Eqn
  q31 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))

-- CA CK10 Gad(t=0, W=(2,), d=Kd, e=-1): 7 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ : ⟪ (ℓ "临丘下中九丮九上丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘临") ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ = derive (ℓ "临丘下中九丮九上丘") (ℓ "丘中九丮九丘临")
  (rw 0 q24 ∷
   rw 1 q30 ∷
   rw 0 q31 ∷
   rw 1 q27 ∷
   rw 5 q28 ∷
   rw 5 q31 ∷
   rw 6 q29 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q33 : Eqn
  q33 = wE 1476 W
  q34 : Eqn
  q34 = sE 2855 lem-pass-X2-CK21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0
  q35 : Eqn
  q35 = wE 1477 W

-- pass [CK21] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 5 steps
lem-pass-CK21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "乇丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乇") ⟫ʷ
lem-pass-CK21-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "乇丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘乇")
  (rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 15 q35 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1817 W
  q37 : Eqn
  q37 = sE 2853 lem-pass-X1-CS10-X1-vs-S0-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0-Sd0
  q38 : Eqn
  q38 = wE 2512 W
  q39 : Eqn
  q39 = wE 2513 W
  q40 : Eqn
  q40 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(), d=SKdSd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩ : ⟪ (ℓ "両丈下三中九丮九丈上三") ⟫ʷ ≈ ⟪ (ℓ "下三中九丮九丈上両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩ = derive (ℓ "両丈下三中九丮九丈上三") (ℓ "下三中九丮九丈上両")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   rw 6 q39 ∷
   rw 8 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 2851 lem-pass-X1-CS10-X1-vs-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0
  q42 : Eqn
  q42 = wE 2514 W
  q43 : Eqn
  q43 = wE 2515 W

-- CA CSd10 Gad(t=0, W=(), d=KdKdKd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩ : ⟪ (ℓ "両下下下中九丮九上上上") ⟫ʷ ≈ ⟪ (ℓ "三下下下中九丮九上上上丈両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩ = derive (ℓ "両下下下中九丮九上上上") (ℓ "三下下下中九丮九上上上丈両")
  (rw 0 q36 ∷
   rw 1 q41 ∷
   rw 0 q42 ∷
   rw 8 q43 ∷
   rw 12 q40 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 2848 lem-pass-X1-CKd10-X1-vs-Sd0-Kd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-K0-S0
  q45 : Eqn
  q45 = wE 2516 W
  q46 : Eqn
  q46 = wE 2517 W

-- CA CK10 Gad(t=0, W=(), d=SdKdKdKd, e=-1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩ : ⟪ (ℓ "临三下下下中九丮九上上上丈") ⟫ʷ ≈ ⟪ (ℓ "丈下丈中九丮九三上三临") ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩ = derive (ℓ "临三下下下中九丮九上上上丈") (ℓ "丈下丈中九丮九三上三临")
  (rw 0 q24 ∷
   rw 1 q44 ∷
   rw 0 q45 ∷
   rw 7 q46 ∷
   rw 10 q29 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = sE 2854 lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0
  q48 : Eqn
  q48 = wE 2518 W
  q49 : Eqn
  q49 = wE 2519 W

-- CA CSd10 Gad(t=0, W=(), d=SdKdSSKd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ : ⟪ (ℓ "両三下丈丈下中九丮九上三三上丈") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈丈下中九丮九上三三上三三両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ = derive (ℓ "両三下丈丈下中九丮九上三三上丈") (ℓ "丈丈下丈丈下中九丮九上三三上三三両")
  (rw 0 q36 ∷
   rw 1 q47 ∷
   rw 0 q48 ∷
   rw 10 q49 ∷
   rw 16 q40 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 2311 W
  q51 : Eqn
  q51 = sE 2847 lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0
  q52 : Eqn
  q52 = wE 2520 W
  q53 : Eqn
  q53 = wE 2521 W
  q54 : Eqn
  q54 = wE 2312 W

-- CA CKd10 Gad(t=0, W=(), d=SSKdSSKd, e=-1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ : ⟪ (ℓ "丵丈丈下丈丈下中九丮九上三三上三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈上丈丈中九丮九三三下三三丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ = derive (ℓ "丵丈丈下丈丈下中九丮九上三三上三三") (ℓ "丈丈上丈丈中九丮九三三下三三丵")
  (rw 0 q50 ∷
   rw 1 q51 ∷
   rw 0 q52 ∷
   rw 9 q53 ∷
   rw 14 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = sE 2852 lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0
  q56 : Eqn
  q56 = wE 2522 W
  q57 : Eqn
  q57 = wE 2523 W

-- CA CSd10 Gad(t=0, W=(), d=SKSdKK, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ : ⟪ (ℓ "両丈上三上上中九丮九下下丈下三") ⟫ʷ ≈ ⟪ (ℓ "上三上上中九丮九下下丈下両") ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ = derive (ℓ "両丈上三上上中九丮九下下丈下三") (ℓ "上三上上中九丮九下下丈下両")
  (rw 0 q36 ∷
   rw 1 q55 ∷
   rw 0 q56 ∷
   rw 8 q57 ∷
   rw 12 q40 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 2863 lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0
  q59 : Eqn
  q59 = wE 2524 W
  q60 : Eqn
  q60 = wE 2525 W

-- CA CK10 Gad(t=0, W=(), d=KSdKK, e=-1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ : ⟪ (ℓ "临上三上上中九丮九下下丈下") ⟫ʷ ≈ ⟪ (ℓ "三上上上上中九丮九下下下下丈临") ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ = derive (ℓ "临上三上上中九丮九下下丈下") (ℓ "三上上上上中九丮九下下下下丈临")
  (rw 0 q24 ∷
   rw 1 q58 ∷
   rw 0 q59 ∷
   rw 9 q60 ∷
   rw 14 q29 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 2526 W
  q62 : Eqn
  q62 = wE 2527 W
  q63 : Eqn
  q63 = wE 2528 W
  q64 : Eqn
  q64 = wE 1 W
  q65 : Eqn
  q65 = wE 3 W
  q66 : Eqn
  q66 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q67 : Eqn
  q67 = wE 1739 W
  q68 : Eqn
  q68 = wE 1738 W
  q69 : Eqn
  q69 = wE 1740 W
  q70 : Eqn
  q70 = wE 2529 W
  q71 : Eqn
  q71 = sE 2671 lem-PP-flip-ᵖ-1

-- spell Gad(t=0, W=(), d=SKdSSKdS, e=-1) -> Gad(t=0, W=(), d=1, e=1): 45 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (ℓ "丈下丈丈下丈中九丮九三上三三上三") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (ℓ "丈下丈丈下丈中九丮九三上三三上三") (ℓ "九中九丮")
  (rw 0 q61 ∷
   rw 10 q62 ∷
   rw 0 q63 ∷
   rw 4 q64 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q65 ∷
   rw 2 q66 ∷
   rw 3 q67 ∷
   rw 4 q64 ∷
   re 2 3 (ℓ "中") ∷
   rw⁻ 3 q66 ∷
   rw 4 q65 ∷
   rw 3 q68 ∷
   rw 6 q64 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 7 q65 ∷
   rw 4 q66 ∷
   rw 5 q69 ∷
   rw 6 q64 ∷
   re 4 3 (ℓ "丮") ∷
   rw⁻ 5 q66 ∷
   rw 6 q65 ∷
   rw 5 q68 ∷
   rw 3 q64 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q65 ∷
   rw 1 q66 ∷
   rw 2 q67 ∷
   rw 3 q64 ∷
   re 1 3 (ℓ "中") ∷
   rw⁻ 2 q66 ∷
   rw 3 q65 ∷
   rw 2 q68 ∷
   rw 5 q64 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q65 ∷
   rw 3 q66 ∷
   rw 4 q69 ∷
   rw 5 q64 ∷
   re 3 3 (ℓ "丮") ∷
   rw⁻ 4 q66 ∷
   rw 5 q65 ∷
   rw 4 q68 ∷
   rw 5 q70 ∷
   rw 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 2829 lem-HD-units
  q73 : Eqn
  q73 = sE 2835 lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩
  q74 : Eqn
  q74 = sE 2860 lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩
  q75 : Eqn
  q75 = sE 2839 lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SKd-e≡1⟩
  q76 : Eqn
  q76 = sE 2841 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡KdSKd-e≡1⟩
  q77 : Eqn
  q77 = sE 2834 lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩
  q78 : Eqn
  q78 = sE 2830 lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡1⟩
  q79 : Eqn
  q79 = sE 2857 lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKKK-e≡1⟩
  q80 : Eqn
  q80 = sE 2842 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKdSd-e≡1⟩
  q81 : Eqn
  q81 = sE 2832 lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩
  q82 : Eqn
  q82 = sE 2833 lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩
  q83 : Eqn
  q83 = sE 2840 lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSS-e≡1⟩
  q84 : Eqn
  q84 = sE 2861 lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩
  q85 : Eqn
  q85 = sE 2858 lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdKd-e≡1⟩
  q86 : Eqn
  q86 = sE 2843 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSSK-e≡1⟩
  q87 : Eqn
  q87 = sE 2836 lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩
  q88 : Eqn
  q88 = sE 2859 lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKKK-e≡1⟩
  q89 : Eqn
  q89 = sE 2856 lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SKKK-e≡1⟩
  q90 : Eqn
  q90 = sE 2844 lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKSdKK-e≡1⟩
  q91 : Eqn
  q91 = sE 2829 lem-HD-units

-- HD conj Gad(t=0, W=(), d=KSSKd, e=1): 20 steps
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑上丈丈下九中九丮上三三下") ⟫ʷ ≈ ⟪ (ℓ "上三上上九中九丮下下丈下丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑上丈丈下九中九丮上三三下") (ℓ "上三上上九中九丮下下丈下丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑")
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
  q92 = wE 2530 W
  q93 : Eqn
  q93 = wE 2531 W
  q94 : Eqn
  q94 = wE 2532 W
  q95 : Eqn
  q95 = sE 1117 lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012
  q96 : Eqn
  q96 = wE 2533 W

-- spell Gad(t=0, W=(), d=SdKdSS, e=-1) -> Gad(t=0, W=(), d=SKdSd, e=1): 26 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ : ⟪ (ℓ "三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "丈下三九中九丮丈上三") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ = derive (ℓ "三下丈丈中九丮九三三上丈") (ℓ "丈下三九中九丮丈上三")
  (rw 0 q92 ∷
   rw 12 q93 ∷
   rw 3 q94 ∷
   rw 7 q64 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q65 ∷
   rw 5 q66 ∷
   rw 6 q67 ∷
   rw 7 q64 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q66 ∷
   rw 7 q65 ∷
   rw 6 q68 ∷
   rw 9 q64 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q65 ∷
   rw 7 q66 ∷
   rw 8 q69 ∷
   rw 9 q64 ∷
   re 7 3 (ℓ "丮") ∷
   rw⁻ 8 q66 ∷
   rw 9 q65 ∷
   rw 8 q68 ∷
   rw 4 q95 ∷
   rw 8 q96 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 2534 W
  q98 : Eqn
  q98 = sE 2862 lem-PP2≡E-at1023
  q99 : Eqn
  q99 = wE 217 W
  q100 : Eqn
  q100 = eqn (ℓ "丌乜") (ℓ "乜丌") (low₁-comm (X) (CCZ))
  q101 : Eqn
  q101 = wE 1106 W
  q102 : Eqn
  q102 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q103 : Eqn
  q103 = wE 388 W
  q104 : Eqn
  q104 = wE 387 W

-- top z form: 10 steps
lem-top-z-form : ⟪ (ℓ "丌丒习丽习举丌丒丌丒习丽习举丌丒丌九中九丮丌") ⟫ʷ ≈ ⟪ (ℓ "丌乛九中九丮丌") ⟫ʷ
lem-top-z-form = derive (ℓ "丌丒习丽习举丌丒丌丒习丽习举丌丒丌九中九丮丌") (ℓ "丌乛九中九丮丌")
  (rw 6 q97 ∷
   rw 2 q98 ∷
   re 2 1 (ℓ "並乜並") ∷
   rw 1 q99 ∷
   rw 2 q100 ∷
   rw 3 q101 ∷
   re 1 3 (ℓ "乛") ∷
   rw⁻ 2 q102 ∷
   rw 3 q103 ∷
   rw 2 q104 ∷ []) Eq.refl
