{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D742 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.D.D039 using (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D042 using (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D043 using (lem-PP-flip-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D053 using (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D081 using (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D740 using (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩ ; lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡-1⟩ ; lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡KdKd-e≡-1⟩ ; lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩ ; lem-HD-units ; lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D741 using (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩ ; lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩ ; lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ ; lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ ; lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩ ; lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩)
-- pass [X1 CS10 X1] [S0 K0 Sd0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 S0 Kd0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 8 (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • K • (S • S • S) • K • K) (S • K • (S • S • S) • K • K • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 11 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 14 (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CSd10 Gad(t=0, W=(), d=SKSdKK, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩ = run b0
  where
  b0 : Chain (CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS)) ((S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0-Sd0) ▸
       at 0 6 (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (win 3 0 complete₃ ((S • S • S) • S • K • (S • S • S) • K • K) (K • (S • S • S) • K • K) tt tt Eq.refl) ▸
       at 8 5 (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) tt tt Eq.refl) ▸
       at 12 4 (CS01⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (X ↑) • CS • (X ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸ done


-- pass [X1 CKd10 X1] [K0 Sd0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 S0 Kd0]: 5 steps
lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 0 7 (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • K • K) (K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 13 (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CK10 Gad(t=0, W=(), d=KSdKK, e=-1): 5 steps
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ : ⟪ (CK10 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK10 ∷ []) ⟫ʷ
lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩ = run b0
  where
  b0 : Chain (CK10 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK10 ∷ [])
  b0 = at 0 1 (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ (CK₁₀) (K • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 15 (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-K0-Sd0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-S0-Kd0) ▸
       at 0 5 (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (win 3 0 complete₃ (K • K • (S • S • S) • K • K) ((S • S • S) • K • K • K • K) tt tt Eq.refl) ▸
       at 9 4 (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • K) tt tt Eq.refl) ▸
       at 14 4 (CK10 ∷ []) (win 3 0 complete₃ (K • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) (CK₁₀) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [Sd0 K0 K0 K0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Kd0 Kd0 Kd0 S0]: 3 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 8 (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • K • K • K • K) ((S • S • S) • K • K • K • K • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 5 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 8 (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • (K • iI) • (K • iI) • S) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CS10 Gad(t=0, W=(), d=SdKKKK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ : ⟪ (CS01 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ = run b0
  where
  b0 : Chain (CS01 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ [])
  b0 = at 0 1 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ (CS) (S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0) ▸
       at 0 6 (K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (win 3 0 complete₃ (S • (S • S • S) • K • K • K • K) (K • K • K • K) tt tt Eq.refl) ▸
       at 8 5 (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S) tt tt Eq.refl) ▸
       at 12 4 (CS01 ∷ []) (win 3 0 complete₃ (S • (X ↑) • (CS • CS • CS) • (X ↑)) (CS) tt tt Eq.refl) ▸ done


-- HD conj Gad(t=0, W=(), d=SdKdSS, e=-1): 20 steps
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ [])
  b0 = at 0 80 (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ []) (lem-HD-units) ▸
       at 17 13 (S0 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ S0⁻ ∷ CK30⁻ ∷ []) (lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩) ▸
       at 16 11 (K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ K0 ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡-1⟩) ▸
       at 15 9 (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ CK10⁻ ∷ []) (lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡KdSd-e≡-1⟩) ▸
       at 14 11 (K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩) ▸
       at 13 9 (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ CK20⁻ ∷ []) (lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡KdKd-e≡-1⟩) ▸
       at 12 11 (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡KdKdKd-e≡-1⟩) ▸
       at 11 13 (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ []) (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKdKd-e≡-1⟩) ▸ done

  b1 : Chain (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ []) (CS01 ∷ CK10 ∷ CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ [])
  b1 = at 10 11 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩) ▸
       at 9 13 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ []) (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩) ▸
       at 8 15 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK30 ∷ []) (lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩) ▸
       at 7 13 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ []) (lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩) ▸
       at 6 15 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩) ▸
       at 5 17 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK10⁻ ∷ []) (lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩) ▸
       at 4 15 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩) ▸
       at 3 13 (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ []) (lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩) ▸ done

  b2 : Chain (CS01 ∷ CK10 ∷ CS01⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CK30 ∷ CK20 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20⁻ ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK30⁻ ∷ []) (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  b2 = at 2 15 (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SKSdKK-e≡-1⟩) ▸
       at 1 13 (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK10 ∷ []) (lem-CA-CK10-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡-1⟩) ▸
       at 0 15 (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩) ▸
       at 12 18 (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (sym lem-HD-units) ▸ done


-- xconj [0] Gad(t=0, W=(), d=KKKK, e=-1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ : ⟪ (X0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ = run b0
  where
  b0 : Chain (X0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b0 = at 0 5 (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ (X • K • K • K • K) (S • (K • iI) • S • S • (K • iI) • S) tt tt Eq.refl) ▸
       at 10 5 (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (K • iI) • X) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) tt tt Eq.refl) ▸ done


-- k conj Gad(t=0, W=(), d=SK, e=-1): 5 steps
lem-k-conj-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ []) ⟫ʷ
lem-k-conj-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = run b0
  where
  b0 : Chain (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ [])
  b0 = at 90 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 81 10 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩) ▸
       at 1 92 (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (lem-HD-conj-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩) ▸
       at 13 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 0 14 (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩) ▸ done


-- spell Gad(t=0, W=(), d=SKdSSKdS, e=-1) -> Gad(t=0, W=(), d=1, e=1): 45 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ ι ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b0 = at 0 6 (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (S • (K • iI) • S • S • (K • iI) • S) tt tt Eq.refl) ▸
       at 10 6 (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) tt tt Eq.refl) ▸
       at 0 6 (X0 ∷ ι ∷ ι ∷ []) (win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (X • iI • iI) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 3 2 (CS02 ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ ι ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ ι ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (X0 ∷ ι ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b2 = at 4 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 5 2 (CS02⁻ ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X0 ∷ ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ CS03 ∷ ι ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b3 = at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 2 2 (CS02 ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (X0 ∷ CS03 ∷ ι ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ ι ∷ Sw23 ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ [])
  b4 = at 2 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 4 2 (CS02⁻ ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ ι ∷ Sw23 ∷ Toff012 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b5 = at 4 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 5 8 (X0 ∷ []) (win 3 0 complete₃ (iI • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) (X) tt tt Eq.refl) ▸
       at 0 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1) ▸ done


-- top k l = p k: 2 steps
lem-top-k-l-≡-p-k : ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ []) ⟫ʷ
lem-top-k-l-≡-p-k = run b0
  where
  b0 : Chain (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ [])
  b0 = at 0 90 (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ []) (lem-k-conj-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩) ▸
       at 0 16 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SKdSSKdS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩) ▸ done


-- xconj [0] Gad(t=0, W=(), d=1, e=1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b0 = at 0 1 (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (X) (K • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 8 1 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (win 3 0 complete₃ (X) (K • (S • S • S) • (S • S • S) • (K • iI)) tt tt Eq.refl) ▸ done


-- pass [X3 CK30 X3] [K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0]: 75 steps
lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b1 = at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 7 (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b2 = at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b3 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b4 = at 17 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 13 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 10 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 7 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 4 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸ done

  b5 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ [])
  b5 = at 27 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 25 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 22 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 21 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ [])
  b6 = at 20 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ [])
  b7 = at 14 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b8 = at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 19 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 11 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b9 = at 13 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- CA CKd30 Gad(t=0, W=(), d=KSSKd, e=1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : ⟪ (CK30⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK30⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K0⁻ ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 15 (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0) ▸
       at 0 5 (S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • K • S • S • (K • iI)) (S • S • (K • iI)) tt tt Eq.refl) ▸
       at 7 4 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI)) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CK30⁻ ∷ [])
  b2 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 11 4 (CK20⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CS10 X1] [S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0]: 5 steps
lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 6 (S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • S • (K • iI)) (S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 9 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 6 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 3 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 7 12 (K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CSd10 Gad(t=0, W=(), d=SSKd, e=1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ : ⟪ (CS01⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKd-e≡1⟩ = run b0
  where
  b0 : Chain (CS01⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS)) ((S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 13 (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0) ▸
       at 0 4 (S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • S • S • (K • iI)) (S • (K • iI)) tt tt Eq.refl) ▸
       at 6 3 (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S)) tt tt Eq.refl) ▸
       at 8 4 (CS01⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (X ↑) • CS • (X ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸ done

