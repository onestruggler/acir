{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D741 where

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
open import Examples.Groups.Clifford+CS.Four.D.D045 using (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D055 using (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D066 using (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D070 using (lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D071 using (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D081 using (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
-- pass [X1 CSd10 X1] [S0 Kd0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 K0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 6 (S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • (K • iI) • S) (S • (K • iI) • S • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 12 (S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CS10 Gad(t=0, W=(), d=SKdS, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩ : ⟪ (CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SKdS-e≡-1⟩ = run b0
  where
  b0 : Chain (CS01 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ [])
  b0 = at 0 1 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ (CS) (S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 13 (S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0) ▸
       at 0 4 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ (S • S • (K • iI) • S) (S • S • (K • iI) • S) tt tt Eq.refl) ▸
       at 8 3 (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ ((S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • S) tt tt Eq.refl) ▸
       at 12 4 (CS01 ∷ []) (win 3 0 complete₃ (S • (X ↑) • (CS • CS • CS) • (X ↑)) (CS) tt tt Eq.refl) ▸ done


-- pass [X2 CKd20 X2] [S0 S0 Kd0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 K0 Sd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 7 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • S • S • (K • iI) • S) (S • S • (K • iI) • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 19 (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- CA CK20 Gad(t=0, W=(), d=SSKdS, e=-1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩ : ⟪ (CK20 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩ = run b0
  where
  b0 : Chain (CK20 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ [])
  b0 = at 0 1 (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑)) (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 15 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0) ▸
       at 0 5 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (K • S • S • (K • iI) • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 9 4 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ ((S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • K) tt tt Eq.refl) ▸
       at 14 4 (CK20 ∷ []) (win 3 0 complete₃ (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 S0]: 79 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b1 = at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 8 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ Sw23 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 5 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b3 = at 11 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b4 = at 17 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 14 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 11 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b5 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b5 = at 8 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 29 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 28 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 27 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 26 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 25 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 24 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b6 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b6 = at 23 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 21 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b7 = at 17 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ Sw23 ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ [])
  b8 = at 11 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 20 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 11 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b9 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ Sw23 ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b9 = at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- CA CK30 Gad(t=0, W=(), d=SdKdSSKd, e=-1): 23 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ : ⟪ (CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑)) (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K0 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 17 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0) ▸
       at 0 6 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • K • S) tt tt Eq.refl) ▸
       at 8 5 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • K) tt tt Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK30 ∷ [])
  b2 = at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 13 4 (CK20 ∷ []) (win 3 0 complete₃ (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CK20 X2] [S0 S0 K0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Kd0 Sd0 Sd0]: 7 steps
lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 7 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • S • K • S) (S • S • K • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 19 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- CA CKd20 Gad(t=0, W=(), d=SSKS, e=-1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩ : ⟪ (CK20⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SSKS-e≡-1⟩ = run b0
  where
  b0 : Chain (CK20⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20⁻ ∷ [])
  b0 = at 0 1 (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 15 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0) ▸
       at 0 5 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • S • S • K • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 9 4 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • (K • iI)) tt tt Eq.refl) ▸
       at 14 4 (CK20⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [X1 CS10 X1] [Sd0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 8 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 11 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 14 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CSd10 Gad(t=0, W=(), d=SdKdSSKd, e=-1): 5 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ : ⟪ (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ = run b0
  where
  b0 : Chain (CS01⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS)) ((S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0) ▸
       at 0 6 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 10 5 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) tt tt Eq.refl) ▸
       at 16 4 (CS01⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (X ↑) • CS • (X ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸ done


-- pass [X1 CK10 X1] [S0 S0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 Sd0 Sd0]: 5 steps
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0 = run b0
  where
  b0 : Chain (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  b0 = at 0 9 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 15 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CKd10 Gad(t=0, W=(), d=SSKdSSKd, e=-1): 5 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ : ⟪ (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSSKd-e≡-1⟩ = run b0
  where
  b0 : Chain (CK10⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK10⁻ ∷ [])
  b0 = at 0 1 (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((S ↑ • CK₁₀)) ((K • iI) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 1 19 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-S0-S0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-Sd0-Sd0) ▸
       at 0 7 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S • S • (K • iI)) (S • S • K • S • S) tt tt Eq.refl) ▸
       at 9 6 (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) tt tt Eq.refl) ▸
       at 14 4 (CK10⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • (X ↑) • CK₁₀ • (X ↑)) ((S ↑ • CK₁₀)) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [S0 S0 K0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 Kd0 Sd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 8 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • S • K • S • S) (S • S • K • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 11 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 14 (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CS10 Gad(t=0, W=(), d=SSKSS, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩ : ⟪ (CS01 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSKSS-e≡-1⟩ = run b0
  where
  b0 : Chain (CS01 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ CS01 ∷ [])
  b0 = at 0 1 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ (CS) (S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0) ▸
       at 0 6 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ (S • S • S • K • S • S) ((S • S • S) • K • S • S) tt tt Eq.refl) ▸
       at 8 5 (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • S • S) tt tt Eq.refl) ▸
       at 12 4 (CS01 ∷ []) (win 3 0 complete₃ (S • (X ↑) • (CS • CS • CS) • (X ↑)) (CS) tt tt Eq.refl) ▸ done


-- pass [X2 CKd20 X2] [Sd0 K0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 Kd0 S0]: 7 steps
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 7 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • K • S • S) ((S • S • S) • K • S • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 19 (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • (K • iI) • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- CA CK20 Gad(t=0, W=(), d=SdKSS, e=-1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩ : ⟪ (CK20 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡-1⟩ = run b0
  where
  b0 : Chain (CK20 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ CK20 ∷ [])
  b0 = at 0 1 (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑)) (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 15 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0) ▸
       at 0 5 (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (win 3 0 complete₃ (K • (S • S • S) • K • S • S) (S • K • (S • S • S) • K • K) tt tt Eq.refl) ▸
       at 9 4 (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • K) tt tt Eq.refl) ▸
       at 14 4 (CK20 ∷ []) (win 3 0 complete₃ (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸ done

