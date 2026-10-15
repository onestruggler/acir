{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D659 where

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
open import Examples.Groups.Clifford+CS.Four.D.D038 using (lem-pass-CZ12-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D045 using (lem-pass-CCZ123-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D049 using (lem-pass-CCZ123-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D054 using (lem-pass-CCZ123-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D055 using (lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D070 using (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D071 using (lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D074 using (lem-pass-X2-CKd21-X2-vs-CS03 ; lem-pass-X2-CKd21-X2-vs-CSd03 ; lem-pass-X2-CKd21-X2-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D297 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2)
open import Examples.Groups.Clifford+CS.Four.D.D302 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2)
open import Examples.Groups.Clifford+CS.Four.D.D602 using (lem-pass-CZ12-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D624 using (lem-pass-CS03-vs-CZ13 ; lem-pass-CS03-vs-Z1)
open import Examples.Groups.Clifford+CS.Four.D.D625 using (lem-pass-CSd03-vs-CZ13 ; lem-pass-CSd03-vs-Z1 ; lem-pass-TOFF012-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D634 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2)
open import Examples.Groups.Clifford+CS.Four.D.D635 using (lem-pass-CCZ123-vs-X2-CK20-X2 ; lem-pass-CCZ123-vs-X2-CKd20-X2 ; lem-pass-CCZ123-vs-X2-CS02-X2 ; lem-pass-CCZ123-vs-X2-CSd02-X2)
open import Examples.Groups.Clifford+CS.Four.D.D656 using (lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D658 using (lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 ; lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
-- CA CSd10 Gad(t=0, W=(2, 3), d=1, e=1): 9 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ : ⟪ (CS01⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS01⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS)) ((S • S • S) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 0 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 1 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 2 1 (S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S)) ((S • S • S)) tt tt Eq.refl) ▸
       at 7 0 (S0 ∷ S0⁻ ∷ []) (win 3 0 complete₃ (ε) (S • (S • S • S)) tt tt Eq.refl) ▸
       at 8 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 9 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  b1 = at 10 4 (CS01⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (X ↑) • CS • (X ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸ done


-- pass [X2 CKd20 X2] [X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X3]: 27 steps
lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b1 : Chain (X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 1 4 (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S)) ((S • S • S) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 6 10 (S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • S) (S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b3 = at 9 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CKd20] [X2 X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = run b0
  where
  b0 : Chain (CK20⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3) ▸
       at 9 4 (X2 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X1 CSd10 X1] [X2 X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 4 (S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S)) ((S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 3 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 7 4 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S) (S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 8 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 9 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- CA CS10 Gad(t=0, W=(2, 3), d=Sd, e=1): 9 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ : ⟪ (CS01 ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 1 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ (CS) (S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 13 (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3) ▸
       at 0 2 (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑))) ▸
       at 1 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 2 2 [] (win 3 0 complete₃ (S • (S • S • S)) (ε) tt tt Eq.refl) ▸
       at 6 1 (S0 ∷ []) (win 3 0 complete₃ (S) (S) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑))) ▸
       at 7 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS01 ∷ [])
  b1 = at 8 4 (CS01 ∷ []) (win 3 0 complete₃ (S • (X ↑) • (CS • CS • CS) • (X ↑)) (CS) tt tt Eq.refl) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 6 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  b0 = at 0 29 (CK20 ∷ CS01 ∷ CK20⁻ ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((Swap ↑ • CK₁₀ • Swap ↑) • CS • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 3 9 (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) (lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩) ▸
       at 2 11 (X2 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) (lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡1⟩) ▸
       at 0 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 8 4 (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • CS • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS • CS • CS)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) tt tt Eq.refl) ▸ done


-- Bar(SSKSKK;2,1->0) passes split Gad(t=0, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 32 (X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2) ▸
       at 3 32 (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2) ▸
       at 6 32 (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS02-X2) ▸
       at 9 32 (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2) ▸
       at 12 37 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 20 32 (X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK20-X2) ▸
       at 23 32 (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2) ▸
       at 26 32 (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd02-X2) ▸ done

  b1 : Chain (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  b1 = at 29 32 (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd20-X2) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  b0 = at 29 16 (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 61 (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 32 (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- pass [X2 CKd21 X2] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸
       at 1 4 (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03) ▸
       at 2 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸
       at 3 4 (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CSd03) ▸ done


-- pass [X2 CKd21 X2] [X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ []) (X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 7 (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 9 7 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 13 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd21] [X2 X3 K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X2-X3 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 17 (X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X3-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0-X3) ▸
       at 15 4 (X2 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [Z1 CZ12 CZ13 CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 16 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 3 2 (Toff012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF012) ▸
       at 2 2 (Toff012 ∷ CZ13 ∷ []) (sym lem-pass-TOFF012-vs-CZ13) ▸
       at 1 2 (Toff012 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ Z1 ∷ []) (win 3 0 complete₃ ((Z ↑) • Toff) (Toff • (Z ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS03) ▸
       at 3 2 (CS03 ∷ CZ13 ∷ []) (sym lem-pass-CS03-vs-CZ13) ▸
       at 2 2 (CS03 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS03) ▸
       at 1 2 (CS03 ∷ Z1 ∷ []) (sym lem-pass-CS03-vs-Z1) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF012) ▸
       at 4 2 (Toff012 ∷ CZ13 ∷ []) (sym lem-pass-TOFF012-vs-CZ13) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ Z1 ∷ []) (win 3 0 complete₃ ((Z ↑) • Toff) (Toff • (Z ↑)) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd03) ▸
       at 5 2 (CS03⁻ ∷ CZ13 ∷ []) (sym lem-pass-CSd03-vs-CZ13) ▸
       at 4 2 (CS03⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd03) ▸
       at 3 2 (CS03⁻ ∷ Z1 ∷ []) (sym lem-pass-CSd03-vs-Z1) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 8 (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03) ▸ done


-- pass [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 : ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (X2 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 7 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 2 8 (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123) ▸
       at 1 2 (Z1 ∷ X3 ∷ []) (sym (low-comm ((Z ↑)) ((X ↑)))) ▸
       at 2 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 3 2 (Z1 ∷ CZ13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CZ • Swap ↑)) (Z • (Swap ↑ • CZ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 0 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 1 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 4 2 (CZ13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 5 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 0 9 (CCZ123 ∷ []) (win 0 3 complete₃ (Z • Z • CZ • Z • (Swap ↑ • CZ • Swap ↑) • Z • CZ • (Swap ↑ • CZ • Swap ↑) • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CCZ123) ▸ done


-- CCZ(2,3,1) passes split Gad(t=0, W=(2, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨231⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X2 ∷ CK20 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK20-X2) ▸
       at 3 4 (X2 ∷ CS02 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS02-X2) ▸
       at 6 4 (X2 ∷ CS02 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS02-X2) ▸
       at 9 4 (X2 ∷ CK20⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd20-X2) ▸
       at 12 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 20 4 (X2 ∷ CK20 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK20-X2) ▸
       at 23 4 (X2 ∷ CS02⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd02-X2) ▸
       at 26 4 (X2 ∷ CS02⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd02-X2) ▸ done

  b1 : Chain (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b1 = at 29 4 (X2 ∷ CK20⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd20-X2) ▸ done

