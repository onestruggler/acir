{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D152 where

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
open import Examples.Groups.Clifford+CS.Four.D.D081 using (lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D151 using (lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
-- pass [CS10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS01 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ (CS • (X ↑)) ((X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3) ▸
       at 9 4 (X1 ∷ CS01 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑)) ((X ↑) • CS) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X1 CKd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 7 0 (X1 ∷ X1 ∷ []) (win 3 0 complete₃ (ε) ((X ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 0 (CK10 ∷ CK10⁻ ∷ []) (win 3 0 complete₃ (ε) (CK₁₀ • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 9 0 (X1 ∷ X1 ∷ []) (win 3 0 complete₃ (ε) ((X ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 7 (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((S ↑ • CK₁₀) • CK₁₀) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CKd10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 0 (CS02 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (CS02⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 7 (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ Toff012 ∷ [])
  b3 = at 9 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b4 = at 7 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CKd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 3 (X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 6 4 (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 7 4 (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3) ▸
       at 9 4 (X1 ∷ CK10⁻ ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X1 CSd10 X1] [TOFF012]: 1 steps
lem-pass-X1-CSd10-X1-vs-TOFF012 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • Toff) (Toff • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [CS03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CS03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b1 = at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [CSd03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CSd03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b1 = at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012) ▸
       at 1 4 (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03) ▸
       at 2 4 (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012) ▸
       at 3 4 (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CSd03) ▸ done


-- pass [X1 CSd10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 0 (CS02 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (CS02⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 7 (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ Toff012 ∷ [])
  b3 = at 9 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b4 = at 7 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CSd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 3 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 6 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 7 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (X ↑)) ((X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3) ▸
       at 9 4 (X1 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑)) ((X ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- ca-split Gad(t=0, W=(1, 2, 3), d=SdKdSS, e=-1) 1: 31 steps
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 : ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (S0⁻ ∷ K0⁻ ∷ X1 ∷ S0 ∷ X2 ∷ X3 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸
       at 1 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 0 2 (S0⁻ ∷ X1 ∷ []) (sym (low₁-comm ((S • S • S)) (X))) ▸
       at 3 2 (K0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((K • iI)) ((X ↑ ↑)))) ▸
       at 2 2 (K0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((K • iI)) ((X ↑)))) ▸
       at 1 2 (K0⁻ ∷ X1 ∷ []) (sym (low₁-comm ((K • iI)) (X))) ▸
       at 4 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 3 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸ done

  b1 : Chain (S0⁻ ∷ K0⁻ ∷ X1 ∷ S0 ∷ X2 ∷ X3 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (S0 ∷ X1 ∷ []) (sym (low₁-comm (S) (X))) ▸
       at 5 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 4 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 3 2 (S0 ∷ X1 ∷ []) (sym (low₁-comm (S) (X))) ▸
       at 14 2 (X1 ∷ S0 ∷ []) (low₁-comm (S) (X)) ▸
       at 13 2 (X1 ∷ K0 ∷ []) (low₁-comm (K) (X)) ▸
       at 12 2 (X1 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (X)) ▸
       at 11 2 (X1 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (X)) ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 15 2 (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑))) ▸
       at 14 2 (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑))) ▸
       at 13 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 12 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 16 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 15 2 (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑))) ▸
       at 14 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 13 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b3 = at 0 4 (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ []) (win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS) tt tt Eq.refl) ▸
       at 26 4 (CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 15 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ []) (lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 14 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ []) (lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 13 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ []) (lem-pass-CKd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 12 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) (lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 22 8 [] (win 3 0 complete₃ ((CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS • (CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS) (ε) tt tt Eq.refl) ▸ done


-- comm CCZ012 CSd23: 19 steps
lem-comm-CCZ012-CSd23 : ⟪ (CCZ012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CSd23 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ012 ∷ CS23⁻ ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ []) (CS01 ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CS23⁻ ∷ CCZ012 ∷ [])
  b2 = at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 1 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [CSd23]: 1 steps
lem-pass-CCZ012-vs-CSd23 : ⟪ (CCZ012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd23 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd23) ▸ done


-- pass [TOFF012] [CSd23]: 5 steps
lem-pass-TOFF012-vs-CSd23 : ⟪ (Toff012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CSd23 = run b0
  where
  b0 : Chain (Toff012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (((CS • CS • CS) ↑))) ▸
       at 1 2 (CS23⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd23) ▸
       at 0 2 (CS23⁻ ∷ K0 ∷ []) (low₁-comm (K) (((CS • CS • CS) ↑))) ▸
       at 1 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done

