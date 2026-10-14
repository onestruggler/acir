{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D074 where

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
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CS13-vs-CSd03 ; lem-pass-TOFF012-vs-CS13 ; lem-pass-TOFF102-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D031 using (lem-pass-CSd13-vs-CSd03 ; lem-pass-TOFF012-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 ; lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 ; lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
-- pass [TOFF012] [X2 TOFF102 X2]: 1 steps
lem-pass-TOFF012-vs-X2-TOFF102-X2 : ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (win 3 0 complete₃ (Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 4 steps
lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = run b0
  where
  b0 : Chain (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff012 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸
       at 3 2 (CS13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13) ▸
       at 4 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸
       at 7 2 (CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CSd13) ▸ done


-- pass [CSd03] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 26 steps
lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (CS03⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ [])
  b0 = at 1 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ CS03⁻ ∷ Sw23 ∷ CX01 ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b1 = at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 0 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸
       at 5 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b2 : Chain (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ CS03⁻ ∷ Sw23 ∷ CX01 ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ CX01 ∷ Toff102 ∷ CS03⁻ ∷ CS13⁻ ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸ done

  b3 : Chain (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ CX01 ∷ Toff102 ∷ CS03⁻ ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ [])
  b3 = at 4 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 3 9 (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13) ▸
       at 2 9 (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13) ▸
       at 1 9 (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13) ▸
       at 0 9 (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13) ▸ done


-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [TOFF102 CS13 TOFF102 CSd13]: 9 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 5 2 (X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 2 (X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 12 (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13) ▸
       at 0 4 (Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 4 (Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b1 = at 3 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CKd21 X2] [CS03]: 39 steps
lem-pass-X2-CKd21-X2-vs-CS03 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ []) (X2 ∷ CK21⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ CK21⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ CK21⁻ ∷ X2 ∷ [])
  b2 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CK32⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01 ∷ CK32⁻ ∷ []) (sym (low-comm (CS) ((S ↑ • CK₁₀)))) ▸
       at 4 2 (Sw12 ∷ CK31⁻ ∷ []) (win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • Swap) (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X2 ∷ CS03 ∷ CK21⁻ ∷ X2 ∷ []) (Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ [])
  b3 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ []) (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b4 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CKd21 X2] [TOFF012]: 1 steps
lem-pass-X2-CKd21-X2-vs-TOFF012 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CKd21 X2] [CSd03]: 39 steps
lem-pass-X2-CKd21-X2-vs-CSd03 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ CK21⁻ ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ CK21⁻ ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ X2 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03⁻ ∷ CK21⁻ ∷ X2 ∷ [])
  b2 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CK32⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ CK32⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((S ↑ • CK₁₀)))) ▸
       at 4 2 (Sw12 ∷ CK31⁻ ∷ []) (win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • Swap) (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X2 ∷ CS03⁻ ∷ CK21⁻ ∷ X2 ∷ []) (Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ [])
  b3 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ []) (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b4 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CKd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸ done


-- pass [CKd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CSd21 X2] [CS03]: 39 steps
lem-pass-X2-CSd21-X2-vs-CS03 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ []) (X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ CS12⁻ ∷ X2 ∷ [])
  b2 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X2 ∷ CS03 ∷ CS12⁻ ∷ X2 ∷ []) (Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ [])
  b3 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ []) (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b4 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CSd21 X2] [TOFF012]: 1 steps
lem-pass-X2-CSd21-X2-vs-TOFF012 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CSd21 X2] [CSd03]: 39 steps
lem-pass-X2-CSd21-X2-vs-CSd03 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ CS12⁻ ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ X2 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03⁻ ∷ CS12⁻ ∷ X2 ∷ [])
  b2 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((CS • CS • CS)))) ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X2 ∷ CS03⁻ ∷ CS12⁻ ∷ X2 ∷ []) (Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ [])
  b3 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ []) (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b4 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CSd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF012) ▸ done


-- pass [CSd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 6 8 (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2) ▸
       at 0 7 (CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (sym lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 1 7 (CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (sym lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 2 10 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 7 (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (sym lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 7 7 (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (sym lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 0 8 (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2) ▸ done

