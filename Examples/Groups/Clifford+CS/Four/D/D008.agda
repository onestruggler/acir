{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D008 where

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
open import Examples.Groups.Clifford+CS.Four.D.D003 using (lem-N32-PP3 ; lem-SW-T-SW)
open import Examples.Groups.Clifford+CS.Four.D.D005 using (lem-CCZ012-passes-PP3 ; lem-CCZ123-passes-PP3 ; lem-CS12-passes-PP3 ; lem-CS13-passes-PP3 ; lem-N23-D ; lem-N23-PP3)
open import Examples.Groups.Clifford+CS.Four.D.D006 using (lem-CCZ013-passes-PP3 ; lem-CZ13-passes-PP3 ; lem-comm-CCZ123-CCZ012)
open import Examples.Groups.Clifford+CS.Four.D.D007 using (lem-comm-CCZ123-CCZ013)
-- comm CCZ013 CS12: 85 steps
lem-comm-CCZ013-CS12 : ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CCZ013 ∷ CS12 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS12 ∷ [])
  b1 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS12 ∷ []) (CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ [])
  b2 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b3 : Chain (CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CS12 ∷ [])
  b3 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CS12 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ [])
  b4 = at 4 2 (CS12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS)) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ []) (CS01 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ [])
  b5 = at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (CS ↑)) ((CS ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS)) ▸ done

  b6 : Chain (CS01 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (CS12 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ [])
  b6 = at 2 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS12 ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (CS ↑)) ((CS ↑) • CS) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (CS12 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CS12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b7 = at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 2 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CS12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b8 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CS12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CS12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b9 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (CS12 ∷ CCZ013 ∷ [])
  b10 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- comm CCZ013 CCZ012: 51 steps
lem-comm-CCZ013-CCZ012 : ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CCZ012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ013 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b0 = at 2 0 (CX32 ∷ CX32 ∷ []) (win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 0 (CCZ012 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (ε) (CCZ • CCZ) tt tt Eq.refl) ▸
       at 4 0 (CX32 ∷ CX32 ∷ []) (win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 1 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b2 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CCZ013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b3 = at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b4 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b4 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (Sw23 ∷ CCZ012 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ [])
  b5 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ CCZ012 ∷ CCZ012 ∷ Sw23 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ [])
  b6 = at 1 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸ done


-- comm CCZ012 CZ13: 51 steps
lem-comm-CCZ012-CZ13 : ⟪ (CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ012 ∷ CZ13 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CZ13 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 7 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ)) ▸
       at 5 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ CX20 ∷ CZ13 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ [])
  b2 = at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 3 2 (CZ12 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (CZ ↑)) ((CZ ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CX20 ∷ CZ13 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b3 = at 3 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CS01 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b4 = at 5 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ)) ▸
       at 3 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b5 = at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 2 (CZ12 ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • (CZ ↑)) ((CZ ↑) • CS) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ13 ∷ CCZ012 ∷ [])
  b6 = at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- S3: 252 steps
lem-S3 : ⟪ (Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-S3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ []) (CX23 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ CX32 ∷ CCZ123 ∷ CX32 ∷ CX23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (win 0 3 complete₃ ((Swap ↑)) ((CX₀₁ ↑) • (CX₁₀ ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 7 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (win 0 3 complete₃ ((Swap ↑)) ((CX₀₁ ↑) • (CX₁₀ ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 2 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ []) (lem-N23-PP3) ▸
       at 6 0 (CX32 ∷ CX32 ∷ []) (win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 6 (CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-N32-PP3) ▸
       at 11 0 (CX32 ∷ CX32 ∷ []) (win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 10 0 (CX32 ∷ CX32 ∷ []) (win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS12 ∷ CS13 ∷ CCZ123 ∷ []) (win 0 3 complete₃ ((CX₁₀ ↑) • CS • (CX₁₀ ↑)) (CS • (Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸ done

  b1 : Chain (CX23 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ CX32 ∷ CCZ123 ∷ CX32 ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ CX23 ∷ [])
  b1 = at 11 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 13 3 (CCZ123 ∷ CZ13 ∷ []) (win 0 3 complete₃ ((CX₁₀ ↑) • CCZ • (CX₁₀ ↑)) (CCZ • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CS12-passes-PP3) ▸
       at 5 5 (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CS13-passes-PP3) ▸
       at 6 5 (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CCZ123-passes-PP3) ▸
       at 7 5 (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CCZ012-passes-PP3) ▸
       at 8 5 (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CCZ013-passes-PP3) ▸
       at 9 5 (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CCZ123-passes-PP3) ▸ done

  b2 : Chain (CX23 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CCZ013 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b2 = at 10 5 (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-CZ13-passes-PP3) ▸
       at 3 2 (CS12 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • CS) (CS • CCZ) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ012) ▸
       at 7 2 (CCZ013 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ013) ▸
       at 9 2 (CZ13 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (CS12 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS12) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CCZ013 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b3 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b4 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b5 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) tt tt Eq.refl) ▸ done

  b6 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b6 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b7 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b8 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b9 : Chain (CX23 ∷ CS13 ∷ CS12 ∷ CS13 ∷ CCZ013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ013 ∷ CCZ123 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CCZ013 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b9 = at 5 2 (CCZ012 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ012) ▸
       at 6 2 (CCZ013 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ013) ▸
       at 8 2 (CZ13 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ012) ▸
       at 7 2 (CZ13 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CCZ013 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b10 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b11 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b12 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b13 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b13 = at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b14 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b14 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b15 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b15 = at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CCZ013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b16 = at 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b17 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b17 = at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b18 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b18 = at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) tt tt Eq.refl) ▸ done

  b19 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b19 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b20 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ CCZ013 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b21 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b22 : Chain (CX23 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ012 ∷ CZ13 ∷ CCZ013 ∷ CCZ013 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b22 = at 4 2 (CZ13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ13) ▸
       at 3 2 (CZ13 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CZ13 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CZ13 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 3 2 (CZ13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b23 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b24 = at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b25 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b26 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b26 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b27 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ Sw23 ∷ CCZ012 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ [])
  b27 = at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (CX23 ∷ CZ13 ∷ CS12 ∷ CZ13 ∷ CCZ012 ∷ Sw23 ∷ CCZ012 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CCZ123 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ CX23 ∷ [])
  b28 = at 6 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 2 2 (CZ13 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) (lem-CCZ123-passes-PP3) ▸
       at 2 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) (lem-CCZ012-passes-PP3) ▸
       at 1 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) (lem-CS12-passes-PP3) ▸ done

  b29 : Chain (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CZ12 ∷ [])
  b29 = at 5 0 (CX23 ∷ CX23 ∷ []) (win 0 3 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ []) (lem-N23-PP3) ▸
       at 10 0 (CX23 ∷ CX23 ∷ []) (win 0 3 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 9 0 (CX23 ∷ CX23 ∷ []) (win 0 3 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS12 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • CS • (CX₀₁ ↑)) (CS) tt tt Eq.refl) ▸
       at 8 3 (CCZ012 ∷ []) (lem-N23-D) ▸
       at 9 3 (CCZ123 ∷ CZ12 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • CCZ • (CX₀₁ ↑)) (CCZ • CZ) tt tt Eq.refl) ▸
       at 6 2 (CS12 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • CS) (CS • CCZ) tt tt Eq.refl) ▸ done

  b30 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CZ12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ12 ∷ CS12 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b30 = at 7 2 (CCZ012 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ012) ▸
       at 9 2 (CZ12 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • CZ) (CZ • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 8 2 (CZ12 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • CZ) (CZ • CCZ) tt tt Eq.refl) ▸
       at 7 2 (CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 6 2 (CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CZ12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (CZ ↑)) ((CZ ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CZ12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (CZ ↑)) ((CZ ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b31 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ12 ∷ CS12 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b31 = at 5 2 (CZ12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (CS ↑)) ((CZ ↑)) tt tt Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ ((CZ ↑) • (CZ ↑)) (ε) tt tt Eq.refl) ▸ done


-- S2: 28 steps
lem-S2 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-S2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b0 = at 0 4 (Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ []) (sym lem-S3) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (lem-SW-T-SW) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff013 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b1 = at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 2 3 (Toff013 ∷ []) (lem-SW-T-SW) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ Sw23 ∷ Sw01 ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b3 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS12⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

