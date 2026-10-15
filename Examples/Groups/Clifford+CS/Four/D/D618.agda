{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D618 where

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
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-pass-CCZ012-vs-CCZ013)
-- pass [CCZ123] [X3 CKd32 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CKd32-X3 : ⟪ (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd32-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X3 ∷ CK32⁻ ∷ X3 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X3 CS23 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X3 ∷ CS23 ∷ X3 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [CS23]: 1 steps
lem-pass-CCZ123-vs-CS23 : ⟪ (CCZ123 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CS23 = run b0
  where
  b0 : Chain (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CS23 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CZ12] [CS23]: 1 steps
lem-pass-CZ12-vs-CS23 : ⟪ (CZ12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CS23 = run b0
  where
  b0 : Chain (CZ12 ∷ CS23 ∷ []) (CS23 ∷ CZ12 ∷ [])
  b0 = at 0 2 (CS23 ∷ CZ12 ∷ []) (win 0 3 complete₃ (CZ • (CS ↑)) ((CS ↑) • CZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [CSd23]: 1 steps
lem-pass-CCZ123-vs-CSd23 : ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CSd23 = run b0
  where
  b0 : Chain (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) tt tt Eq.refl) ▸ done


-- comm CCZ013 CSd23: 97 steps
lem-comm-CCZ013-CSd23 : ⟪ (CCZ013 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (CCZ013 ∷ CS23⁻ ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS23⁻ ∷ [])
  b1 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS23⁻ ∷ []) (CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ CS23⁻ ∷ [])
  b2 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b3 : Chain (CS01 ∷ Sw23 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ CS23⁻ ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CS23⁻ ∷ [])
  b3 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CS23⁻ ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw01 ∷ CX31 ∷ CS23⁻ ∷ Sw01 ∷ CS13 ∷ [])
  b4 = at 4 2 (CS23⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw01 ∷ CX31 ∷ CS23⁻ ∷ Sw01 ∷ CS13 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CS23⁻ ∷ CX30 ∷ CS13 ∷ [])
  b5 = at 4 2 (CS23⁻ ∷ CX31 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (CS01 ∷ CX30 ∷ CS01⁻ ∷ CS23⁻ ∷ CX30 ∷ CS13 ∷ []) (CS01 ∷ Sw01 ∷ CX31 ∷ CS23⁻ ∷ Sw01 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ [])
  b6 = at 2 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS01 ∷ Sw01 ∷ CX31 ∷ CS23⁻ ∷ Sw01 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (CS01 ∷ CS23⁻ ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ [])
  b7 = at 2 2 (CS23⁻ ∷ CX31 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (CS01 ∷ CS23⁻ ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (CS23⁻ ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ [])
  b8 = at 0 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CS23⁻ ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ []) (CS23⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b9 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 2 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (CS23⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CS23⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b10 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b11 : Chain (CS23⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CS23⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b11 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CS23⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (CS23⁻ ∷ CCZ013 ∷ [])
  b12 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CCZ013] [CSd23]: 1 steps
lem-pass-CCZ013-vs-CSd23 : ⟪ (CCZ013 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd23 = run b0
  where
  b0 : Chain (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd23) ▸ done


-- pass [CZ12] [CSd23]: 1 steps
lem-pass-CZ12-vs-CSd23 : ⟪ (CZ12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CSd23 = run b0
  where
  b0 : Chain (CZ12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ12 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CZ12 ∷ []) (win 0 3 complete₃ (CZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CZ) tt tt Eq.refl) ▸ done


-- pass [CZ01] [CSd23]: 1 steps
lem-pass-CZ01-vs-CSd23 : ⟪ (CZ01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CZ01 ∷ []) ⟫ʷ
lem-pass-CZ01-vs-CSd23 = run b0
  where
  b0 : Chain (CZ01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ01 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ CZ01 ∷ []) (low-comm (CZ) ((CS • CS • CS))) ▸ done


-- pass [TOFF201] [CCZ013]: 13 steps
lem-pass-TOFF201-vs-CCZ013 : ⟪ (Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CCZ013 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ013 ∷ []) (K2 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ012 ∷ K2⁻ ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (win 3 0 complete₃ (Toffᵗ) ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ K3⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ K3⁻ ∷ []) (sym (low₃-comm (CCZ) ((K • iI)))) ▸
       at 4 2 (Sw23 ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CCZ013) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K2 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ012 ∷ K2⁻ ∷ []) (CCZ013 ∷ Toff201 ∷ [])
  b1 = at 0 2 (Sw23 ∷ K3 ∷ []) (win 0 3 complete₃ ((K ↑) • (Swap ↑)) ((Swap ↑) • (K ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ K3 ∷ []) (sym (low₃-comm (CCZ) (K))) ▸
       at 2 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff201 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CCZ013] [TOFF201]: 1 steps
lem-pass-CCZ013-vs-TOFF201 : ⟪ (CCZ013 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-TOFF201 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (Toff201 ∷ CCZ013 ∷ []) (sym lem-pass-TOFF201-vs-CCZ013) ▸ done

