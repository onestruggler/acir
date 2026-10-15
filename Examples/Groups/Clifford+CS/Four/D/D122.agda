{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D122 where

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
open import Examples.Groups.Clifford+CS.Four.D.D018 using (lem-S2-at2013)
-- pass [X3 CS32 X3] [TOFF203]: 67 steps
lem-pass-X3-CS32-X3-vs-TOFF203 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b4 : Chain (X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b8 : Chain (Toff203 ∷ X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b8 = at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [X3 CS32 X3] [CS12]: 1 steps
lem-pass-X3-CS32-X3-vs-CS12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [X3 CS32 X3] [CSd12]: 1 steps
lem-pass-X3-CS32-X3-vs-CSd12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [X3 CS32 X3] [TOFF203 CS12 TOFF203 CSd12]: 4 steps
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF203) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS12) ▸
       at 2 4 (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF203) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CSd12) ▸ done


-- pass [X3 CS32 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 3 4 (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (lem-S2-at2013) ▸
       at 0 7 (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12) ▸
       at 0 4 (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-S2-at2013) ▸ done


-- pass [X3 CS32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ Toff201 ∷ [])
  b0 = at 0 0 (CS23 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (ε) ((CS ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 0 (Toff201 ∷ Toff201 ∷ []) (win 3 0 complete₃ (ε) (Toffᵗ • Toffᵗ) tt tt Eq.refl) ▸
       at 2 0 (CS23⁻ ∷ CS23 ∷ []) (win 0 3 complete₃ (ε) (((CS • CS • CS) ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 3 0 (Toff201 ∷ Toff201 ∷ []) (win 3 0 complete₃ (ε) (Toffᵗ • Toffᵗ) tt tt Eq.refl) ▸
       at 4 7 (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23) ▸
       at 10 2 [] (win 0 3 complete₃ (((CS • CS • CS) ↑) • (CS ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Toffᵗ • Toffᵗ) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((CS ↑) • ((CS • CS • CS) ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b1 = at 7 2 [] (win 3 0 complete₃ (Toffᵗ • Toffᵗ) (ε) tt tt Eq.refl) ▸ done


-- pass [CS32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = run b0
  where
  b0 : Chain (CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ [])
  b0 = at 0 2 (X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (win 0 3 complete₃ ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201) ▸
       at 5 4 (X3 ∷ CS23 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

