{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D132 where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-S2)
open import Examples.Groups.Clifford+CS.Four.D.D018 using (lem-S2-at2013)
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-pass-CCZ012-vs-CZ01)
open import Examples.Groups.Clifford+CS.Four.D.D029 using (lem-pass-CS12-vs-X3-TOFF013-X3 ; lem-pass-CSd12-vs-X3-TOFF013-X3)
open import Examples.Groups.Clifford+CS.Four.D.D062 using (lem-pass-CS23-vs-CS01)
open import Examples.Groups.Clifford+CS.Four.D.D125 using (lem-pass-CCZ012-vs-CS23)
open import Examples.Groups.Clifford+CS.Four.D.D126 using (lem-pass-CS23-vs-CS02 ; lem-pass-CS23-vs-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D127 using (lem-pass-CS23-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D131 using (lem-pass-CCZ023-vs-X3-TOFF013-X3)
-- pass [TOFF203] [X3 TOFF013 X3]: 129 steps
lem-pass-TOFF203-vs-X3-TOFF013-X3 : ⟪ (Toff203 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ
lem-pass-TOFF203-vs-X3-TOFF013-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (Toff203 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 0 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b1 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b2 = at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ Sw01 ∷ CCZ123 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b3 = at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (win 0 3 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b4 : Chain (K2 ∷ Sw01 ∷ CCZ123 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b4 = at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b5 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2⁻ ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ [])
  b6 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸ done

  b7 : Chain (K2 ∷ CCZ023 ∷ K2⁻ ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (K2 ∷ CCZ023 ∷ X3 ∷ Toff013 ∷ X3 ∷ K2⁻ ∷ [])
  b7 = at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 2 (X3 ∷ K2⁻ ∷ []) (low₃-comm (((K • iI) ↑ ↑)) (X)) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ K3⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ K3⁻ ∷ []) (sym (low₃-comm (Toff) ((K • iI)))) ▸
       at 5 2 (Sw23 ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ K2⁻ ∷ []) (low₃-comm (((K • iI) ↑ ↑)) (X)) ▸ done

  b8 : Chain (K2 ∷ CCZ023 ∷ X3 ∷ Toff013 ∷ X3 ∷ K2⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ [])
  b8 = at 1 4 (X3 ∷ Toff013 ∷ X3 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-X3-TOFF013-X3) ▸
       at 0 2 (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X)) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ K3 ∷ []) (win 0 3 complete₃ ((K ↑) • (Swap ↑)) ((Swap ↑) • (K ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ K3 ∷ []) (sym (low₃-comm (Toff) (K))) ▸
       at 3 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X)) ▸ done

  b9 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ K2⁻ ∷ Sw01 ∷ [])
  b9 = at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ K2⁻ ∷ []) (sym (low-comm (Swap) ((K • iI)))) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b10 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2⁻ ∷ Sw01 ∷ [])
  b10 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b11 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2⁻ ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2⁻ ∷ Sw01 ∷ [])
  b11 = at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b12 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2⁻ ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b12 = at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 3 (Toff213 ∷ []) (win 0 3 complete₃ ((K ↑) • CCZ • ((K • iI) ↑)) ((K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b13 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b13 = at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (X3 ∷ Toff013 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b14 = at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b15 : Chain (X3 ∷ Toff013 ∷ X3 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ Sw01 ∷ Sw01 ∷ [])
  b15 = at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ [])
  b16 = at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [TOFF203 CS12 TOFF203 CSd12] [X3 TOFF013 X3]: 4 steps
lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 : ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 = run b0
  where
  b0 : Chain (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ [])
  b0 = at 3 4 (X3 ∷ Toff013 ∷ X3 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-X3-TOFF013-X3) ▸
       at 2 4 (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ []) (lem-pass-TOFF203-vs-X3-TOFF013-X3) ▸
       at 1 4 (X3 ∷ Toff013 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS12-vs-X3-TOFF013-X3) ▸
       at 0 4 (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ []) (lem-pass-TOFF203-vs-X3-TOFF013-X3) ▸ done


-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3]: 3 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 4 (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (lem-S2-at2013) ▸
       at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3) ▸
       at 3 4 (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-S2-at2013) ▸ done


-- pass [CS02] [CZ01]: 1 steps
lem-pass-CS02-vs-CZ01 : ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CZ01 = run b0
  where
  b0 : Chain (CS02 ∷ CZ01 ∷ []) (CZ01 ∷ CS02 ∷ [])
  b0 = at 0 2 (CZ01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CS02] [CSd23]: 7 steps
lem-pass-CS02-vs-CSd23 : ⟪ (CS02 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CSd23 = run b0
  where
  b0 : Chain (CS02 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) tt tt Eq.refl) ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CS02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CZ01 ∷ CCZ012 ∷ CCZ012 ∷ CS23⁻ ∷ [])
  b0 = at 0 2 (Toff201 ∷ CS01 ∷ CS02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toffᵗ) (Toffᵗ • CS • (Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS23) ▸
       at 2 2 (CS23 ∷ CS02 ∷ []) (sym lem-pass-CS23-vs-CS02) ▸
       at 1 2 (CS23 ∷ CS01 ∷ []) (sym lem-pass-CS23-vs-CS01) ▸
       at 4 2 (Toff201 ∷ CZ01 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toffᵗ) (Toffᵗ • CZ • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ CS01 ∷ CS02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toffᵗ) (Toffᵗ • CS • (Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • Toffᵗ) (Toffᵗ • CS) tt tt Eq.refl) ▸
       at 6 2 (CZ01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ01) ▸ done

  b1 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CZ01 ∷ CCZ012 ∷ CCZ012 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ [])
  b1 = at 5 2 (CZ01 ∷ CS02 ∷ []) (lem-pass-CS02-vs-CZ01) ▸
       at 3 3 [] (win 3 0 complete₃ (CS • CS • CZ) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ CS02 ∷ []) (lem-pass-CS02-vs-CSd23) ▸ done


-- pass [TOFF201 CS23 TOFF201 CSd23] [CS02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 5 (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23) ▸ done


-- pass [CSd02] [CZ01]: 1 steps
lem-pass-CSd02-vs-CZ01 : ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CZ01 = run b0
  where
  b0 : Chain (CS02⁻ ∷ CZ01 ∷ []) (CZ01 ∷ CS02⁻ ∷ [])
  b0 = at 0 2 (CZ01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd02] [CSd23]: 7 steps
lem-pass-CSd02-vs-CSd23 : ⟪ (CS02⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CSd23 = run b0
  where
  b0 : Chain (CS02⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02⁻ ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS01⁻ ∷ CS01⁻ ∷ CS02⁻ ∷ CZ01 ∷ CCZ012 ∷ CCZ012 ∷ CS23⁻ ∷ [])
  b0 = at 0 2 (Toff201 ∷ CS01⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Toffᵗ) (Toffᵗ • (CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS23) ▸
       at 2 2 (CS23 ∷ CS02⁻ ∷ []) (sym lem-pass-CS23-vs-CSd02) ▸
       at 1 2 (CS23 ∷ CS01⁻ ∷ []) (sym lem-pass-CS23-vs-CSd01) ▸
       at 4 2 (Toff201 ∷ CZ01 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toffᵗ) (Toffᵗ • CZ • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ CS01⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Toffᵗ) (Toffᵗ • (CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • Toffᵗ) (Toffᵗ • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 6 2 (CZ01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ01) ▸ done

  b1 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS01⁻ ∷ CS01⁻ ∷ CS02⁻ ∷ CZ01 ∷ CCZ012 ∷ CCZ012 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ [])
  b1 = at 5 2 (CZ01 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CZ01) ▸
       at 3 3 [] (win 3 0 complete₃ ((CS • CS • CS) • (CS • CS • CS) • CZ) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CSd23) ▸ done


-- pass [TOFF201 CS23 TOFF201 CSd23] [CSd02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 5 (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23) ▸ done


-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 3 5 (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02) ▸
       at 4 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 7 5 (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02) ▸ done


-- pass [X3 TOFF201 CS23 TOFF201 CSd23 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b1 = at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b2 = at 12 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b3 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b4 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b5 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b6 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b6 = at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b7 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b7 = at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CS02 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b8 = at 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b9 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ [])
  b9 = at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 17 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ [])
  b10 = at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b11 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b11 = at 11 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 11 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b12 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b12 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b13 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b13 = at 17 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b14 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b14 = at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 18 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 11 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b15 = at 11 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CS02⁻ ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))) ▸
       at 1 12 (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (X3 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b16 = at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b17 : Chain (X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b17 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b18 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b19 : Chain (X3 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b19 = at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b20 = at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b21 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b21 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b22 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b22 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Toff013 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b23 = at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b24 : Chain (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b24 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b25 = at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b26 : Chain (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b26 = at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Toff013 ∷ CS02 ∷ X3 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b27 = at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b28 : Chain (Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b28 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b29 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b29 = at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b30 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b31 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  b31 = at 3 2 (CS02⁻ ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))) ▸ done


-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = run b0
  where
  b0 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 0 10 (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (sym lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 0 10 (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3) ▸
       at 6 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 13 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  b0 = at 0 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 0 (CS23 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (ε) ((CS ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 2 0 (Toff201 ∷ Toff201 ∷ []) (win 3 0 complete₃ (ε) (Toffᵗ • Toffᵗ) tt tt Eq.refl) ▸
       at 3 0 (CS23⁻ ∷ CS23 ∷ []) (win 0 3 complete₃ (ε) (((CS • CS • CS) ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 0 (Toff201 ∷ Toff201 ∷ []) (win 3 0 complete₃ (ε) (Toffᵗ • Toffᵗ) tt tt Eq.refl) ▸
       at 5 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 10 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) (sym lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3) ▸
       at 15 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b1 = at 14 2 [] (win 0 3 complete₃ (((CS • CS • CS) ↑) • (CS ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Toffᵗ • Toffᵗ) (ε) tt tt Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((CS ↑) • ((CS • CS • CS) ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Toffᵗ • Toffᵗ) (ε) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

