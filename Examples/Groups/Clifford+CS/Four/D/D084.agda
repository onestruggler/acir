{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D084 where

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
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-pass-CCZ012-vs-CCZ013 ; lem-pass-CCZ012-vs-CZ01)
open import Examples.Groups.Clifford+CS.Four.D.D025 using (lem-pass-CS13-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D029 using (lem-pass-CSd02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CCZ012-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D054 using (lem-pass-CCZ012-vs-CCZ123)
-- pass [CCZ123] [CCZ012]: 1 steps
lem-pass-CCZ123-vs-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CCZ012 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CCZ012 ∷ CCZ123 ∷ []) (sym lem-pass-CCZ012-vs-CCZ123) ▸ done


-- pass [TOFF123] [TOFF102]: 7 steps
lem-pass-TOFF123-vs-TOFF102 : ⟪ (Toff123 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-TOFF102 = run b0
  where
  b0 : Chain (Toff123 ∷ Toff102 ∷ []) (Toff102 ∷ Toff123 ∷ [])
  b0 = at 1 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 0 1 (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (win 0 3 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (((K • iI) ↑) • (K ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ012) ▸
       at 2 0 (K1⁻ ∷ K1 ∷ []) (win 3 0 complete₃ (ε) (((K • iI) ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 0 3 (Toff102 ∷ []) (win 3 0 complete₃ ((K ↑) • CCZ • ((K • iI) ↑)) ((K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 1 3 (Toff123 ∷ []) (win 0 3 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF102] [X3 TOFF103 X3]: 118 steps
lem-pass-TOFF102-vs-X3-TOFF103-X3 : ⟪ (Toff102 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-X3-TOFF103-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Toff102 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (Toff102 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Toff102 ∷ K1 ∷ Sw23 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((K ↑) • CZ • CCZ • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b4 : Chain (Toff102 ∷ K1 ∷ Sw23 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ Sw23 ∷ []) (Toff102 ∷ K1 ∷ CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1⁻ ∷ Sw23 ∷ [])
  b4 = at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (Toff102 ∷ K1 ∷ CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1⁻ ∷ Sw23 ∷ []) (Toff102 ∷ K1 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ [])
  b5 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (Toff102 ∷ K1 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) (Toff102 ∷ K1 ∷ CZ01 ∷ CCZ013 ∷ K1⁻ ∷ [])
  b6 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((K • iI) ↑)) (Swap))) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff102 ∷ K1 ∷ CZ01 ∷ CCZ013 ∷ K1⁻ ∷ []) (K1 ∷ CZ01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b7 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (((K • iI) ↑) • (K ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ01) ▸
       at 2 2 (CCZ013 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CCZ013) ▸
       at 3 0 (K1⁻ ∷ K1 ∷ []) (win 3 0 complete₃ (ε) (((K • iI) ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap)) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (K1 ∷ CZ01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b8 = at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (K1 ∷ CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CZ01 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b9 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b10 : Chain (K1 ∷ CZ01 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1⁻ ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (X3 ∷ Sw23 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b10 = at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap)) ▸
       at 0 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ ((K ↑) • CZ • CCZ • ((K • iI) ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b11 : Chain (X3 ∷ Sw23 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b11 = at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b12 : Chain (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b12 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b13 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b13 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b14 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ [])
  b14 = at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 3 (Toff102 ∷ []) (win 3 0 complete₃ ((K ↑) • CCZ • ((K • iI) ↑)) ((K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸ done


-- pass [CS13] [X3 TOFF103 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF103-X3 : ⟪ (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF103-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ [])
  b8 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd13] [X3 TOFF103 X3]: 65 steps
lem-pass-CSd13-vs-X3-TOFF103-X3 : ⟪ (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-X3-TOFF103-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF103 X3]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 3 4 (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-X3-TOFF103-X3) ▸
       at 2 4 (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-X3-TOFF103-X3) ▸
       at 1 4 (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS13-vs-X3-TOFF103-X3) ▸
       at 0 4 (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-X3-TOFF103-X3) ▸ done


-- pass [CS12] [CS13]: 1 steps
lem-pass-CS12-vs-CS13 : ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CS13 = run b0
  where
  b0 : Chain (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ [])
  b0 = at 0 2 (CS13 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [CZ02]: 1 steps
lem-pass-CCZ012-vs-CZ02 : ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CS12] [CZ02]: 1 steps
lem-pass-CS12-vs-CZ02 : ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CZ02 = run b0
  where
  b0 : Chain (CS12 ∷ CZ02 ∷ []) (CZ02 ∷ CS12 ∷ [])
  b0 = at 0 2 (CZ02 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [CS12] [CSd13]: 1 steps
lem-pass-CS12-vs-CSd13 : ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CSd13 = run b0
  where
  b0 : Chain (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) tt tt Eq.refl) ▸ done


-- pass [CS12] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS02 ∷ CS02 ∷ CS12 ∷ CZ02 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((CS ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13) ▸
       at 2 2 (CS13 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS13) ▸
       at 1 2 (CS13 ∷ CS02 ∷ []) (sym lem-pass-CS13-vs-CS02) ▸
       at 4 2 (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((CS ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS02 ∷ CS02 ∷ CS12 ∷ CZ02 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ [])
  b1 = at 5 2 (CZ02 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CZ02) ▸
       at 3 3 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd13) ▸ done


-- pass [TOFF102 CS13 TOFF102 CSd13] [CS12]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 5 (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13) ▸ done


-- pass [CSd12] [CS13]: 1 steps
lem-pass-CSd12-vs-CS13 : ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CS13 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CS13 ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸ done


-- pass [CSd12] [CZ02]: 1 steps
lem-pass-CSd12-vs-CZ02 : ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CZ02 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CZ02 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd12] [CSd13]: 1 steps
lem-pass-CSd12-vs-CSd13 : ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CSd13 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CS12⁻ ∷ []) (win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸ done


-- pass [CSd12] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS02⁻ ∷ CS02⁻ ∷ CS12⁻ ∷ CZ02 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13) ▸
       at 2 2 (CS13 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CS13) ▸
       at 1 2 (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13) ▸
       at 4 2 (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS02⁻ ∷ CS02⁻ ∷ CS12⁻ ∷ CZ02 ∷ CCZ012 ∷ CCZ012 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (CZ02 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CZ02) ▸
       at 3 3 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CSd13) ▸ done

