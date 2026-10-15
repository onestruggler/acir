{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D625 where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-comm-CCZ012-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D045 using (lem-pass-CCZ123-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D054 using (lem-pass-TOFF012-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D602 using (lem-pass-CZ12-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D624 using (lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 ; lem-pass-TOFF012-vs-CZ12 ; lem-pass-TOFF012-vs-Z1 ; lem-pass-TOFF012-vs-Z2 ; lem-pass-TOFF012-vs-Z3 ; lem-pass-TOFF012-vs-iI)
-- pass [CCZ012] [CZ13]: 1 steps
lem-pass-CCZ012-vs-CZ13 : ⟪ (CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ13 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ13) ▸ done


-- pass [TOFF012] [CZ13]: 5 steps
lem-pass-TOFF012-vs-CZ13 : ⟪ (Toff012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CZ13 = run b0
  where
  b0 : Chain (Toff012 ∷ CZ13 ∷ []) (CZ13 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 2 2 (CZ13 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • CZ • Swap ↑))) ▸
       at 1 2 (CZ13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ13) ▸
       at 0 2 (CZ13 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • CZ • Swap ↑))) ▸
       at 1 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done


-- comm CCZ012 CZ23: 19 steps
lem-comm-CCZ012-CZ23 : ⟪ (CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ23 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ012 ∷ CZ23 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CZ23 ∷ CS12 ∷ []) (win 0 3 complete₃ (CS • (CZ ↑)) ((CZ ↑) • CS) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CZ23 ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • (CZ ↑)) ((CZ ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 3 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ []) (CS01 ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 2 (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 2 (CZ23 ∷ CX21 ∷ []) (win 0 3 complete₃ (CX₁₀ • (CZ ↑)) ((CZ ↑) • CX₁₀) tt tt Eq.refl) ▸
       at 1 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ23 ∷ CCZ012 ∷ [])
  b2 = at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 1 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [CZ23]: 1 steps
lem-pass-CCZ012-vs-CZ23 : ⟪ (CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ23 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ23 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ23) ▸ done


-- pass [TOFF012] [CZ23]: 5 steps
lem-pass-TOFF012-vs-CZ23 : ⟪ (Toff012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CZ23 = run b0
  where
  b0 : Chain (Toff012 ∷ CZ23 ∷ []) (CZ23 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 2 2 (CZ23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((CZ ↑))) ▸
       at 1 2 (CZ23 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ23) ▸
       at 0 2 (CZ23 ∷ K0 ∷ []) (low₁-comm (K) ((CZ ↑))) ▸
       at 1 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ Toff012 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (ι ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI) ▸
       at 1 2 (ι ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI) ▸
       at 2 2 (Z1 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z1) ▸
       at 3 2 (Z2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z2) ▸
       at 4 2 (CZ12 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ12) ▸
       at 5 2 (Z3 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Z3) ▸
       at 6 2 (CZ13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ13) ▸
       at 7 2 (CZ23 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CZ23) ▸ done

  b1 : Chain (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ Toff012 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ [])
  b1 = at 8 2 (CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CCZ123) ▸ done


-- pass [CSd03] [iI]: 9 steps
lem-pass-CSd03-vs-iI : ⟪ (CS03⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-iI = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ ι ∷ []) (ι ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (ι ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (ι ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [Z1]: 9 steps
lem-pass-CSd03-vs-Z1 : ⟪ (CS03⁻ ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z1 ∷ []) (Z1 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Z1 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Z ↑)) ((Z ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z1 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Z1 ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [Z2]: 15 steps
lem-pass-CSd03-vs-Z2 : ⟪ (CS03⁻ ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z2 ∷ []) (Sw01 ∷ Z2 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Z2 ∷ []) (sym (low-comm (Swap) (Z))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Z2 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Z ↑)) ((Z ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Z2 ∷ CS13⁻ ∷ Sw01 ∷ []) (Z2 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [CZ12]: 1 steps
lem-pass-CSd03-vs-CZ12 : ⟪ (CS03⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ12 = run b0
  where
  b0 : Chain (CS03⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (CZ12 ∷ CS03⁻ ∷ []) (sym lem-pass-CZ12-vs-CSd03) ▸ done


-- pass [CSd03] [Z3]: 9 steps
lem-pass-CSd03-vs-Z3 : ⟪ (CS03⁻ ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z3 ∷ []) (Z3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ Z2 ∷ []) (win 0 3 complete₃ ((Z ↑ ↑) • (Swap ↑)) ((Swap ↑) • (Z ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Z2 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Z ↑ ↑)) ((Z ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (Z3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Z3 ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [CZ13]: 11 steps
lem-pass-CSd03-vs-CZ13 : ⟪ (CS03⁻ ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CZ13 ∷ []) (CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CZ12 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CZ13 ∷ CS03⁻ ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [CZ23]: 15 steps
lem-pass-CSd03-vs-CZ23 : ⟪ (CS03⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CZ23 ∷ []) (Sw01 ∷ CZ23 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ CZ23 ∷ CS13⁻ ∷ Sw01 ∷ []) (CZ23 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [CCZ123]: 1 steps
lem-pass-CSd03-vs-CCZ123 : ⟪ (CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CCZ123 = run b0
  where
  b0 : Chain (CS03⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (CCZ123 ∷ CS03⁻ ∷ []) (sym lem-pass-CCZ123-vs-CSd03) ▸ done


-- pass [CSd03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CS03⁻ ∷ CCZ123 ∷ [])
  b0 = at 0 2 (ι ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-iI) ▸
       at 1 2 (ι ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-iI) ▸
       at 2 2 (Z1 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z1) ▸
       at 3 2 (Z2 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z2) ▸
       at 4 2 (CZ12 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ12) ▸
       at 5 2 (Z3 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Z3) ▸
       at 6 2 (CZ13 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ13) ▸
       at 7 2 (CZ23 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CZ23) ▸ done

  b1 : Chain (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CS03⁻ ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ [])
  b1 = at 8 2 (CCZ123 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CCZ123) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 3 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 2 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 1 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 0 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ []) (lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸ done

