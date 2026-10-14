{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D038 where

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
open import Examples.Groups.Clifford+CS.Four.D.D015 using (lem-C3d-A)
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-pass-CCZ012-vs-CS03 ; lem-pass-CS12-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D023 using (lem-pass-CCZ012-vs-CS12 ; lem-pass-CCZ012-vs-CSd12 ; lem-pass-CCZ012-vs-CZ12 ; lem-pass-CS02-vs-CS03 ; lem-pass-CS02-vs-CSd03 ; lem-pass-CSd12-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D024 using (lem-pass-S0-vs-CS03 ; lem-pass-S0-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D025 using (lem-pass-Sd0-vs-CS03 ; lem-pass-Sd0-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CCZ012-vs-CSd03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
open import Examples.Groups.Clifford+CS.Four.D.D037 using (lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02)
-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = run b0
  where
  b0 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 0 14 (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (sym lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 0 14 (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3) ▸
       at 10 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2) ▸ done


-- pass [X1 TOFF012 CS03 TOFF012 CSd03 X1] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-TOFF012-CS03-TOFF012-CSd03-X1-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ [])
  b0 = at 5 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 14 0 (X1 ∷ X1 ∷ []) (win 3 0 complete₃ (ε) ((X ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 14 (X0 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3) ▸
       at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸ done


-- pass [CSd03] [TOFF012 CS03 TOFF012]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-C3d-A) ▸ done


-- pass [S0] [TOFF012 CS03 TOFF012]: 11 steps
lem-pass-S0-vs-TOFF012-CS03-TOFF012 : ⟪ (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF012-CS03-TOFF012 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ CS12 ∷ CS12 ∷ CCZ012 ∷ CZ12 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (S • Toff) (Toff • S • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03) ▸
       at 2 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 1 2 (CS03 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (S • Toff) (Toff • S • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS12) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ CS12 ∷ CS12 ∷ CCZ012 ∷ CZ12 ∷ CCZ012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ [])
  b1 = at 6 2 (CZ12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ12) ▸
       at 4 3 [] (win 3 0 complete₃ ((CS ↑) • (CS ↑) • (CZ ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸ done


-- pass [CS12] [TOFF012 CS03 TOFF012]: 3 steps
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 = run b0
  where
  b0 : Chain (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [CZ12] [CS03]: 9 steps
lem-pass-CZ12-vs-CS03 : ⟪ (CZ12 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01 ∷ CZ23 ∷ []) (sym (low-comm (CS) (CZ))) ▸
       at 3 2 (Sw12 ∷ CZ13 ∷ []) (win 0 3 complete₃ ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CZ12 ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- pass [CCZ012] [TOFF012 CS03 TOFF012]: 6 steps
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03) ▸
       at 1 2 (CS03 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS03) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ ((CZ ↑) • (CZ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [Sd0]: 1 steps
lem-pass-CCZ012-vs-Sd0 : ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-Sd0 = run b0
  where
  b0 : Chain (CCZ012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (S • S • S)) ((S • S • S) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CS12] [Sd0]: 1 steps
lem-pass-CS12-vs-Sd0 : ⟪ (CS12 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Sd0 = run b0
  where
  b0 : Chain (CS12 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) tt tt Eq.refl) ▸ done


-- merge3: 52 steps
lem-merge3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-merge3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 4 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS12 ∷ CCZ012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ S0⁻ ∷ [])
  b2 = at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS02 ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 4 3 (S0 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (Toff • S • Toff) (S • (CS ↑) • CCZ) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS12 ∷ CCZ012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ S0⁻ ∷ []) (CS03⁻ ∷ S0 ∷ CS12 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ S0⁻ ∷ [])
  b3 = at 0 4 (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (sym lem-pass-CSd03-vs-TOFF012-CS03-TOFF012) ▸
       at 1 4 (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (sym lem-pass-S0-vs-TOFF012-CS03-TOFF012) ▸
       at 2 4 (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (sym lem-pass-CS12-vs-TOFF012-CS03-TOFF012) ▸
       at 3 4 (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (sym lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012) ▸
       at 6 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03⁻ ∷ S0 ∷ CS12 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ S0⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS12 ∷ CS03 ∷ S0⁻ ∷ CCZ012 ∷ [])
  b4 = at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 0 2 (S0 ∷ CS03⁻ ∷ []) (sym lem-pass-S0-vs-CSd03) ▸
       at 3 2 (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03) ▸
       at 4 2 (S0⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-Sd0) ▸ done

  b5 : Chain (S0 ∷ CS03⁻ ∷ CS12 ∷ CS03 ∷ S0⁻ ∷ CCZ012 ∷ []) (CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CS12 ∷ CCZ012 ∷ [])
  b5 = at 2 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 3 2 (S0⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-Sd0) ▸
       at 2 2 (S0⁻ ∷ CS03 ∷ []) (sym lem-pass-Sd0-vs-CS03) ▸
       at 1 2 (S0⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-Sd0-vs-CSd03) ▸
       at 0 2 [] (win 3 0 complete₃ (S • (S • S • S)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CS12 ∷ CCZ012 ∷ []) (CS12 ∷ CCZ012 ∷ [])
  b6 = at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- merge3 @1023: 78 steps
lem-merge3-at1023 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-merge3-at1023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b0 = at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b1 = at 14 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b2 = at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b3 = at 12 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ CS13 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (Toff102 ∷ CS13 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff102 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 2 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Toff102 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ []) (CS02 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ [])
  b8 = at 0 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 10 (CS12 ∷ CCZ012 ∷ []) (lem-merge3) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ []) (CS02 ∷ CCZ012 ∷ [])
  b9 = at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- PP1-split: 7 steps
lem-PP1-split : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ
lem-PP1-split = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (CS02 ∷ CCZ012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  b0 = at 4 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 6 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 8 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 10 (CS02 ∷ CCZ012 ∷ []) (lem-merge3-at1023) ▸ done


-- PP0-sep-inv: 13 steps
lem-PP0-sep-inv : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-PP0-sep-inv = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  b0 = at 0 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 3 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 5 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 10 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (sym lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3) ▸
       at 15 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b1 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS02 CCZ012] [TOFF012 CS03 TOFF012 CSd03]: 13 steps
lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS02 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CS12⁻ ∷ CS03⁻ ∷ [])
  b0 = at 1 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CZ12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ12) ▸
       at 2 2 (CS12⁻ ∷ []) (win 3 0 complete₃ ((CS ↑) • (CZ ↑)) (((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 2 2 (CS03 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CS03) ▸
       at 1 2 (CS03 ∷ CS02 ∷ []) (lem-pass-CS02-vs-CS03) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CS12⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ CCZ012 ∷ [])
  b1 = at 2 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd12) ▸
       at 4 2 [] (win 3 0 complete₃ ((CS ↑) • ((CS • CS • CS) ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd03) ▸
       at 3 2 (CS03⁻ ∷ CS02 ∷ []) (lem-pass-CS02-vs-CSd03) ▸ done


-- adj01: 4 steps
lem-adj01 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-adj01 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 4 4 (CS02 ∷ CCZ012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (lem-PP1-split) ▸
       at 0 6 (CS02 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 10 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP0-sep-inv) ▸
       at 0 8 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-PP1-split) ▸ done

