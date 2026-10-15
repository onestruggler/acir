{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D109 where

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

-- xc03: 1 steps
lem-xc03 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ
lem-xc03 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ [])
  b0 = at 0 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸ done


-- xx1: 1 steps
lem-xx1 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx1 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xc10: 1 steps
lem-xc10 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xc10 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xc12: 1 steps
lem-xc12 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ
lem-xc12 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ [])
  b0 = at 0 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸ done


-- xc13: 1 steps
lem-xc13 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ
lem-xc13 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ [])
  b0 = at 0 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸ done


-- xx2: 1 steps
lem-xx2 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx2 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xc20: 1 steps
lem-xc20 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xc20 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done


-- xc21: 1 steps
lem-xc21 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xc21 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xc23: 1 steps
lem-xc23 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ
lem-xc23 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ [])
  b0 = at 0 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸ done


-- xx3: 1 steps
lem-xx3 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx3 = run b0
  where
  b0 : Chain (X3 ∷ X3 ∷ []) []
  b0 = at 0 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xc30: 1 steps
lem-xc30 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xc30 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done


-- xc31: 1 steps
lem-xc31 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xc31 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done


-- xc32: 1 steps
lem-xc32 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xc32 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- swsw0: 1 steps
lem-swsw0 : ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw0 = run b0
  where
  b0 : Chain (Sw01 ∷ Sw01 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- swsw1: 1 steps
lem-swsw1 : ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw1 = run b0
  where
  b0 : Chain (Sw12 ∷ Sw12 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- swsw2: 1 steps
lem-swsw2 : ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw2 = run b0
  where
  b0 : Chain (Sw23 ∷ Sw23 ∷ []) []
  b0 = at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

