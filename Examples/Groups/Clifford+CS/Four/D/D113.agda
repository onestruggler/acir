{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D113 where

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

-- xt1 0001: 0 steps
lem-xt1-0001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0001 = refl

-- xs1 0001: 1 steps
lem-xs1-0001 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0001 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done


-- xt1 1001: 1 steps
lem-xt1-1001 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1001 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xs1 1001: 1 steps
lem-xs1-1001 : ⟪ (X0 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1001 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done


-- xt1 0101: 1 steps
lem-xt1-0101 : ⟪ (X1 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt1-0101 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X3 ∷ []) (X3 ∷ [])
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 0101: 2 steps
lem-xs1-0101 : ⟪ (X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs1-0101 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X1 ∷ []) (X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 1101: 2 steps
lem-xt1-1101 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1101 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 1101: 2 steps
lem-xs1-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1101 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 0011: 0 steps
lem-xt1-0011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0011 = refl

-- xs1 0011: 2 steps
lem-xs1-0011 : ⟪ (X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0011 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ X1 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xt1 1011: 1 steps
lem-xt1-1011 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1011 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xs1 1011: 2 steps
lem-xs1-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1011 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xt1 0111: 1 steps
lem-xt1-0111 : ⟪ (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0111 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 0111: 3 steps
lem-xs1-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0111 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 1111: 2 steps
lem-xt1-1111 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1111 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 1111: 3 steps
lem-xs1-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 3 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done

